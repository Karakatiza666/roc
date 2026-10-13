//! The measure of normal-form 3.0: every simplify round must lower it.
//!
//! The components, in lexicographic order. `applies` counts `Apply` nodes,
//! which N8i turns into calls, one per arm where a switch chose the
//! function; it comes before `switches`, because that switch is new.
//! `negated_connectives` counts `Bool.not` nodes over an `And`, an `Or` or a
//! `Bool` switch, which N13t pushes to the leaves. `forwarding_calls` counts
//! the calls of a row that only calls another row over its parameters, which
//! N8c's call half makes that call; it comes before `nodes`, because that
//! call can read a parameter twice.
//! `flipped_comparisons` counts `is_gt` and `is_gte` nodes, which N1l
//! removes. `is_lte_scrutinees` counts the integer `is_lte` leaves of switch
//! scrutinees (`polarity.zig`), which N13q and N13s flip, and
//! `flipping_scrutinees` the `Bool` switches that N13s flips.
//! `unordered_leaves` counts the calls `prims.ordersLiteralLast` names whose
//! first operand is a literal and whose second is not, which N15c swaps.
//! `arms_and_operands` counts arm and operand regions, one of which N7d's
//! factoring removes; it comes after `joins`, which T3 lowers by adding one.
//! Every component but the last
//! counts the term the row unfolds to, so a node read twice counts twice; the
//! last counts the row's graph, which N5 merges and N6 removal lower without
//! changing the unfolding.

const std = @import("std");
const ir = @import("ir.zig");
const types_mod = @import("types.zig");
const prims = @import("prims.zig");
const polarity = @import("polarity.zig");

const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const RowId = ir.RowId;

/// One component of the measure.
pub const Component = enum(u8) {
    loops,
    general_loops,
    aggregate_slots,
    applies,
    switches,
    negated_connectives,
    forwarding_calls,
    nodes,
    flipped_comparisons,
    is_lte_scrutinees,
    flipping_scrutinees,
    unordered_leaves,
    terminators,
    joins,
    arms_and_operands,
    graph_nodes,
};

/// The measure's value: one count per component, saturating.
pub const Measure = struct {
    counts: [component_count]u64 = @splat(0),

    const component_count = @typeInfo(Component).@"enum".field_names.len;

    /// The count of one component.
    pub fn get(self: Measure, c: Component) u64 {
        return self.counts[@backingInt(c)];
    }

    fn add(self: *Measure, c: Component, n: u64) void {
        const slot = &self.counts[@backingInt(c)];
        slot.* +|= n;
    }

    /// Lexicographic comparison.
    pub fn order(a: Measure, b: Measure) std.math.Order {
        for (a.counts, b.counts) |x, y| {
            if (x != y) return std.math.order(x, y);
        }
        return .eq;
    }
};

/// The measure of `row`, over the nodes `live` marks (`live.zig`): a node
/// the row no longer reaches, such as the old body a rebuild copied, counts
/// nowhere.
pub fn ofRow(gpa: std.mem.Allocator, store: *const ir.Store, types: *const types_mod.Types, live: []const bool, row: RowId) std.mem.Allocator.Error!Measure {
    var m: Measure = .{};
    const node_mult = try gpa.alloc(u64, store.nodeCount());
    defer gpa.free(node_mult);
    @memset(node_mult, 0);
    const region_mult = try gpa.alloc(u64, store.regionCount());
    defer gpa.free(region_mult);
    @memset(region_mult, 0);

    const r = store.row(row);
    for (store.tySlice(r.params)) |t| if (types.isAggregate(t)) m.add(.aggregate_slots, 1);
    region_mult[r.body.index()] = 1;
    addEnd(store, &m, r.body, 1, node_mult);

    // Every user of a node has a larger id or ends a region its owner, with a
    // larger id, owns; so decreasing ids visit users first.
    const regions = store.nodes.items(.region);
    var i = store.nodeCount();
    while (i > 0) {
        i -= 1;
        if (!live[i] or store.region(regions[i]).row != row) continue;
        m.add(.graph_nodes, 1);
        const mult = node_mult[i];
        if (mult == 0) continue;
        const nd = store.node(NodeId.of(@intCast(i)));
        m.add(.nodes, mult);
        if (nd.op.isLoop()) m.add(.loops, mult);
        if (nd.op == .loop) m.add(.general_loops, mult);
        if (nd.op == .apply) m.add(.applies, mult);
        if (nd.op == .call and store.forwardingCall(RowId.of(nd.payload)) != null) m.add(.forwarding_calls, mult);
        if (nd.op == .prim) {
            if (prims.lookup(ir.PrimId.of(nd.payload))) |p| {
                const args = store.refSlice(nd.args);
                if (args.len == 2 and prims.ordersLiteralLast(p.owner, p.method) and isLit(store, args[0]) and !isLit(store, args[1])) m.add(.unordered_leaves, mult);
                switch (p.method) {
                    .is_gt, .is_gte => m.add(.flipped_comparisons, mult),
                    .not => if (isConnective(store, store.refSlice(nd.args)[0])) m.add(.negated_connectives, mult),
                    .is_eq, .is_lt, .is_lte, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get => {},
                }
            }
        }
        if (nd.op == .switch_) {
            m.add(.switches, mult);
            const scrutinee = store.refSlice(nd.args)[0];
            m.add(.is_lte_scrutinees, mult *| polarity.leavesOf(store, types, scrutinee).lte);
            const shape = polarity.isBoolSwitch(types, store.refTy(row, scrutinee), nd.payload, store.regionSlice(nd.regions).len, nd.tys.len, nd.aux.len);
            if (shape and polarity.flips(store, types, scrutinee)) m.add(.flipping_scrutinees, mult);
        }
        for (store.refSlice(nd.args)) |a| addRef(&m, a, mult, node_mult);
        for (store.regionSlice(nd.regions)) |sub| {
            region_mult[sub.index()] +|= mult;
            const reg = store.region(sub);
            if (reg.kind == .join) m.add(.joins, mult);
            if (reg.kind == .arm or reg.kind == .operand) m.add(.arms_and_operands, mult);
            if (reg.kind == .loop_body) {
                for (store.tySlice(reg.params)) |t| if (types.isAggregate(t)) m.add(.aggregate_slots, mult);
            }
            addEnd(store, &m, sub, mult, node_mult);
        }
    }
    return m;
}

// A parameter is a leaf of the unfolded term, and counts as one node, so a
// rule that reads a value fewer times lowers the count even when the value
// is a parameter.
fn addRef(m: *Measure, ref: ir.Ref, mult: u64, node_mult: []u64) void {
    switch (ref.kind) {
        .node => node_mult[ref.target] +|= mult,
        .row_param, .region_param => m.add(.nodes, mult),
    }
}

fn addEnd(store: *const ir.Store, m: *Measure, r: RegionId, mult: u64, node_mult: []u64) void {
    const end = store.region(r).end;
    switch (end.kind) {
        .return_, .continue_, .break_ => m.add(.terminators, mult),
        .open, .value, .jump => {},
        // The exiting switch a region ends in is read by the region's end.
        .branch => node_mult[end.target] +|= mult,
    }
    for (store.refSlice(end.refs)) |ref| addRef(m, ref, mult, node_mult);
}

fn isLit(store: *const ir.Store, ref: ir.Ref) bool {
    return ref.kind == .node and store.node(ref.nodeId()).op == .lit;
}

fn isConnective(store: *const ir.Store, ref: ir.Ref) bool {
    if (ref.kind != .node) return false;
    const op = store.node(ref.nodeId()).op;
    return op == .and_ or op == .or_ or op == .switch_;
}

const testing = std.testing;
const builder_mod = @import("builder.zig");

test "a node read twice counts twice in the unfolding, a parameter counts at each read, and a node once in the graph" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    const row = try b.beginRow(&.{i64_ty}, i64_ty);
    const x = try b.call(.i64, .plus_wrap, &.{ ir.Ref.rowParam(0), ir.Ref.rowParam(0) });
    const y = try b.call(.i64, .times_wrap, &.{ x, x });
    try b.endRow(.{ .value = &.{y} });

    var live = try @import("live.zig").ofStore(testing.allocator, &store);
    defer live.deinit(testing.allocator);
    const m = try ofRow(testing.allocator, &store, &types, live.nodes, row);
    // times(plus(p, p), plus(p, p)): three operations and four reads of p.
    try testing.expectEqual(@as(u64, 7), m.get(.nodes));
    try testing.expectEqual(@as(u64, 2), m.get(.graph_nodes));
}
