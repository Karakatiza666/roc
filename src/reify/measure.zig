//! The measure of normal-form 3.0: every simplify round must lower it.
//!
//! The components, in lexicographic order. `law_redexes` counts, at a site
//! that opts into layer L, the `List.fold`s of a known function, which N16c
//! makes loops, so it comes before `loops`, and the literal switches on
//! `List.len` that N16f makes `Bool` switches; elsewhere it is 0. The raising
//! laws N16a and N16b each remove a loop, and N16d, N16e and N16f over a
//! comparison lower `nodes`. `self_tail_calls` counts the calls
//! a row makes to itself when N12 applies to it, and the rule removes them
//! all, at the price of one loop; it comes before `loops`. `loop_slots`
//! counts the slots and outputs of loops, which N11g to N11j remove, and
//! `loop_returns` the `Return` terminators on the paths of loops, which N11j
//! makes `Break`s. `aggregate_slots` counts the layers of records and tuples
//! that N14 splits in the parameters of the row and in the slots of loops
//! (`Types.splitLayers`), and `split_calls` the layers that N14a splits in
//! the parameters of the rows the calls name. A split lowers the first
//! while it raises `loop_slots`, and the second while it raises `nodes`. `unhoisted_tests` counts the
//! arms that end in a switch on a position before their switch's own, in a
//! switch none of whose arms holds a loop, an `Apply`, a `Lambda` or a
//! `Closure`. N7b's interchange removes them by copying arms, which raises
//! `switches` and the counts after it, so it comes before those and after
//! the counts of what it never copies. Removing a loop can expose such a
//! test, and it lowers `loops`, which comes first. `applies` counts `Apply` nodes,
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
//! first operand is a literal and whose second is not, and, in the root row,
//! those whose two operands are parameters out of parameter order: N15c swaps
//! both. N13u's decided comparisons lower `nodes`, and its `plus` chains
//! lower `nodes` too, one node per operand they splice.
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
const match = @import("match.zig");
const live_mod = @import("live.zig");
const loops = @import("loops.zig");
const scalar = @import("scalar.zig");
const laws_mod = @import("laws.zig");

const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const RowId = ir.RowId;

/// One component of the measure.
pub const Component = enum(u8) {
    self_tail_calls,
    law_redexes,
    loops,
    general_loops,
    aggregate_slots,
    split_calls,
    loop_slots,
    loop_returns,
    applies,
    unhoisted_tests,
    switches,
    negated_connectives,
    forwarding_calls,
    list_gets,
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
/// `laws` says whether the site opts into layer L.
pub fn ofRow(gpa: std.mem.Allocator, store: *const ir.Store, types: *const types_mod.Types, live: live_mod.Live, calls: *scalar.Cache, row: RowId, laws: bool) std.mem.Allocator.Error!Measure {
    var m: Measure = .{};
    const node_mult = try gpa.alloc(u64, store.nodeCount());
    defer gpa.free(node_mult);
    @memset(node_mult, 0);
    const region_mult = try gpa.alloc(u64, store.regionCount());
    defer gpa.free(region_mult);
    @memset(region_mult, 0);

    const r = store.row(row);
    m.add(.self_tail_calls, try loops.selfTailCalls(gpa, store, live, row));
    for (store.tySlice(r.params)) |t| m.add(.aggregate_slots, types.splitLayers(t));
    region_mult[r.body.index()] = 1;
    addEnd(store, &m, r.body, 1, node_mult);

    const regions = store.nodes.items(.region);
    for (0..store.nodeCount()) |k| {
        if (live.nodes[k] and store.region(regions[k]).row == row) m.add(.graph_nodes, 1);
    }
    const order = try usersFirst(gpa, store, r.body);
    defer gpa.free(order);
    for (order) |n| {
        const i = n.index();
        const mult = node_mult[i];
        if (mult == 0) continue;
        const nd = store.node(NodeId.of(@intCast(i)));
        m.add(.nodes, mult);
        if (nd.op.isLoop()) m.add(.loops, mult);
        if (nd.op == .loop) m.add(.general_loops, mult);
        if (nd.op == .apply) m.add(.applies, mult);
        if (laws and laws_mod.isLawRedex(store, nd)) m.add(.law_redexes, mult);
        if (nd.op == .call and store.forwardingCall(RowId.of(nd.payload)) != null) m.add(.forwarding_calls, mult);
        if (nd.op == .call) m.add(.split_calls, mult *| try calls.layersOf(RowId.of(nd.payload)));
        if (nd.op == .prim) {
            if (prims.lookup(ir.PrimId.of(nd.payload))) |p| {
                const args = store.refSlice(nd.args);
                if (args.len == 2 and prims.ordersLiteralLast(p.owner, p.method) and isLit(store, args[0]) and !isLit(store, args[1])) m.add(.unordered_leaves, mult);
                if (args.len == 2 and prims.ordersLiteralLast(p.owner, p.method) and r.fixed_params and args[0].kind == .row_param and args[1].kind == .row_param and args[0].output > args[1].output) m.add(.unordered_leaves, mult);
                if (p.owner == .list and p.method == .get) m.add(.list_gets, mult);
                switch (p.method) {
                    .is_gt, .is_gte => m.add(.flipped_comparisons, mult),
                    .not => if (isConnective(store, store.refSlice(nd.args)[0])) m.add(.negated_connectives, mult),
                    .is_eq, .is_lt, .is_lte, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect => {},
                }
            }
        }
        if (nd.op == .switch_) {
            m.add(.unhoisted_tests, mult *| try match.inversions(gpa, store, types, live.nodes, NodeId.of(@intCast(i))));
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
                for (store.tySlice(reg.params)) |t| m.add(.aggregate_slots, mult *| types.splitLayers(t));
                const lead: usize = switch (nd.op) {
                    .for_range => 1,
                    .for_list => 2,
                    .loop => 0,
                    .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .lambda, .apply => unreachable, // only a loop owns a loop body
                };
                m.add(.loop_slots, mult *| (store.tySlice(reg.params).len - lead + nd.tys.len));
                m.add(.loop_returns, mult *| try returnsOnPaths(gpa, store, sub));
            }
            addEnd(store, &m, sub, mult, node_mult);
        }
    }
    return m;
}

// The `Return` terminators on the paths of a loop body: its own region and
// the arms and joins of the exiting switches its paths end in.
fn returnsOnPaths(gpa: std.mem.Allocator, store: *const ir.Store, body: RegionId) std.mem.Allocator.Error!u64 {
    var count: u64 = 0;
    var regions: std.ArrayList(RegionId) = .empty;
    defer regions.deinit(gpa);
    try regions.append(gpa, body);
    var at: usize = 0;
    while (at < regions.items.len) : (at += 1) {
        const end = store.region(regions.items[at]).end;
        switch (end.kind) {
            .return_ => count += 1,
            .branch => try regions.appendSlice(gpa, store.regionSlice(store.node(NodeId.of(end.target)).regions)),
            .open, .value, .jump, .continue_, .break_ => {},
        }
    }
    return count;
}

// The nodes the region `body` reads, each before every node it reads: a
// node is read by the nodes that take it as an argument and by the owner of
// a region whose end reads it. Node ids are no such order, because the exit
// rules build a node in an arm of a switch built before it (T2), so this is
// the reverse of a depth-first post-order over the reads.
fn usersFirst(gpa: std.mem.Allocator, store: *const ir.Store, body: RegionId) std.mem.Allocator.Error![]NodeId {
    var post: std.ArrayList(NodeId) = .empty;
    errdefer post.deinit(gpa);
    const seen = try gpa.alloc(bool, store.nodeCount());
    defer gpa.free(seen);
    @memset(seen, false);
    // The reads of every node on the stack, each frame's after its parent's:
    // a frame reads `reads[start..end]`.
    var reads: std.ArrayList(NodeId) = .empty;
    defer reads.deinit(gpa);
    const Frame = struct { n: ?NodeId, start: usize, end: usize, next: usize };
    var stack: std.ArrayList(Frame) = .empty;
    defer stack.deinit(gpa);
    try endReads(gpa, store, body, &reads);
    try stack.append(gpa, .{ .n = null, .start = 0, .end = reads.items.len, .next = 0 });
    while (stack.items.len > 0) {
        const top = &stack.items[stack.items.len - 1];
        if (top.start + top.next < top.end) {
            const d = reads.items[top.start + top.next];
            top.next += 1;
            if (seen[d.index()]) continue;
            seen[d.index()] = true;
            const start = reads.items.len;
            const nd = store.node(d);
            for (store.refSlice(nd.args)) |a| if (a.kind == .node) try reads.append(gpa, a.nodeId());
            for (store.regionSlice(nd.regions)) |sub| try endReads(gpa, store, sub, &reads);
            try stack.append(gpa, .{ .n = d, .start = start, .end = reads.items.len, .next = 0 });
            continue;
        }
        if (top.n) |n| try post.append(gpa, n);
        reads.shrinkRetainingCapacity(top.start);
        _ = stack.pop();
    }
    std.mem.reverse(NodeId, post.items);
    return post.toOwnedSlice(gpa);
}

// The nodes the end of region `r` reads, the exiting switch it ends in among them.
fn endReads(gpa: std.mem.Allocator, store: *const ir.Store, r: RegionId, out: *std.ArrayList(NodeId)) std.mem.Allocator.Error!void {
    const end = store.region(r).end;
    if (end.kind == .branch) try out.append(gpa, NodeId.of(end.target));
    for (store.refSlice(end.refs)) |ref| if (ref.kind == .node) try out.append(gpa, ref.nodeId());
}

// A parameter is a leaf of the unfolded term, and counts as one node, so a
// rule that reads a value fewer times lowers the count even when the value
// is a parameter.
fn addRef(m: *Measure, ref: ir.Ref, mult: u64, node_mult: []u64) void {
    switch (ref.kind) {
        .node => node_mult[ref.target] +|= mult,
        .row_param, .region_param, .input => m.add(.nodes, mult),
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
    var calls = scalar.Cache.init(testing.allocator, &store, &types, live);
    defer calls.deinit();
    const m = try ofRow(testing.allocator, &store, &types, live, &calls, row, false);
    // times(plus(p, p), plus(p, p)): three operations and four reads of p.
    try testing.expectEqual(@as(u64, 7), m.get(.nodes));
    try testing.expectEqual(@as(u64, 2), m.get(.graph_nodes));
}
