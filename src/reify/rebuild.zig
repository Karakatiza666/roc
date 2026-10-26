//! The rebuild (plan 1.3): a row copied through the builder, each node in
//! the region its placement (`place.zig`) chose.
//!
//! Only what the row's ends reach is copied, so a dead node is not (N6), and
//! a switch output nothing reads is dropped from every arm. Every node is
//! built by its smart constructor, in the region it is placed in and under
//! that region's facts, so a rule that a placement enables fires in the same
//! round, and hash-consing merges a node into an identical one of an
//! enclosing region (N5a). The number stage copies a normal row with its
//! rules off: it only moves nodes, and puts outputs and joins in order.
//!
//! The row keeps its id; its body is a new region, and the old one stays in
//! the store with nothing reaching it.

const std = @import("std");
const collections = @import("collections");
const ir = @import("ir.zig");
const builder_mod = @import("builder.zig");
const place = @import("place.zig");
const provenance = @import("provenance.zig");
const loops = @import("loops.zig");
const scalar = @import("scalar.zig");

const Allocator = std.mem.Allocator;
const Ref = ir.Ref;
const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const RowId = ir.RowId;
const TyId = ir.TyId;
const NameId = @import("types.zig").NameId;
const Types = @import("types.zig").Types;
const Builder = builder_mod.Builder;
const EndSpec = Builder.EndSpec;
const OriginId = provenance.OriginId;

/// How a rebuild builds.
pub const Options = struct {
    /// Build every node without its rules, and without the eta rule of
    /// `Builder.closure`: the number stage, over a row already normal.
    raw: bool = false,
    /// Per switch with several outputs: its outputs, by their old index, in
    /// the order to give them (N9). An output left out is one nothing reads.
    outputs: ?*const collections.DenseMapUnmanaged(NodeId, std.ArrayList(u32)) = null,
    /// Per switch with joins: its joins in the order to give them (N9).
    joins: ?*const collections.DenseMapUnmanaged(NodeId, std.ArrayList(RegionId)) = null,
    /// Per row parameter, by its old index: its new index (N8f). The row's
    /// parameter types are already the new ones, and nothing reads a
    /// parameter the row dropped.
    row_params: ?[]const ?u32 = null,
    /// Per row parameter, by its old index: the value that stands for it in
    /// a row that `into` builds.
    param_values: ?[]const Ref = null,
    /// Per row whose calls are inlined (V1, V2): its placement. A call of it
    /// is its body, built where the call stands, over the call's arguments.
    /// Such a row's body ends in one value.
    inline_rows: ?*const collections.DenseMapUnmanaged(RowId, *const place.Plan) = null,
    /// Per row whose closures become lambdas (V2): its placement. A
    /// `Closure` of it is a `Lambda` whose body is the row's, built in
    /// place, with the captured values for the row's first parameters and
    /// the lambda's parameters for the rest.
    lambda_rows: ?*const collections.DenseMapUnmanaged(RowId, *const place.Plan) = null,
};

/// Rebuild the row of `p` through `b`, which builds no other row now.
pub fn run(gpa: Allocator, b: *Builder, p: *const place.Plan, opts: Options) Allocator.Error!void {
    const old_body = b.store.row(p.row).body;
    var r: Rebuild = .{ .gpa = gpa, .b = b, .p = p, .opts = opts, .row_body = old_body };
    defer r.deinit();
    try b.rebuildRow(p.row);
    try r.regions.put(gpa, old_body, b.store.row(p.row).body);
    try r.fill(old_body);
    try r.finish(old_body, .row, null);
}

/// Build a new row over `params` with the body of `p`'s row copied into it,
/// each old parameter read as the value `values` gives for it once the new
/// row's body is open. Returns the new row. `b` builds no other row now.
pub fn into(
    gpa: Allocator,
    b: *Builder,
    p: *const place.Plan,
    params: []const TyId,
    ctx: anytype,
    comptime values: fn (@TypeOf(ctx), *Builder) Allocator.Error![]const Ref,
) Allocator.Error!RowId {
    const old_body = b.store.row(p.row).body;
    const row = try b.beginRow(params, b.store.row(p.row).result);
    const refs = try values(ctx, b);
    defer gpa.free(refs);
    var r: Rebuild = .{ .gpa = gpa, .b = b, .p = p, .opts = .{ .param_values = refs }, .row_body = old_body };
    defer r.deinit();
    try r.regions.put(gpa, old_body, b.store.row(row).body);
    try r.fill(old_body);
    try r.finish(old_body, .row, null);
    return row;
}

/// N12: rebuild the row of `p`, whose every call to itself is one of `tail`'s,
/// as a row whose body is one `Loop`. The parameters become the loop's slots,
/// a tail call is `Continue` with its arguments, and every other path of the
/// row ends in `Break` with the row's value, so the loop's one output is the
/// row's result. The row keeps its id and its parameters. `b` builds no other
/// row now.
pub fn runTail(gpa: Allocator, b: *Builder, p: *const place.Plan, tail: *const loops.Tail) Allocator.Error!void {
    const old_body = b.store.row(p.row).body;
    var r: Rebuild = .{ .gpa = gpa, .b = b, .p = p, .opts = .{}, .row_body = old_body, .tail = tail };
    defer r.deinit();
    var calls = tail.calls.keyIterator();
    while (calls.next()) |n| try r.skipped.put(gpa, n.*, {});
    var switches = tail.switches.keyIterator();
    while (switches.next()) |n| try r.skipped.put(gpa, n.*, {});
    const row = p.row;
    const params = try gpa.dupe(TyId, b.store.tySlice(b.store.row(row).params));
    defer gpa.free(params);
    const result = b.store.row(row).result;
    try b.rebuildRow(row);
    const body = try b.openRegion(.loop_body, params);
    const slots = try gpa.alloc(Ref, params.len);
    defer gpa.free(slots);
    const init = try gpa.alloc(Ref, params.len);
    defer gpa.free(init);
    for (slots, init, 0..) |*slot, *start, k| {
        slot.* = Ref.regionParam(body, @intCast(k));
        start.* = Ref.rowParam(@intCast(k));
    }
    r.opts.param_values = slots;
    try r.regions.put(gpa, old_body, body);
    try r.fill(old_body);
    try r.finish(old_body, .region, null);
    const loop = try b.loopOf(.loop, init, body, &.{result});
    try b.endRow(.{ .value = &.{loop} });
}

/// How a copied region closes: as a region, as the row's body (`endRow`),
/// or as the body of the lambda it names (`endLambda`).
const EndAs = union(enum) {
    region,
    row,
    lambda: RegionId,
};

/// The types the ends of an inlined body are built at, where the call stands
/// at a wider type than the row's result (design.md "Row Coercion Primitive").
///
/// A value the body ends with takes the demanded type if it is a `Tag`, a
/// `Wrap`, a `Crash`, a `Call`, an output of a value `Switch`, or a join
/// parameter. A `Tag` demands the member payload types of the union at its
/// payloads, a `Wrap` demands the backing of its nominal, and a `Switch`
/// demands its type at the value each arm ends with. Any other value has a
/// type its producer fixes, and conforms to the wider type as it is.
///
/// A value that something outside these ends also reads keeps its type,
/// because that reader needs it: it is demanded only when every reader of it
/// is an end that demands it, at one type.
const Demand = struct {
    gpa: Allocator,
    /// Per value an end demands a type of, keyed by `key`: that type.
    wanted: std.AutoHashMapUnmanaged(u64, TyId) = .empty,

    fn deinit(self: *Demand) void {
        self.wanted.deinit(self.gpa);
    }

    /// The type output `output` of old node `n` is built at, when it is demanded.
    fn ofNode(self: *const Demand, p: *const place.Plan, n: NodeId, output: usize) ?TyId {
        return self.wanted.get(key(Ref.node(p.aliasOf(n), @intCast(output))));
    }

    /// The type parameter `output` of the join `r` is built at, when it is demanded.
    fn ofJoin(self: *const Demand, r: RegionId, output: usize) ?TyId {
        return self.wanted.get(key(Ref.regionParam(r, @intCast(output))));
    }

    fn key(ref: Ref) u64 {
        return @bitCast(ref);
    }
};

/// How many times a value is demanded, and at which type.
const Arrivals = struct { count: u32, ty: TyId, conflict: bool };

/// The walk that finds what `Demand` holds, over the body of `p`'s row, from
/// its end value at the type `ty`.
const DemandWalk = struct {
    gpa: Allocator,
    store: *const ir.Store,
    types: *Types,
    p: *const place.Plan,
    out: Demand,
    reads: std.AutoHashMapUnmanaged(u64, u32) = .empty,
    arrivals: std.AutoHashMapUnmanaged(u64, Arrivals) = .empty,

    fn run(gpa: Allocator, store: *const ir.Store, types: *Types, p: *const place.Plan, ty: TyId) Allocator.Error!Demand {
        var w: DemandWalk = .{ .gpa = gpa, .store = store, .types = types, .p = p, .out = .{ .gpa = gpa } };
        defer w.reads.deinit(gpa);
        defer w.arrivals.deinit(gpa);
        errdefer w.out.deinit();
        try w.countReads();
        const end = store.region(store.row(p.row).body).end;
        try w.demand(store.refSlice(end.refs)[0], ty);
        return w.out;
    }

    // Every read of a value in the body: by a node and by the end of a region.
    // A node the plan merges into another still counts, so a merge keeps a
    // value from being demanded and never the reverse.
    fn countReads(self: *DemandWalk) Allocator.Error!void {
        var nodes = self.p.info.constKeyIterator();
        while (nodes.next()) |n| for (self.store.refSlice(self.store.node(n).args)) |ref| try self.countRead(ref);
        for (self.p.regions.items) |r| for (self.store.refSlice(self.store.region(r).end.refs)) |ref| try self.countRead(ref);
    }

    fn countRead(self: *DemandWalk, ref: Ref) Allocator.Error!void {
        if (ref.kind == .row_param or ref.kind == .input) return;
        const gop = try self.reads.getOrPut(self.gpa, Demand.key(self.canonical(ref)));
        if (!gop.found_existing) gop.value_ptr.* = 0;
        gop.value_ptr.* += 1;
    }

    fn canonical(self: *const DemandWalk, ref: Ref) Ref {
        return if (ref.kind == .node) Ref.node(self.p.aliasOf(ref.nodeId()), ref.output) else ref;
    }

    // `ref` is read at the type `ty` by one reader that demands it.
    fn demand(self: *DemandWalk, ref: Ref, ty: TyId) Allocator.Error!void {
        const have = self.store.refTy(self.p.row, ref);
        if (have == ty) return;
        if (!try self.types.widens(have, ty)) @import("base").invariant("reify rebuild: an inlined end of type {d} is demanded at type {d}, which it does not widen to", .{ have.index(), ty.index() });
        if (ref.kind == .row_param or ref.kind == .input) return;
        const at = self.canonical(ref);
        const gop = try self.arrivals.getOrPut(self.gpa, Demand.key(at));
        if (!gop.found_existing) gop.value_ptr.* = .{ .count = 0, .ty = ty, .conflict = false };
        gop.value_ptr.count += 1;
        if (gop.value_ptr.ty != ty) gop.value_ptr.conflict = true;
        const all = self.reads.get(Demand.key(at)) orelse
            @import("base").invariant("reify rebuild: a demanded value has no reader", .{});
        if (gop.value_ptr.count != all or gop.value_ptr.conflict) return;
        switch (at.kind) {
            .region_param => {
                try self.out.wanted.put(self.gpa, Demand.key(at), ty);
                try self.demandJumps(at, ty);
            },
            .node => try self.demandNode(at, ty),
            .row_param, .input => unreachable, // demands are made on nodes and region parameters, never row parameters or slots
        }
    }

    // A join parameter at `ty`: every jump to the join passes it at `ty`.
    fn demandJumps(self: *DemandWalk, param: Ref, ty: TyId) Allocator.Error!void {
        const join = param.regionId();
        for (self.p.regions.items) |r| {
            const end = self.store.region(r).end;
            if (end.kind != .jump or end.target != join.index()) continue;
            try self.demand(self.store.refSlice(end.refs)[param.output], ty);
        }
    }

    // The values the node `at` reads that its own type fixes.
    fn demandNode(self: *DemandWalk, at: Ref, ty: TyId) Allocator.Error!void {
        const nd = self.store.node(at.nodeId());
        switch (nd.op) {
            .tag, .wrap, .crash, .call, .switch_ => try self.out.wanted.put(self.gpa, Demand.key(at), ty),
            .lit, .derived, .record, .tuple, .list, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .for_range, .for_list, .loop, .lambda, .apply => return,
        }
        switch (nd.op) {
            .tag => {
                const args = try self.gpa.dupe(Ref, self.store.refSlice(nd.args));
                defer self.gpa.free(args);
                const index = self.types.memberIndex(ty, NameId.of(nd.payload)) orelse
                    @import("base").invariant("reify rebuild: the demanded union has no tag {s}", .{self.types.nameText(NameId.of(nd.payload))});
                const members = self.types.memberSlice(self.types.get(ty).tag_union);
                const payload = try self.gpa.dupe(TyId, self.types.tySlice(members[index].tys));
                defer self.gpa.free(payload);
                for (args, payload) |arg, want| try self.demand(arg, want);
            },
            .wrap => {
                const arg = self.store.refSlice(nd.args)[0];
                try self.demand(arg, try self.types.unfold(ty));
            },
            .switch_ => {
                const arms = try self.gpa.dupe(RegionId, self.store.regionSlice(nd.regions)[0..nd.payload]);
                defer self.gpa.free(arms);
                for (arms) |arm| try self.demandEnd(arm, at.output, ty);
            },
            .crash, .call => {},
            .lit, .derived, .record, .tuple, .list, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .for_range, .for_list, .loop, .lambda, .apply => unreachable, // only ops that carry demands are demanded here (switch_, crash, call)
        }
    }

    // Output `output` of the value region `r` ends with, at `ty`: a value, or
    // the value of the one join an exiting switch continues in.
    fn demandEnd(self: *DemandWalk, r: RegionId, output: u32, ty: TyId) Allocator.Error!void {
        const end = self.store.region(r).end;
        switch (end.kind) {
            .value => try self.demand(self.store.refSlice(end.refs)[output], ty),
            .branch => {
                const nd = self.store.node(NodeId.of(end.target));
                const joins = self.store.regionSlice(nd.regions)[nd.payload..];
                if (joins.len == 1) try self.demandEnd(joins[0], output, ty);
            },
            .open, .jump, .return_, .continue_, .break_ => {},
        }
    }
};

/// What an old node became: the ref of its new node, and, for a switch
/// whose outputs were dropped or reordered, where each old output went.
const Built = struct {
    ref: Ref,
    /// Per old output: its new index, or `no_output` for one the new node does
    /// not give. Empty when outputs keep their places.
    outs: []const u32 = &.{},
    /// Per old output that the new node does not give: the value that stands
    /// for it. Empty for a node whose dropped outputs nothing reads.
    repl: []const Ref = &.{},
    /// The number of outputs the new node has.
    width: u32,

    const no_output = std.math.maxInt(u32);
};

/// The loop being copied under a rewrite (`loops.zig`): the rewrite, the body
/// of the loop it builds, and the new values its slots start from.
const Active = struct {
    rw: *const loops.Rewrite,
    body: RegionId,
    /// Per old slot, its initial value in the new row.
    init: []const Ref,
};

const Rebuild = struct {
    gpa: Allocator,
    b: *Builder,
    p: *const place.Plan,
    opts: Options,
    /// The origins of the call or closure whose row this copy inlines: each
    /// copied node's origins are reached through them (N10).
    via: []const OriginId = &.{},
    /// The types the ends of the body being inlined are built at, where the
    /// call stands at a wider type than the row's result.
    demand: ?*const Demand = null,
    /// The origins of the node being copied.
    here: []const OriginId = &.{},
    /// Per node the plan merges others into (N5c): those others, built on
    /// first use.
    aliases: ?collections.DenseMapUnmanaged(NodeId, std.ArrayList(NodeId)) = null,
    nodes: collections.DenseMapUnmanaged(NodeId, Built) = .empty,
    regions: collections.DenseMapUnmanaged(RegionId, RegionId) = .empty,
    /// The body of the row `p` places, as it stood before the rebuild.
    row_body: RegionId = RegionId.none,
    /// Whether this copy builds a body into another one: an inlined call or a
    /// lambda. A rule that reads the row's result does not apply there.
    inside: bool = false,
    /// Nodes the copy does not build: what a loop rule or N12 replaced.
    skipped: std.AutoHashMapUnmanaged(NodeId, void) = .empty,
    /// Per old loop body being copied under a rewrite: that rewrite.
    rewrites: collections.DenseMapUnmanaged(RegionId, *const Active) = .empty,
    /// The loops being copied, innermost last: null for one copied as it is,
    /// and for a lambda, whose paths are not the loop's.
    frames: std.ArrayList(?*const Active) = .empty,
    /// Where set, the row is rebuilt as a loop (N12).
    tail: ?*const loops.Tail = null,
    arena_impl: ?std.heap.ArenaAllocator = null,
    /// How the row of `p` uses its values, read by the loop rules; made when
    /// the first loop asks.
    usage_impl: ?scalar.Usage = null,

    // What the rules of the loop being copied allocate.
    fn arena(self: *Rebuild) Allocator {
        if (self.arena_impl == null) self.arena_impl = std.heap.ArenaAllocator.init(self.gpa);
        return self.arena_impl.?.allocator();
    }

    // How the row of `p` uses its values.
    fn usage(self: *Rebuild) Allocator.Error!*const scalar.Usage {
        if (self.usage_impl == null) self.usage_impl = try scalar.Usage.ofPlan(self.arena(), self.p);
        return &self.usage_impl.?;
    }

    fn deinit(self: *Rebuild) void {
        self.skipped.deinit(self.gpa);
        self.rewrites.deinit(self.gpa);
        self.frames.deinit(self.gpa);
        if (self.arena_impl) |*impl| impl.deinit();
        if (self.aliases) |*map| {
            var lists = map.valueIterator();
            while (lists.next()) |l| l.deinit(self.gpa);
            map.deinit(self.gpa);
        }
        var it = self.nodes.valueIterator();
        while (it.next()) |v| {
            self.gpa.free(v.outs);
            self.gpa.free(v.repl);
        }
        self.nodes.deinit(self.gpa);
        self.regions.deinit(self.gpa);
    }

    fn store(self: *const Rebuild) *ir.Store {
        return self.b.store;
    }

    fn mapRef(self: *const Rebuild, ref: Ref) Ref {
        return switch (ref.kind) {
            .row_param => if (self.opts.param_values) |values|
                values[ref.output]
            else if (self.opts.row_params) |map|
                Ref.rowParam(@intCast(map[ref.output].?))
            else
                ref,
            .region_param => blk: {
                if (self.rewrites.get(ref.regionId())) |act| break :blk self.paramRef(act, ref.output);
                break :blk Ref.regionParam(self.regions.get(ref.regionId()).?, ref.output);
            },
            .input => ref,
            .node => blk: {
                const built = self.nodes.get(self.p.aliasOf(ref.nodeId())) orelse
                    @import("base").invariant("reify rebuild: node {d} is read before it is built", .{ref.target});
                const k: u32 = if (built.outs.len == 0) ref.output else built.outs[ref.output];
                if (k == Built.no_output) {
                    if (built.repl.len == 0) @import("base").invariant("reify rebuild: an output a rewrite dropped is read", .{});
                    break :blk built.repl[ref.output];
                }
                break :blk if (built.width > 1) Ref.node(built.ref.nodeId(), @intCast(k)) else built.ref;
            },
        };
    }

    // What parameter `k` of the old loop body a rewrite replaces is in the new one.
    fn paramRef(self: *const Rebuild, act: *const Active, k: u32) Ref {
        return switch (act.rw.params[k]) {
            .param => |i| Ref.regionParam(act.body, @intCast(i)),
            .init => |slot| act.init[slot],
            .same_as => |j| self.paramRef(act, j),
            // A slot the rule removed because nothing that stays reads it. Values
            // computed only for its next value are still built in this round,
            // over its initial value; nothing reads them, so the next round
            // does not copy them.
            .gone => act.init[k - (act.rw.params.len - act.init.len)],
            // A split slot is read through the nodes that stand for its components.
            .split => @import("base").invariant("reify rebuild: a split loop slot is read whole", .{}),
        };
    }

    // The loop whose paths the region being copied is on, when a rewrite copies it.
    fn active(self: *const Rebuild) ?*const Active {
        if (self.frames.items.len == 0) return null;
        return self.frames.items[self.frames.items.len - 1];
    }

    fn mapRefs(self: *const Rebuild, refs: []const Ref) Allocator.Error![]Ref {
        const out = try self.gpa.alloc(Ref, refs.len);
        for (refs, out) |r, *o| o.* = self.mapRef(r);
        return out;
    }

    fn fill(self: *Rebuild, r: RegionId) Allocator.Error!void {
        for (self.p.membersOf(r)) |m| {
            // A node a rule stands in for, or built ahead of its region, is not built again.
            if (self.skipped.contains(m) or self.nodes.contains(m)) continue;
            try self.node(m);
        }
    }

    // Close the region being built, a copy of old region `r`, with `r`'s end,
    // by the rule `as` names. A region that ends in an exiting switch with a
    // join goes on in the join's copy, which the end of that join closes.
    // `select` gives the outputs an arm of a value switch keeps, by old
    // index, in new order.
    fn finish(self: *Rebuild, r: RegionId, as: EndAs, select_in: ?[]const u32) Allocator.Error!void {
        const end = self.store().region(r).end;
        const old_refs = try self.gpa.dupe(Ref, self.store().refSlice(end.refs));
        defer self.gpa.free(old_refs);
        // N12: the paths of a row built as a loop end in its terminators.
        if (self.tail) |t| if (t.spine.contains(r)) switch (end.kind) {
            .value, .return_ => return self.tailValue(t, old_refs[0], as),
            .jump, .branch, .open, .continue_, .break_ => {},
        };
        // N14b: a loop that splits slots gives each part its component.
        if (self.active()) |act| if (act.rw.split) |sp| {
            const bounded = act.rw.op != .loop;
            if (end.kind == .continue_ or (end.kind == .break_ and bounded)) {
                const refs = try self.partRefs(act, sp, old_refs);
                defer self.gpa.free(refs);
                return self.close(if (end.kind == .continue_) .{ .continue_ = refs } else .{ .break_ = refs }, as);
            }
        };
        // A loop under a rewrite keeps the values of the slots and outputs it keeps.
        var select = select_in;
        var returns_break = false;
        if (self.active()) |act| switch (end.kind) {
            .continue_ => select = act.rw.slots,
            .break_ => select = act.rw.break_keep,
            .return_ => returns_break = act.rw.returns_break,
            .value, .jump, .branch, .open => {},
        };
        const picked = if (select) |sel| blk: {
            const out = try self.gpa.alloc(Ref, sel.len);
            for (sel, out) |k, *o| o.* = old_refs[k];
            break :blk out;
        } else try self.gpa.dupe(Ref, old_refs);
        defer self.gpa.free(picked);
        const refs = try self.mapRefs(picked);
        defer self.gpa.free(refs);
        const spec: EndSpec = switch (end.kind) {
            .open => unreachable, // ends of the old rows are closed
            .value => .{ .value = refs },
            .jump => .{ .jump = .{ .join = self.regions.get(RegionId.of(end.target)).?, .args = refs } },
            .return_ => if (returns_break) .{ .break_ = refs[0..1] } else .{ .return_ = refs[0] },
            .continue_ => .{ .continue_ = refs },
            .break_ => .{ .break_ = refs },
            .branch => {
                const sw = NodeId.of(end.target);
                const new_sw = self.nodes.get(sw).?.ref.nodeId();
                const nd = self.store().node(sw);
                const joins = self.store().regionSlice(nd.regions)[nd.payload..];
                switch (joins.len) {
                    0 => {},
                    1 => {
                        const join = joins[0];
                        try self.b.continueIn(new_sw, self.regions.get(join).?);
                        try self.fill(join);
                        return self.finish(join, as, null);
                    },
                    else => @import("base").invariant("reify rebuild: an exiting switch continues in {d} joins", .{joins.len}),
                }
                return self.close(.{ .branch = new_sw }, as);
            },
        };
        try self.close(spec, as);
    }

    // N14b: per part of the loop `act` builds, the value the old values of
    // the slots give it, for the `Continue` or `Break` that ends with `old_refs`.
    fn partRefs(self: *Rebuild, act: *const Active, sp: *const loops.Split, old_refs: []const Ref) Allocator.Error![]Ref {
        const header: u32 = @intCast(act.rw.params.len - sp.shapes.len);
        const out = try self.gpa.alloc(Ref, sp.parts.len);
        errdefer self.gpa.free(out);
        for (sp.parts, out, 0..) |leaf, *o, j| {
            const old_param = Ref.regionParam(act.rw.body, @intCast(header + leaf.index));
            o.* = try self.partValue(act, old_param, Ref.regionParam(act.body, @intCast(header + j)), old_refs[leaf.index], leaf.path);
        }
        return out;
    }

    // The component at `path` of the old value `v` of a slot: a component of
    // the construction `v` is, the new parameter when `v` is the slot itself,
    // and otherwise a read of the value.
    fn partValue(self: *Rebuild, act: *const Active, old_param: Ref, new_param: Ref, v: Ref, path: []const u32) Allocator.Error!Ref {
        var cur = v;
        var rest = path;
        while (rest.len > 0) {
            if (cur == old_param) return new_param;
            if (cur.kind != .node or cur.output != 0) break;
            const nd = self.store().node(cur.nodeId());
            if ((nd.op != .record and nd.op != .tuple) or nd.aux.len != 0) break;
            cur = self.store().refSlice(nd.args)[rest[0]];
            rest = rest[1..];
        }
        _ = act;
        self.mark();
        return self.components(self.mapRef(cur), rest);
    }

    // The component of `value` at `path`.
    fn components(self: *Rebuild, value: Ref, path: []const u32) Allocator.Error!Ref {
        var ref = value;
        for (path) |i| {
            const ty = self.store().refTy(self.b.row, ref);
            ref = switch (self.b.types.get(ty)) {
                .record => try self.b.field(ref, i),
                .tuple => try self.b.index(ref, i),
                .bool_, .str, .int, .float, .dec, .tag_union, .list, .nominal, .func, .opaque_, .recursive => unreachable, // a shape splits records and tuples only
            };
        }
        return ref;
    }

    // The aggregate of type `ty` that the outputs of `loop` from `next` make,
    // as `shape` splits it.
    fn aggregateFrom(self: *Rebuild, loop: NodeId, ty: TyId, shape: scalar.Shape, next: *u32) Allocator.Error!Ref {
        switch (shape) {
            .whole => {
                defer next.* += 1;
                return Ref.node(loop, @intCast(next.*));
            },
            .split => |children| {
                const parts = try self.gpa.alloc(Ref, children.len);
                defer self.gpa.free(parts);
                for (children, parts, 0..) |child, *part, i| {
                    part.* = try self.aggregateFrom(loop, self.b.types.componentTy(ty, @intCast(i)), child, next);
                }
                self.mark();
                return switch (self.b.types.get(ty)) {
                    .record => try self.b.record(ty, parts),
                    .tuple => try self.b.tuple(ty, parts),
                    .bool_, .str, .int, .float, .dec, .tag_union, .list, .nominal, .func, .opaque_, .recursive => unreachable, // a shape splits records and tuples only
                };
            },
        }
    }

    // N12: the value a path of the row ends in. A tail call is the next turn,
    // a value switch is an exiting switch whose arms end the same way, and any
    // other value is where the loop ends.
    fn tailValue(self: *Rebuild, t: *const loops.Tail, ref: Ref, as: EndAs) Allocator.Error!void {
        if (ref.kind == .node) {
            const n = ref.nodeId();
            const nd = self.store().node(n);
            if (t.calls.contains(n)) {
                const old_args = try self.gpa.dupe(Ref, self.store().refSlice(nd.args));
                defer self.gpa.free(old_args);
                const args = try self.mapRefs(old_args);
                defer self.gpa.free(args);
                return self.close(.{ .continue_ = args }, as);
            }
            if (t.switches.contains(n)) {
                const old_regions = try self.gpa.dupe(RegionId, self.store().regionSlice(nd.regions));
                defer self.gpa.free(old_regions);
                const aux = try self.gpa.dupe(u32, self.store().wordSlice(nd.aux));
                defer self.gpa.free(aux);
                const old_args = try self.gpa.dupe(Ref, self.store().refSlice(nd.args));
                defer self.gpa.free(old_args);
                const args = try self.mapRefs(old_args);
                defer self.gpa.free(args);
                // No outputs: the switch is the exiting one, and its arms end the loop's turn.
                try self.switchNode(n, nd, args, &.{}, aux, old_regions);
                return self.close(.{ .branch = self.nodes.get(n).?.ref.nodeId() }, as);
            }
        }
        const value = [1]Ref{self.mapRef(ref)};
        try self.close(.{ .break_ = &value }, as);
    }

    fn close(self: *Rebuild, spec: EndSpec, as: EndAs) Allocator.Error!void {
        switch (as) {
            .region => try self.b.close(spec),
            .row => try self.b.endRow(spec),
            .lambda => |body| try self.b.endLambda(body, spec),
        }
    }

    fn make(self: *Rebuild, spec: builder_mod.NodeSpec) Allocator.Error!Ref {
        self.mark();
        return if (self.opts.raw) self.b.makeRaw(spec) else self.b.make(spec);
    }

    // Build what follows under the origins of the node being copied.
    fn mark(self: *Rebuild) void {
        self.b.origins = self.here;
    }

    // The origins of old node `n` and of the nodes the plan merges into it
    // (N5c), each reached through `via` (N10).
    fn originsOf(self: *Rebuild, n: NodeId) Allocator.Error![]OriginId {
        const prov = &self.store().provenance;
        var own: std.ArrayList(OriginId) = .empty;
        defer own.deinit(self.gpa);
        try own.appendSlice(self.gpa, prov.of(n));
        if (try self.aliasesOf(n)) |merged| for (merged) |m| try own.appendSlice(self.gpa, prov.of(m));
        var out: std.ArrayList(OriginId) = .empty;
        errdefer out.deinit(self.gpa);
        for (own.items) |o| {
            if (self.via.len == 0) {
                if (std.mem.findScalar(OriginId, out.items, o) == null) try out.append(self.gpa, o);
            } else for (self.via) |c| {
                const t = try prov.through(self.gpa, o, c);
                if (std.mem.findScalar(OriginId, out.items, t) == null) try out.append(self.gpa, t);
            }
        }
        return out.toOwnedSlice(self.gpa);
    }

    fn aliasesOf(self: *Rebuild, n: NodeId) Allocator.Error!?[]const NodeId {
        if (self.aliases == null) {
            var map: collections.DenseMapUnmanaged(NodeId, std.ArrayList(NodeId)) = .empty;
            errdefer {
                var lists = map.valueIterator();
                while (lists.next()) |l| l.deinit(self.gpa);
                map.deinit(self.gpa);
            }
            var it = self.p.info.constIterator();
            while (it.next()) |e| {
                if (e.value_ptr.alias == e.key_ptr.*) continue;
                const gop = try map.getOrPut(self.gpa, e.value_ptr.alias);
                if (!gop.found_existing) gop.value_ptr.* = .empty;
                try gop.value_ptr.append(self.gpa, e.key_ptr.*);
            }
            self.aliases = map;
        }
        const list = self.aliases.?.get(n) orelse return null;
        return list.items;
    }

    fn node(self: *Rebuild, n: NodeId) Allocator.Error!void {
        const s = self.store();
        const nd = s.node(n);
        // Building appends to the pools these spans point into.
        const old_args = try self.gpa.dupe(Ref, s.refSlice(nd.args));
        defer self.gpa.free(old_args);
        const tys = try self.gpa.dupe(TyId, s.tySlice(nd.tys));
        defer self.gpa.free(tys);
        const aux = try self.gpa.dupe(u32, s.wordSlice(nd.aux));
        defer self.gpa.free(aux);
        if (self.demand) |wanted| for (tys, 0..) |*t, k| {
            if (wanted.ofNode(self.p, n, k)) |ty| t.* = ty;
        };
        const old_regions = try self.gpa.dupe(RegionId, s.regionSlice(nd.regions));
        defer self.gpa.free(old_regions);
        const args = try self.mapRefs(old_args);
        defer self.gpa.free(args);
        const origins = try self.originsOf(n);
        defer self.gpa.free(origins);
        const outer = self.here;
        self.here = origins;
        defer {
            self.here = outer;
            self.b.origins = &.{};
        }

        const built: Built = switch (nd.op) {
            .switch_ => return self.switchNode(n, nd, args, tys, aux, old_regions),
            .and_, .or_ => blk: {
                const regions = try self.gpa.alloc(RegionId, old_regions.len);
                defer self.gpa.free(regions);
                for (old_regions, regions) |old, *new| {
                    new.* = try self.b.openOperand(args[0..1], nd.op);
                    try self.regions.put(self.gpa, old, new.*);
                    try self.fill(old);
                    try self.finish(old, .region, null);
                }
                break :blk .{ .ref = try self.make(.{ .op = nd.op, .payload = nd.payload, .args = args, .tys = tys, .regions = regions, .aux = aux }), .width = 1 };
            },
            .for_range, .for_list, .loop, .lambda => blk: {
                // The loop rules (`loops.zig`): the loop is copied as a rewrite says.
                if (nd.op != .lambda and !self.opts.raw) {
                    const where: loops.Where = .{ .row_body = if (self.inside) null else self.row_body, .usage = try self.usage() };
                    if (try loops.analyze(self.arena(), self.p, self.b.types, n, where)) |found| {
                        const rw = found;
                        break :blk try self.rewrittenLoop(nd, &rw, args);
                    }
                }
                // A loop copied as it is, and a lambda, are paths of their own.
                try self.frames.append(self.gpa, null);
                defer _ = self.frames.pop();
                const regions = try self.gpa.alloc(RegionId, old_regions.len);
                defer self.gpa.free(regions);
                for (old_regions, regions) |old, *new| {
                    const params = try self.gpa.dupe(TyId, s.tySlice(s.region(old).params));
                    defer self.gpa.free(params);
                    new.* = try self.b.openRegion(s.region(old).kind, params);
                    if (nd.op == .for_list) try self.b.noteListLoop(new.*, args[0]);
                    try self.regions.put(self.gpa, old, new.*);
                    try self.fill(old);
                    try self.finish(old, if (nd.op == .lambda) .{ .lambda = new.* } else .region, null);
                }
                break :blk .{ .ref = try self.make(.{ .op = nd.op, .payload = nd.payload, .args = args, .tys = tys, .regions = regions, .aux = aux }), .width = @intCast(tys.len) };
            },
            .closure => .{
                .ref = if (self.lambdaOf(RowId.of(nd.payload))) |row|
                    try self.lambda(row, args, tys[0])
                else if (self.opts.raw)
                    try self.make(.{ .op = .closure, .payload = nd.payload, .args = args, .tys = tys })
                else blk: {
                    self.mark();
                    break :blk try self.b.closure(RowId.of(nd.payload), args, tys[0]);
                },
                .width = 1,
            },
            .call => .{ .ref = if (self.opts.inline_rows) |rows| (if (rows.get(RowId.of(nd.payload))) |callee| try self.inlined(callee, args, tys[0]) else try self.make(.{ .op = nd.op, .payload = nd.payload, .args = args, .tys = tys, .aux = aux })) else try self.make(.{ .op = nd.op, .payload = nd.payload, .args = args, .tys = tys, .aux = aux }), .width = 1 },
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .apply => .{
                .ref = try self.make(.{ .op = nd.op, .payload = nd.payload, .args = args, .tys = tys, .aux = aux }),
                .width = 1,
            },
        };
        try self.nodes.put(self.gpa, n, built);
    }

    // N11: the loop `nd` copied as the rewrite `rw` says. What the header
    // reads from the old body is built first, where the loop stands. The new
    // body is built from the old body's nodes without those the rule replaced,
    // then, when the rule moves the body into one of its arms, from that
    // arm's nodes and end. The rewrite says which slots and outputs the new
    // loop keeps and what the others are.
    fn rewrittenLoop(self: *Rebuild, nd: ir.Node, rw: *const loops.Rewrite, args: []const Ref) Allocator.Error!Built {
        const lead: usize = switch (nd.op) {
            .for_range => 2,
            .for_list => 1,
            .loop => 0,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .lambda, .apply => unreachable, // only a loop is rewritten
        };
        for (rw.hoist) |m| try self.node(m);
        const slot_count = if (rw.split) |sp| sp.parts.len else rw.slots.len;
        const new_args = try self.gpa.alloc(Ref, rw.header.len + slot_count);
        defer self.gpa.free(new_args);
        for (rw.header, new_args[0..rw.header.len]) |h, *o| o.* = self.mapRef(h);
        if (rw.split) |sp| {
            // N14b: each part starts as the component of its slot's initial value.
            for (sp.parts, new_args[rw.header.len..]) |leaf, *o| {
                self.mark();
                o.* = try self.components(args[lead + leaf.index], leaf.path);
            }
        } else for (rw.slots, new_args[rw.header.len..]) |k, *o| o.* = args[lead + k];
        const body = try self.b.openRegion(.loop_body, rw.param_tys);
        if (rw.op == .for_list) try self.b.noteListLoop(body, new_args[0]);
        var act: Active = .{ .rw = rw, .body = body, .init = args[lead..] };
        try self.regions.put(self.gpa, rw.body, body);
        if (rw.continue_in) |r| try self.regions.put(self.gpa, r, body);
        try self.rewrites.put(self.gpa, rw.body, &act);
        defer _ = self.rewrites.remove(rw.body);
        for (rw.skip) |m| try self.skipped.put(self.gpa, m, {});
        for (rw.stands) |st| try self.nodes.put(self.gpa, st.node, .{ .ref = Ref.regionParam(body, @intCast(st.param)), .width = 1 });
        try self.frames.append(self.gpa, &act);
        defer _ = self.frames.pop();
        try self.fill(rw.body);
        if (rw.continue_in) |r| {
            try self.fill(r);
            try self.finish(r, .region, null);
        } else try self.finish(rw.body, .region, null);
        const ref = try self.make(.{ .op = rw.op, .payload = rw.payload, .args = new_args, .tys = rw.out_tys, .regions = &.{body} });
        const outs = try self.gpa.alloc(u32, rw.outputs.len);
        errdefer self.gpa.free(outs);
        const repl = try self.gpa.alloc(Ref, rw.outputs.len);
        errdefer self.gpa.free(repl);
        for (rw.outputs, outs, repl, 0..) |to, *out, *value, o| {
            var at = to;
            while (std.meta.activeTag(at) == .same_as) at = rw.outputs[at.same_as];
            switch (at) {
                .output => |k| {
                    out.* = k;
                    value.* = ref;
                },
                .init => |slot| {
                    out.* = Built.no_output;
                    value.* = args[lead + slot];
                },
                // Every `Break` gave this value, which stands outside the loop.
                .value => |v| {
                    out.* = Built.no_output;
                    value.* = self.mapRef(v);
                },
                // Nothing reads an output the rule dropped.
                .gone => {
                    out.* = Built.no_output;
                    value.* = ref;
                },
                // N14b: the aggregate the outputs of the parts make.
                .rebuilt => |slot| {
                    const sp = rw.split.?;
                    out.* = Built.no_output;
                    var next = sp.first[slot];
                    value.* = try self.aggregateFrom(ref.nodeId(), sp.slot_tys[slot], sp.shapes[slot], &next);
                },
                .same_as => unreachable, // resolved by the loop above
            }
            _ = o;
        }
        return .{ .ref = ref, .outs = outs, .repl = repl, .width = @intCast(rw.out_tys.len) };
    }

    // The body of the row `callee` places, built in the current region over
    // `args` for its parameters: its value, at the type `ty` of the call. A
    // call at a type wider than the row's result has the ends of the body
    // built at that type (`Demand`). Calls and closures in it are inlined as
    // the caller's are.
    fn inlined(self: *Rebuild, callee: *const place.Plan, args: []const Ref, ty: TyId) Allocator.Error!Ref {
        var wanted: ?Demand = if (ty == self.store().row(callee.row).result) null else try DemandWalk.run(self.gpa, self.store(), self.b.types, callee, ty);
        defer if (wanted) |*w| w.deinit();
        var r: Rebuild = .{ .gpa = self.gpa, .b = self.b, .p = callee, .opts = .{ .param_values = args, .inline_rows = self.opts.inline_rows, .lambda_rows = self.opts.lambda_rows }, .via = self.here, .demand = if (wanted) |*w| w else null, .inside = true };
        defer r.deinit();
        const body = self.store().row(callee.row).body;
        try r.regions.put(self.gpa, body, self.b.current());
        try r.fill(body);
        const end = self.store().region(body).end;
        std.debug.assert(end.kind == .value and end.refs.len == 1);
        return r.mapRef(self.store().refSlice(end.refs)[0]);
    }

    fn lambdaOf(self: *const Rebuild, row: RowId) ?*const place.Plan {
        const rows = self.opts.lambda_rows orelse return null;
        return rows.get(row);
    }

    // `Lambda` of the function type `ty`: a closure of the row `callee`
    // places, with `captures` for its first parameters, built in place.
    fn lambda(self: *Rebuild, callee: *const place.Plan, captures: []const Ref, ty: TyId) Allocator.Error!Ref {
        const s = self.store();
        const all = s.tySlice(s.row(callee.row).params);
        const params = try self.gpa.dupe(TyId, all[captures.len..]);
        defer self.gpa.free(params);
        const region = try self.b.openRegion(.lambda_body, params);
        const values = try self.gpa.alloc(Ref, captures.len + params.len);
        defer self.gpa.free(values);
        @memcpy(values[0..captures.len], captures);
        for (values[captures.len..], 0..) |*v, k| v.* = Ref.regionParam(region, @intCast(k));
        var r: Rebuild = .{ .gpa = self.gpa, .b = self.b, .p = callee, .opts = .{ .param_values = values, .inline_rows = self.opts.inline_rows, .lambda_rows = self.opts.lambda_rows }, .via = self.here, .inside = true };
        defer r.deinit();
        const body = s.row(callee.row).body;
        try r.regions.put(self.gpa, body, region);
        try r.fill(body);
        try r.finish(body, .{ .lambda = region }, null);
        return self.make(.{ .op = .lambda, .tys = &.{ty}, .regions = &.{region} });
    }

    // Whether the switch `n` and its arms are the only readers of its
    // scrutinee, a node of the old row, and of the `Unwrap`s of nominals that
    // lead to the node it reads, each of which only the `Unwrap` after it reads.
    fn soleReader(self: *const Rebuild, n: NodeId, nd: ir.Node) bool {
        const s = self.store();
        var t = s.refSlice(nd.args)[0];
        var reader = n;
        const arms = s.regionSlice(nd.regions);
        while (true) {
            if (t.kind != .node) return false;
            const sites = (self.p.uses.get(t.nodeId()) orelse return false).items;
            for (sites) |site| {
                const at: RegionId = switch (site) {
                    .node => |r| if (r == reader or (reader != n and r == n)) continue else s.node(r).region,
                    .region => |r| r,
                };
                for (arms) |arm| {
                    if (s.encloses(arm, at)) break;
                } else return false;
            }
            const read = s.node(t.nodeId());
            if (read.op != .unwrap) return true;
            reader = t.nodeId();
            t = s.refSlice(read.args)[0];
        }
    }

    fn switchNode(self: *Rebuild, n: NodeId, nd: ir.Node, args: []const Ref, tys: []const TyId, aux: []const u32, old_regions: []const RegionId) Allocator.Error!void {
        const s = self.store();
        const arms = old_regions[0..nd.payload];
        // The tags the old arms are for, when this is a tag switch. The new
        // scrutinee can have fewer tags than the old one, because an inlined
        // argument conforms to a wider parameter: an arm for a tag it lacks is
        // dead and is not built (design.md "Row Coercion Primitive").
        const old_ty = s.refTy(self.p.row, s.refSlice(nd.args)[0]);
        const old_names: ?[]NameId = switch (self.b.types.get(old_ty)) {
            .tag_union => |span| blk: {
                const members = self.b.types.memberSlice(span);
                const out = try self.gpa.alloc(NameId, members.len);
                for (members, out) |m, *o| o.* = m.name;
                break :blk out;
            },
            .bool_, .str, .int, .float, .dec, .record, .tuple, .list, .nominal, .func, .opaque_, .recursive => null,
        };
        defer if (old_names) |names| self.gpa.free(names);
        // The outputs kept, by old index, in their new order.
        var select: std.ArrayList(u32) = .empty;
        defer select.deinit(self.gpa);
        if (self.opts.outputs) |order| if (order.get(n)) |o| {
            for (o.items) |k| if (self.p.outputRead(n, k)) try select.append(self.gpa, k);
        };
        if (select.items.len == 0) for (0..tys.len) |k| {
            if (self.p.outputRead(n, @intCast(k))) try select.append(self.gpa, @intCast(k));
        };
        const new_tys = try self.gpa.alloc(TyId, select.items.len);
        defer self.gpa.free(new_tys);
        for (select.items, new_tys) |k, *t| t.* = tys[k];
        const outs = try self.gpa.alloc(u32, tys.len);
        errdefer self.gpa.free(outs);
        @memset(outs, std.math.maxInt(u32));
        for (select.items, 0..) |k, j| outs[k] = @intCast(j);

        // Joins first: an arm names its join in its `Jump`.
        const old_joins = try self.gpa.dupe(RegionId, old_regions[nd.payload..]);
        defer self.gpa.free(old_joins);
        if (self.opts.joins) |order| if (order.get(n)) |o| {
            if (o.items.len == old_joins.len) @memcpy(old_joins, o.items);
        };
        const joins = try self.gpa.alloc(RegionId, old_joins.len);
        defer self.gpa.free(joins);
        for (old_joins, joins) |old, *new| {
            const params = try self.gpa.dupe(TyId, s.tySlice(s.region(old).params));
            defer self.gpa.free(params);
            if (self.demand) |wanted| for (params, 0..) |*t, k| {
                if (wanted.ofJoin(old, k)) |ty| t.* = ty;
            };
            new.* = try self.b.reserveJoin(params);
            try self.regions.put(self.gpa, old, new.*);
        }
        var built_arms: std.ArrayList(RegionId) = .empty;
        defer built_arms.deinit(self.gpa);
        var built_names: std.ArrayList(NameId) = .empty;
        defer built_names.deinit(self.gpa);
        const value = tys.len > 0;
        for (arms, 0..) |old, i| {
            const new = if (old_names) |names| blk: {
                if (!self.b.tagLive(args[0], names[i])) continue;
                try built_names.append(self.gpa, names[i]);
                break :blk try self.b.openTagArm(args[0], names[i]);
            } else try self.b.openArmAt(args[0], aux, @intCast(i));
            try built_arms.append(self.gpa, new);
            try self.regions.put(self.gpa, old, new);
            try self.fill(old);
            try self.finish(old, .region, if (value) select.items else null);
        }
        // The arms in the order of the new scrutinee's type.
        const new_arms = if (old_names != null) try self.b.liveTagArms(args[0], built_names.items, built_arms.items) else try self.gpa.dupe(RegionId, built_arms.items);
        defer self.gpa.free(new_arms);
        const regions = try self.gpa.alloc(RegionId, new_arms.len + joins.len);
        defer self.gpa.free(regions);
        @memcpy(regions[0..new_arms.len], new_arms);
        @memcpy(regions[new_arms.len..], joins);
        const spec: builder_mod.NodeSpec = .{ .op = .switch_, .payload = @intCast(new_arms.len), .args = args, .tys = new_tys, .regions = regions, .aux = aux };
        self.mark();
        // N13r moves this switch into the arms of the value switch it tests an
        // output of only when it is the one reader of that output.
        self.b.sole_reader = if (self.soleReader(n, nd)) args[0] else null;
        defer self.b.sole_reader = null;
        const ref = if (self.opts.raw)
            try self.b.makeRaw(spec)
        else if (value)
            try self.b.make(spec)
        else
            Ref.of(try self.b.exitingSwitch(args[0], new_arms, joins, aux));
        try self.nodes.put(self.gpa, n, .{ .ref = ref, .outs = outs, .width = @intCast(select.items.len) });
    }
};

const testing = std.testing;
const types_mod = @import("types.zig");
const live_mod = @import("live.zig");
const verify = @import("verify.zig");
const eval = @import("eval.zig");

test "inlining a call over a narrower argument drops the arms of the tags the argument cannot hold" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    const narrow = try types.tagUnionTy(&.{ .{ .name = "B", .payload = &.{} }, .{ .name = "C", .payload = &.{} } });
    const wide = try types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{} }, .{ .name = "C", .payload = &.{} } });
    const names = [_]types_mod.NameId{ try types.name("A"), try types.name("B"), try types.name("C") };

    // read(w) = match w { A => 1, B => 2, C => 3 }
    const read = try b.beginRow(&.{wide}, i64_ty);
    var arms: [3]RegionId = undefined;
    for (&arms, names, 1..) |*arm, name, value| {
        arm.* = try b.openTagArm(Ref.rowParam(0), name);
        try b.close(.{ .value = &.{try b.litInt(i64_ty, @intCast(value))} });
    }
    try b.endRow(.{ .value = &.{try b.tagSwitchOn(Ref.rowParam(0), &names, &arms, &.{}, &.{i64_ty})} });
    // main(n) = read(n), where n is only B or C.
    const main = try b.beginRow(&.{narrow}, i64_ty);
    try b.endRow(.{ .value = &.{try b.callRow(read, &.{Ref.rowParam(0)})} });

    var returns = try live_mod.Returns.init(testing.allocator, &store);
    defer returns.deinit(testing.allocator);
    var read_plan = try place.plan(testing.allocator, &store, &returns, read, .simplify);
    defer read_plan.deinit();
    var main_plan = try place.plan(testing.allocator, &store, &returns, main, .simplify);
    defer main_plan.deinit();
    var inline_rows: collections.DenseMapUnmanaged(RowId, *const place.Plan) = .empty;
    defer inline_rows.deinit(testing.allocator);
    try inline_rows.put(testing.allocator, read, &read_plan);
    try run(testing.allocator, &b, &main_plan, .{ .inline_rows = &inline_rows });

    // The call is the switch, and it has the two arms of the argument's type.
    const end = store.region(store.row(main).body).end;
    const sw = store.node(store.refSlice(end.refs)[0].nodeId());
    try testing.expectEqual(ir.Op.switch_, sw.op);
    try testing.expectEqual(@as(u32, 2), sw.payload);
    var report = try verify.verifyAll(testing.allocator, &store, &types);
    defer report.deinit();
    try testing.expect(report.ok());
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var strict = try eval.Evaluator.init(arena.allocator(), &store, &types, .strict);
    try testing.expect((try strict.run(main, &.{.{ .tag = .{ .name = names[1], .payload = &.{} } }})).eql(.{ .int = 2 }));
    try testing.expect((try strict.run(main, &.{.{ .tag = .{ .name = names[2], .payload = &.{} } }})).eql(.{ .int = 3 }));
}
