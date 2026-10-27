//! What a store's rows reach: the regions and nodes a row's body, read from
//! its end, depends on.
//!
//! A node nothing reads is dead (N6). The walk leaves some behind, such as a
//! binding nothing reads, and so do the exit rules, whose rewritten switch
//! replaces the one it was built from. The verifier, the dump and the
//! emitter read only what is live.
//!
//! A loop whose body can end the row in `Return` is live wherever its region
//! is, read or not: a loop whose slots nothing reads still decides what the
//! row returns. Only a loop, because every other node that owns regions is
//! reached through what it gives: an exiting switch through the `Branch` that
//! ends its region, a value switch, `And` and `Or` through their outputs,
//! and none of those three ever holds a `Return` (the walk builds a
//! construct that can exit as an exiting switch). An exiting switch the exit
//! rules replaced is dead, even though its join still ends in `Return`.

const std = @import("std");
const ir = @import("ir.zig");

const Allocator = std.mem.Allocator;
const Ref = ir.Ref;
const NodeId = ir.NodeId;
const RegionId = ir.RegionId;

/// Per region and per node, whether a row reaches it.
pub const Live = struct {
    regions: []bool,
    nodes: []bool,

    pub fn deinit(self: *Live, gpa: Allocator) void {
        gpa.free(self.regions);
        gpa.free(self.nodes);
    }
};

/// What every row of `store` reaches.
pub fn ofStore(gpa: Allocator, store: *const ir.Store) Allocator.Error!Live {
    var live: Live = .{
        .regions = try gpa.alloc(bool, store.regionCount()),
        .nodes = try gpa.alloc(bool, store.nodeCount()),
    };
    errdefer live.deinit(gpa);
    @memset(live.regions, false);
    @memset(live.nodes, false);
    var pending: std.ArrayList(NodeId) = .empty;
    defer pending.deinit(gpa);
    for (store.rows.items) |r| try reachRegion(gpa, store, &live, &pending, r.body);
    try drain(gpa, store, &live, &pending);

    var returns = try Returns.init(gpa, store);
    defer returns.deinit(gpa);
    const regions = store.nodes.items(.region);
    var changed = true;
    while (changed) {
        changed = false;
        for (regions, store.nodes.items(.op), 0..) |r, op, i| {
            if (!op.isLoop() or live.nodes[i] or !live.regions[r.index()]) continue;
            if (!returns.holds(store, NodeId.of(@intCast(i)))) continue;
            try reachRef(gpa, &live, &pending, Ref.of(NodeId.of(@intCast(i))));
            try drain(gpa, store, &live, &pending);
            changed = true;
        }
    }
    return live;
}

fn drain(gpa: Allocator, store: *const ir.Store, live: *Live, pending: *std.ArrayList(NodeId)) Allocator.Error!void {
    while (pending.pop()) |n| {
        const nd = store.node(n);
        for (store.refSlice(nd.args)) |a| try reachRef(gpa, live, pending, a);
        for (store.regionSlice(nd.regions)) |sub| try reachRegion(gpa, store, live, pending, sub);
    }
}

/// Per node: whether a region it owns, or a node inside one, can end the row
/// in `Return`. Only the regions a node lists count, so a join an exit rule
/// dropped from its switch does not.
pub const Returns = struct {
    const State = enum(u8) { unknown, visiting, no, yes };

    state: []State,
    /// Per region: its nodes, in id order, as `Store.members` gave them at `init`.
    members: [][]NodeId,

    /// Index the regions of `store`. Build it again after adding nodes.
    pub fn init(gpa: Allocator, store: *const ir.Store) Allocator.Error!Returns {
        const state = try gpa.alloc(State, store.nodeCount());
        errdefer gpa.free(state);
        @memset(state, .unknown);
        const members = try gpa.alloc([]NodeId, store.regionCount());
        var filled: usize = 0;
        errdefer {
            for (members[0..filled]) |m| gpa.free(m);
            gpa.free(members);
        }
        for (members, 0..) |*m, i| {
            m.* = try gpa.dupe(NodeId, store.members(RegionId.of(@intCast(i))));
            filled += 1;
        }
        return .{ .state = state, .members = members };
    }

    pub fn deinit(self: *Returns, gpa: Allocator) void {
        for (self.members) |m| gpa.free(m);
        gpa.free(self.members);
        gpa.free(self.state);
    }

    /// Whether node `n` can end the row in `Return` (`canReturn`).
    pub fn holds(self: *Returns, store: *const ir.Store, n: NodeId) bool {
        switch (self.state[n.index()]) {
            .yes => return true,
            .no, .visiting => return false,
            .unknown => {},
        }
        self.state[n.index()] = .visiting;
        const found = nodeReturns(store, n, self);
        self.state[n.index()] = if (found) .yes else .no;
        return found;
    }

    /// Whether node `n` is a loop whose body can end the row in `Return`
    /// (`exits`).
    pub fn exits(self: *Returns, store: *const ir.Store, n: NodeId) bool {
        return store.nodes.items(.op)[n.index()].isLoop() and self.holds(store, n);
    }

    /// Whether region `r` ends in `Return`, or holds a node that can.
    pub fn regionHolds(self: *Returns, store: *const ir.Store, r: RegionId) bool {
        return regionReturns(store, r, self);
    }

    fn membersOf(self: *const Returns, _: *const ir.Store, r: RegionId) []const NodeId {
        return self.members[r.index()];
    }
};

/// Whether node `n` can end the row in `Return`: a region it lists ends in
/// `Return` or holds a node that can. A `Return` in a lambda body ends the
/// lambda, so a `Lambda` never does. Only the regions a node lists count, so
/// a join an exit rule dropped from its switch does not. It reads the store
/// as it is, so it holds at every point of a build; `Returns` caches it for
/// a store that no longer changes.
pub fn canReturn(store: *const ir.Store, n: NodeId) bool {
    return nodeReturns(store, n, Direct{});
}

/// Whether node `n` is a loop whose body can end the row in `Return`. Such a
/// loop stays in the region it was built in, whether a value reads it or
/// not, and two of them in one region keep their order, because the first
/// to return decides the row's value. The numbering (`number.zig`), the
/// structural comparison (`equal.zig`) and the digests (`digest.zig`) read a
/// region's such loops, in id order, through this one definition.
pub fn exits(store: *const ir.Store, n: NodeId) bool {
    return store.nodes.items(.op)[n.index()].isLoop() and canReturn(store, n);
}

/// The loops of region `r` that can end the row in `Return` (`exits`), in id order.
pub const ExitLoops = struct {
    store: *const ir.Store,
    members: []const NodeId,
    at: usize = 0,

    pub fn of(store: *const ir.Store, r: RegionId) ExitLoops {
        return .{ .store = store, .members = store.members(r) };
    }

    pub fn next(self: *ExitLoops) ?NodeId {
        while (self.at < self.members.len) {
            const m = self.members[self.at];
            self.at += 1;
            if (exits(self.store, m)) return m;
        }
        return null;
    }
};

// Reads `canReturn` of a member with no cache.
const Direct = struct {
    fn holds(_: Direct, store: *const ir.Store, n: NodeId) bool {
        return canReturn(store, n);
    }

    fn membersOf(_: Direct, store: *const ir.Store, r: RegionId) []const NodeId {
        return store.members(r);
    }
};

fn nodeReturns(store: *const ir.Store, n: NodeId, cx: anytype) bool {
    if (store.nodes.items(.op)[n.index()] == .lambda) return false;
    for (store.regionSlice(store.node(n).regions)) |r| {
        if (regionReturns(store, r, cx)) return true;
    }
    return false;
}

fn regionReturns(store: *const ir.Store, r: RegionId, cx: anytype) bool {
    if (store.region(r).end.kind == .return_) return true;
    for (cx.membersOf(store, r)) |m| if (cx.holds(store, m)) return true;
    return false;
}

fn reachRegion(gpa: Allocator, store: *const ir.Store, live: *Live, pending: *std.ArrayList(NodeId), r: RegionId) Allocator.Error!void {
    if (live.regions[r.index()]) return;
    live.regions[r.index()] = true;
    const end = store.region(r).end;
    for (store.refSlice(end.refs)) |ref| try reachRef(gpa, live, pending, ref);
    if (end.kind == .branch) try reachRef(gpa, live, pending, Ref.of(NodeId.of(end.target)));
}

fn reachRef(gpa: Allocator, live: *Live, pending: *std.ArrayList(NodeId), ref: Ref) Allocator.Error!void {
    if (ref.kind != .node) return;
    const n = ref.nodeId();
    if (live.nodes[n.index()]) return;
    live.nodes[n.index()] = true;
    try pending.append(gpa, n);
}

const testing = std.testing;

test "a loop nothing reads is live when its body can return, and dead when it cannot" {
    const builder_mod = @import("builder.zig");
    const types_mod = @import("types.zig");
    for ([_]bool{ true, false }) |returns| {
        var store = ir.Store.init(testing.allocator);
        defer store.deinit();
        var types = types_mod.Types.init(testing.allocator);
        defer types.deinit();
        var b = builder_mod.Builder.init(testing.allocator, &store, &types);
        defer b.deinit();
        const i64_ty = try types.intTy(.i64);
        // for i in 0..<n { if i == k { return i } }; 0
        _ = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
        const zero = try b.litInt(i64_ty, 0);
        const body = try b.openRegion(.loop_body, &.{i64_ty});
        const i = Ref.regionParam(body, 0);
        const c = try b.call(.i64, .is_eq, &.{ i, Ref.rowParam(1) });
        const arm0 = try b.openArm(c, 0);
        try b.close(.{ .continue_ = &.{} });
        const arm1 = try b.openArm(c, 1);
        try b.close(if (returns) .{ .return_ = i } else .{ .continue_ = &.{} });
        const sw = try b.exitingSwitch(c, &.{ arm0, arm1 }, &.{}, &.{});
        try b.close(.{ .branch = sw });
        const loop = try b.forRange(false, &.{ zero, Ref.rowParam(0) }, body, &.{});
        try b.endRow(.{ .value = &.{zero} });
        var live = try ofStore(testing.allocator, &store);
        defer live.deinit(testing.allocator);
        try testing.expectEqual(returns, live.nodes[loop.nodeId().index()]);
        try testing.expectEqual(returns, live.nodes[c.nodeId().index()]);
    }
}

test "a loop nothing reads is dead when only a lambda in its body can return" {
    const builder_mod = @import("builder.zig");
    const types_mod = @import("types.zig");
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    const fn_ty = try types.funcTy(&.{i64_ty}, i64_ty);
    // for i in 0..<n { f = |x| { if x == i { return x }; 0 } }; 0
    _ = try b.beginRow(&.{i64_ty}, i64_ty);
    const zero = try b.litInt(i64_ty, 0);
    const body = try b.openRegion(.loop_body, &.{i64_ty});
    const lam = try b.openRegion(.lambda_body, &.{i64_ty});
    const x = Ref.regionParam(lam, 0);
    const c = try b.call(.i64, .is_eq, &.{ x, Ref.regionParam(body, 0) });
    const arm0 = try b.openArm(c, 0);
    try b.close(.{ .return_ = zero });
    const arm1 = try b.openArm(c, 1);
    try b.close(.{ .return_ = x });
    const sw = try b.exitingSwitch(c, &.{ arm0, arm1 }, &.{}, &.{});
    try b.close(.{ .branch = sw });
    _ = try b.make(.{ .op = .lambda, .tys = &.{fn_ty}, .regions = &.{lam} });
    try b.close(.{ .continue_ = &.{} });
    const loop = try b.forRange(false, &.{ zero, Ref.rowParam(0) }, body, &.{});
    try b.endRow(.{ .value = &.{zero} });
    var live = try ofStore(testing.allocator, &store);
    defer live.deinit(testing.allocator);
    try testing.expect(!live.nodes[loop.nodeId().index()]);
}
