//! Placement (N5, normal-form 3.5): the region the rebuild builds each node
//! of a row in, and the nodes it merges.
//!
//! | Step | Stage | Node | Region |
//! |---|---|---|---|
//! | late (N5d) | every simplify round | every node | the latest: the innermost region that encloses every use, at no deeper loop depth than the region the node stood in |
//! | every arm (N5c) | every simplify round | a node every arm of a switch computes from values outside it, and one that owns regions reading nothing from the arms that end alike | one node in the switch's region |
//! | hoist (N5b) | the number stage | a speculatable node | among the regions from its latest up to its earliest, the innermost with the fewest enclosing loops and lambdas |
//!
//! A node's uses and the region it stands in are read from the row as it is,
//! never from where the source wrote it, so a binding written before a
//! branch and read in one arm, and the same binding written in that arm, are
//! placed alike. Sinking a node into a branch evaluates it in fewer cases,
//! which C2 allows for any node; hoisting one out of a loop evaluates it
//! where the body might not, so only a speculatable node is hoisted.
//!
//! A region-owning node moves with its regions, so where a region sits is
//! where its owner is placed: the regions form a new tree, and every region
//! below the one a node stood in is found by walking that tree.
//!
//! What a node reads decides nothing else. Only these hold a row's order:
//!
//! | Fixed | Why |
//! |---|---|
//! | a loop that can end the row in `Return` stays in its region, and two of them in one region keep their order | the first to return decides the row's value |
//! | a switch output nothing reads is dropped from every arm (N6) | an unread output is dead work |

const std = @import("std");
const collections = @import("collections");
const ir = @import("ir.zig");
const live_mod = @import("live.zig");
const digest = @import("digest.zig");
const equal = @import("equal.zig");

const Allocator = std.mem.Allocator;
const Ref = ir.Ref;
const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const RowId = ir.RowId;

/// Which stage the plan is for.
pub const Stage = enum {
    /// A simplify round: late placement and the every-arm merge.
    simplify,
    /// The number stage: late placement, then hoisting.
    number,
};

/// Where one node of the row is built, and what it reads as.
pub const Info = struct {
    /// The region the node is built in. A region is named by its id in the
    /// row as it is; where it sits follows its owner.
    place: RegionId,
    /// The node this one merges into (N5c), or itself.
    alias: NodeId,
    /// For a value switch: per output, whether anything reads it (N6).
    read: []bool = &.{},
    /// Whether N5c placed the node in a switch's region for every arm.
    merged: bool = false,
};

/// How the plan orders nodes that nothing orders: by id, or, for the test of
/// order independence (plan 5.7, L6), at random.
pub const Ties = union(enum) {
    lowest,
    shuffled: std.Random,
};

/// Where a use of a node is: in a node that reads it, or in a region's end.
pub const Site = union(enum) { node: NodeId, region: RegionId };

/// The placement of one row.
pub const Plan = struct {
    arena_impl: std.heap.ArenaAllocator,
    store: *const ir.Store,
    row: RowId,
    ties: Ties = .lowest,
    /// Per node the row reaches.
    info: collections.DenseMapUnmanaged(NodeId, Info) = .empty,
    /// Per region the row reaches: the nodes built in it, in the order the
    /// rebuild builds them. Every node a region-owning node reads from the
    /// region is built before it, and every node that owns no region is built
    /// as soon as what it reads is, so a node of the region comes before any
    /// identical node inside a region nested in it, which then merges into it
    /// (N5a, in dominator pre-order).
    members: collections.DenseMapUnmanaged(RegionId, std.ArrayList(NodeId)) = .empty,
    /// Per node the row reaches: where it is used.
    uses: collections.DenseMapUnmanaged(NodeId, std.ArrayList(Site)) = .empty,
    /// The regions the row reaches, in the order the walk met them.
    regions: std.ArrayList(RegionId) = .empty,
    /// The nodes the row reaches, each after what it depends on.
    order: std.ArrayList(NodeId) = .empty,

    pub fn deinit(self: *Plan) void {
        self.arena_impl.deinit();
    }

    fn arena(self: *Plan) Allocator {
        return self.arena_impl.allocator();
    }

    /// Where node `n` is built, after merges: the node the rebuild builds for it.
    pub fn aliasOf(self: *const Plan, n: NodeId) NodeId {
        return self.info.get(n).?.alias;
    }

    /// Whether output `k` of node `n` is read. Only a value switch drops outputs.
    pub fn outputRead(self: *const Plan, n: NodeId, k: u32) bool {
        const read = self.info.get(n).?.read;
        return read.len == 0 or read[k];
    }

    /// The nodes built in region `r`, in build order.
    pub fn membersOf(self: *const Plan, r: RegionId) []const NodeId {
        const list = self.members.get(r) orelse return &.{};
        return list.items;
    }

    /// The region a region sits in once its owner is placed; `none` for the row body.
    pub fn parentOf(self: *const Plan, r: RegionId) RegionId {
        const owner = self.store.region(r).owner;
        if (owner == NodeId.none) return RegionId.none;
        return self.info.get(owner).?.place;
    }
};

/// Whether the plan moves, merges and drops nothing: every node stays in its
/// region, none merges into another, and every switch output is read. After
/// the simplify stage this holds for every row (plan 5.2): no node is out of
/// its latest region, no node is computed by every arm of a switch, and no
/// switch output goes unread.
pub fn settled(p: *const Plan) bool {
    var it = p.info.constIterator();
    while (it.next()) |e| {
        const n = e.key_ptr.*;
        if (e.value_ptr.alias != n) return false;
        if (e.value_ptr.place != p.store.nodes.items(.region)[n.index()]) return false;
        for (e.value_ptr.read) |r| if (!r) return false;
    }
    return true;
}

/// Whether the plan evaluates no node that is not speculatable in a case
/// where the row as it is does not (C2): every such node is placed in its
/// region or in a region below it, or N5c placed it for every arm.
pub fn noSpeculation(p: *const Plan) bool {
    var it = p.info.constIterator();
    while (it.next()) |e| {
        const n = e.key_ptr.*;
        if (e.value_ptr.merged) continue;
        // A checked op N13u proved fits is speculatable inside the region
        // of its facts and no further out (normal-form 1.1).
        if (p.store.fitFloor(n)) |floor| {
            if (!within(p, e.value_ptr.place, floor)) return false;
            continue;
        }
        if (p.store.nodes.items(.flags)[n.index()].speculatable or e.value_ptr.merged) continue;
        const home = p.store.nodes.items(.region)[n.index()];
        var at = e.value_ptr.place;
        while (at != home) : (at = p.parentOf(at)) {
            if (at == RegionId.none) return false;
        }
    }
    return true;
}

/// Place the nodes of `row`. `returns` indexes the store's regions.
pub fn plan(gpa: Allocator, store: *const ir.Store, returns: *live_mod.Returns, row: RowId, stage: Stage) Allocator.Error!Plan {
    return planWith(gpa, store, returns, row, stage, .lowest);
}

/// `plan`, with ties broken by `ties`.
pub fn planWith(gpa: Allocator, store: *const ir.Store, returns: *live_mod.Returns, row: RowId, stage: Stage, ties: Ties) Allocator.Error!Plan {
    var p: Plan = .{ .arena_impl = std.heap.ArenaAllocator.init(gpa), .store = store, .row = row, .ties = ties };
    errdefer p.deinit();
    var reach: Reach = .{ .p = &p, .returns = returns };
    try reach.run();
    try buildOrder(&p, returns);
    try late(&p, returns);
    try fillMembers(&p);
    switch (stage) {
        .simplify => _ = try everyArm(&p, returns),
        // A node hoisted into the arms of a switch merges with the nodes
        // every arm computes, as in the simplify phase (normal-form 3.5),
        // and a merged node is hoisted again from the switch's region.
        .number => {
            try hoist(&p, returns);
            while (try everyArm(&p, returns)) try hoist(&p, returns);
        },
    }
    try regionOrder(&p, returns);
    return p;
}

// The nodes and regions the row reaches from its body's end, and every use:
// a value switch is reached output by output, so an output nothing reads
// reaches nothing (N6), and a loop that can return is reached wherever its
// region is (`live.zig`).
const Reach = struct {
    p: *Plan,
    returns: *live_mod.Returns,
    tasks: std.ArrayList(Task) = .empty,

    const Task = union(enum) {
        ref: struct { ref: Ref, site: Site },
        region: RegionId,
    };

    fn run(self: *Reach) Allocator.Error!void {
        const a = self.p.arena();
        const store = self.p.store;
        var live_regions: collections.DenseMapUnmanaged(RegionId, void) = .empty;
        try self.tasks.append(a, .{ .region = store.row(self.p.row).body });
        var cursor: usize = 0;
        while (true) {
            while (self.tasks.pop()) |t| switch (t) {
                .region => |r| {
                    if ((try live_regions.getOrPut(a, r)).found_existing) continue;
                    try self.p.regions.append(a, r);
                    const end = store.region(r).end;
                    for (store.refSlice(end.refs)) |ref| try self.tasks.append(a, .{ .ref = .{ .ref = ref, .site = .{ .region = r } } });
                    if (end.kind == .branch) try self.tasks.append(a, .{ .ref = .{ .ref = Ref.of(NodeId.of(end.target)), .site = .{ .region = r } } });
                },
                .ref => |u| try self.use(u.ref, u.site, &live_regions),
            };
            // A loop that can return is live wherever its region is.
            var more = false;
            while (cursor < self.p.regions.items.len) : (cursor += 1) {
                for (self.returns.members[self.p.regions.items[cursor].index()]) |m| {
                    if (self.p.info.contains(m) or !self.returns.exits(store, m)) continue;
                    try self.first(m);
                    more = true;
                }
            }
            if (!more) break;
        }
    }

    fn use(self: *Reach, ref: Ref, site: Site, live_regions: *collections.DenseMapUnmanaged(RegionId, void)) Allocator.Error!void {
        if (ref.kind != .node) return;
        const a = self.p.arena();
        const store = self.p.store;
        const n = ref.nodeId();
        const gop = try self.p.uses.getOrPut(a, n);
        if (!gop.found_existing) gop.value_ptr.* = .empty;
        try gop.value_ptr.append(a, site);
        if (!self.p.info.contains(n)) try self.first(n);
        const info = self.p.info.getPtr(n).?;
        if (info.read.len == 0 or info.read[ref.output]) return;
        // A value switch's output read for the first time: each arm's value for it.
        info.read[ref.output] = true;
        const nd = store.node(n);
        for (store.regionSlice(nd.regions)[0..nd.payload]) |arm| {
            if (!(try live_regions.getOrPut(a, arm)).found_existing) try self.p.regions.append(a, arm);
            const value = store.refSlice(store.region(arm).end.refs)[ref.output];
            try self.tasks.append(a, .{ .ref = .{ .ref = value, .site = .{ .region = arm } } });
        }
    }

    fn first(self: *Reach, n: NodeId) Allocator.Error!void {
        const a = self.p.arena();
        const store = self.p.store;
        const nd = store.node(n);
        const value_switch = nd.op == .switch_ and nd.tys.len > 0;
        try self.p.info.put(a, n, .{
            .place = nd.region,
            .alias = n,
            .read = if (value_switch) blk: {
                const read = try a.alloc(bool, nd.tys.len);
                @memset(read, false);
                break :blk read;
            } else &.{},
        });
        for (store.refSlice(nd.args)) |arg| try self.tasks.append(a, .{ .ref = .{ .ref = arg, .site = .{ .node = n } } });
        if (!value_switch) for (store.regionSlice(nd.regions)) |r| try self.tasks.append(a, .{ .region = r });
    }
};

// Whether node `n` is a loop that can return, which stays where it is.
fn pinned(p: *const Plan, returns: *live_mod.Returns, n: NodeId) bool {
    return returns.exits(p.store, n);
}

// The region a use is in: a reading node's place, or the region whose end reads.
fn siteRegion(p: *const Plan, s: Site) RegionId {
    return switch (s) {
        .node => |m| p.info.get(p.aliasOf(m)).?.place,
        .region => |r| r,
    };
}

// `p.order`: every node after what it reads, and after every node read from
// inside a region it owns that stands outside it, as the row is now. Placing
// a node reads where each such node is placed. Two loops that can return in
// one region keep their order.
fn buildOrder(p: *Plan, returns: *live_mod.Returns) Allocator.Error!void {
    const a = p.arena();
    const store = p.store;
    var deps: collections.DenseMapUnmanaged(NodeId, std.ArrayList(NodeId)) = .empty;
    const addDep = struct {
        fn f(al: Allocator, d: *collections.DenseMapUnmanaged(NodeId, std.ArrayList(NodeId)), after: NodeId, before: NodeId) Allocator.Error!void {
            const gop = try d.getOrPut(al, after);
            if (!gop.found_existing) gop.value_ptr.* = .empty;
            try gop.value_ptr.append(al, before);
        }
    }.f;
    var uses = p.uses.iterator();
    while (uses.next()) |e| {
        const f = e.key_ptr.*;
        const home = store.nodes.items(.region)[f.index()];
        for (e.value_ptr.items) |s| {
            var at = switch (s) {
                .node => |m| blk: {
                    try addDep(a, &deps, m, f);
                    break :blk store.nodes.items(.region)[m.index()];
                },
                .region => |r| r,
            };
            // Every owner between the use and `f`'s region reads `f` from outside.
            while (at != home) {
                const owner = store.region(at).owner;
                if (owner == NodeId.none) break;
                try addDep(a, &deps, owner, f);
                at = store.nodes.items(.region)[owner.index()];
            }
        }
    }
    for (p.regions.items) |r| {
        var prev: ?NodeId = null;
        for (returns.members[r.index()]) |m| {
            if (!p.info.contains(m) or !pinned(p, returns, m)) continue;
            if (prev) |q| try addDep(a, &deps, m, q);
            prev = m;
        }
    }
    // Depth first, in id order, so the order is the same on every run.
    var ids: std.ArrayList(NodeId) = .empty;
    var keys = p.info.keyIterator();
    while (keys.next()) |k| try ids.append(a, k.*);
    switch (p.ties) {
        .lowest => std.mem.sort(NodeId, ids.items, {}, idLess),
        .shuffled => |random| random.shuffle(NodeId, ids.items),
    }
    var state: collections.DenseMapUnmanaged(NodeId, bool) = .empty;
    const Frame = struct { n: NodeId, next: usize };
    var stack: std.ArrayList(Frame) = .empty;
    for (ids.items) |start| {
        if (state.contains(start)) continue;
        try state.put(a, start, false);
        try stack.append(a, .{ .n = start, .next = 0 });
        while (stack.items.len > 0) {
            const top = &stack.items[stack.items.len - 1];
            const list = if (deps.get(top.n)) |l| l.items else &.{};
            if (top.next < list.len) {
                const d = list[top.next];
                top.next += 1;
                if (state.contains(d)) continue;
                try state.put(a, d, false);
                try stack.append(a, .{ .n = d, .next = 0 });
                continue;
            }
            try p.order.append(a, top.n);
            _ = stack.pop();
        }
    }
}

fn idLess(_: void, x: NodeId, y: NodeId) bool {
    return x.index() < y.index();
}

// The number of loop bodies and lambda bodies that enclose region `r`, `r`
// included. Moving a node never changes it: late placement stays at the
// depth, and a hoisted owner's regions are found through the new tree.
fn loopDepth(p: *const Plan, r: RegionId) u32 {
    var depth: u32 = 0;
    var at = r;
    while (at != RegionId.none) : (at = p.parentOf(at)) {
        switch (p.store.region(at).kind) {
            .loop_body, .lambda_body => depth += 1,
            .row_body, .arm, .join, .operand => {},
        }
    }
    return depth;
}

// N5d: users first, each node in the innermost region that encloses its
// uses, at no deeper loop depth than the region it stands in.
fn late(p: *Plan, returns: *live_mod.Returns) Allocator.Error!void {
    const a = p.arena();
    var path: std.ArrayList(RegionId) = .empty;
    var i = p.order.items.len;
    while (i > 0) {
        i -= 1;
        const n = p.order.items[i];
        const home = p.store.nodes.items(.region)[n.index()];
        if (pinned(p, returns, n)) continue;
        const sites = (p.uses.get(n) orelse invariant("a node the row reaches has no use")).items;
        // The path from the first use up to the node's region, then each
        // other use's first region on it.
        path.clearRetainingCapacity();
        var at = siteRegion(p, sites[0]);
        while (true) : (at = p.parentOf(at)) {
            if (at == RegionId.none) invariant("a use is not inside the region of the node it reads");
            try path.append(a, at);
            if (at == home) break;
        }
        var best: usize = 0;
        for (sites[1..]) |s| {
            var up = siteRegion(p, s);
            while (true) : (up = p.parentOf(up)) {
                if (up == RegionId.none) invariant("a use is not inside the region of the node it reads");
                if (std.mem.findScalar(RegionId, path.items, up)) |k| {
                    best = @max(best, k);
                    break;
                }
            }
        }
        var place = path.items[best];
        const limit = loopDepth(p, home);
        while (loopDepth(p, place) > limit) place = p.parentOf(place);
        p.info.getPtr(n).?.place = place;
    }
}

fn fillMembers(p: *Plan) Allocator.Error!void {
    const a = p.arena();
    var lists = p.members.valueIterator();
    while (lists.next()) |l| l.clearRetainingCapacity();
    for (p.order.items) |n| {
        const info = p.info.get(n).?;
        if (info.alias != n) continue;
        const gop = try p.members.getOrPut(a, info.place);
        if (!gop.found_existing) gop.value_ptr.* = .empty;
        try gop.value_ptr.append(a, n);
    }
}

// The structural key of a node for the every-arm merge: its op, payload,
// types, immediates, what its arguments read after merges, and the content
// digest of each region it owns. Null when an argument is built in one of
// `arms`.
fn armKey(p: *const Plan, a: Allocator, n: NodeId, arms: []const RegionId) Allocator.Error!?[]u32 {
    const store = p.store;
    const nd = store.node(n);
    var key: std.ArrayList(u32) = .empty;
    try key.appendSlice(a, &.{ @backingInt(nd.op), nd.payload, nd.tys.len });
    for (store.tySlice(nd.tys)) |t| try key.append(a, t.index());
    try key.append(a, nd.aux.len);
    try key.appendSlice(a, store.wordSlice(nd.aux));
    for (store.refSlice(nd.args)) |arg| {
        var r = arg;
        if (r.kind == .node) {
            const target = p.aliasOf(r.nodeId());
            if (std.mem.findScalar(RegionId, arms, p.info.get(target).?.place) != null) return null;
            r = Ref.node(target, r.output);
        }
        const bits: u64 = @bitCast(r);
        try key.appendSlice(a, &.{ @truncate(bits), @truncate(bits >> 32) });
    }
    for (store.regionSlice(nd.regions)) |r| {
        const d = try digest.ofRegion(a, store, r);
        try key.appendSlice(a, &.{ @truncate(d), @truncate(d >> 32), @truncate(d >> 64), @truncate(d >> 96) });
    }
    return key.items;
}

// Whether a node that owns regions can merge out of `arms`: it delivers a
// value, so it does not end its arm, it is not a loop that can return, and
// its regions read nothing built in the arms.
fn ownerMerges(p: *const Plan, a: Allocator, returns: *live_mod.Returns, n: NodeId, arms: []const RegionId) Allocator.Error!bool {
    const nd = p.store.node(n);
    if (nd.op == .switch_ and nd.tys.len == 0) return false;
    if (pinned(p, returns, n)) return false;
    var reads: collections.DenseMapUnmanaged(RegionId, void) = .empty;
    try readRegions(p, a, n, &reads);
    var it = reads.keyIterator();
    while (it.next()) |r| {
        var at = r.*;
        while (at != RegionId.none) : (at = p.parentOf(at)) {
            if (std.mem.findScalar(RegionId, arms, at) != null) return false;
        }
    }
    return true;
}

// Whether owners `x` and `y` own regions that end alike over equal values,
// which confirms equal digests.
fn sameRegions(p: *const Plan, a: Allocator, x: NodeId, y: NodeId) Allocator.Error!bool {
    var cmp: equal.Comparison = .{ .gpa = a, .store = p.store };
    for (p.store.regionSlice(p.store.node(x).regions), p.store.regionSlice(p.store.node(y).regions)) |rx, ry| {
        if (!try cmp.regions(rx, ry)) return false;
    }
    return true;
}

// N5c: a node that every arm of a switch computes, from values outside the
// switch, is one node in the switch's region. A node that owns regions is
// one when its regions read nothing from the arms and end alike. Inner
// switches first, so a node merged out of an inner switch can merge again
// out of an outer one; each switch again until nothing merges, so a node
// over merged nodes merges too. Says whether a node merged.
fn everyArm(p: *Plan, returns: *live_mod.Returns) Allocator.Error!bool {
    var any = false;
    const a = p.arena();
    const store = p.store;
    var inner_first: std.ArrayList(NodeId) = .empty;
    var seen: collections.DenseMapUnmanaged(NodeId, void) = .empty;
    try hoistOrder(p, a, store.row(p.row).body, &inner_first, &seen);
    for (inner_first.items) |s| {
        const nd = store.node(s);
        if (nd.op != .switch_) continue;
        const arms = store.regionSlice(nd.regions)[0..nd.payload];
        const home = p.info.get(s).?.place;
        while (true) {
            var tables = try a.alloc(std.StringHashMapUnmanaged(NodeId), arms.len);
            for (tables, arms) |*t, arm| {
                t.* = .empty;
                for (p.membersOf(arm)) |m| {
                    if (store.node(m).op.ownsRegions() and !try ownerMerges(p, a, returns, m, arms)) continue;
                    const key = try armKey(p, a, m, arms) orelse continue;
                    const gop = try t.getOrPut(a, std.mem.sliceAsBytes(key));
                    if (!gop.found_existing) gop.value_ptr.* = m;
                }
            }
            var merged = false;
            var keys = tables[0].iterator();
            next_key: while (keys.next()) |e| {
                for (tables[1..]) |t| if (!t.contains(e.key_ptr.*)) continue :next_key;
                const kept = e.value_ptr.*;
                if (store.node(kept).op.ownsRegions()) for (tables[1..]) |t| {
                    if (!try sameRegions(p, a, kept, t.get(e.key_ptr.*).?)) continue :next_key;
                };
                for (tables[1..]) |t| retarget(p, t.get(e.key_ptr.*).?, kept);
                p.info.getPtr(kept).?.place = home;
                p.info.getPtr(kept).?.merged = true;
                merged = true;
            }
            if (!merged) break;
            any = true;
            try fillMembers(p);
        }
    }
    return any;
}

// Merge node `from` into `kept`, and every node already merged into `from`,
// so a node's alias is always the node the rebuild builds for it, never a node
// that merged away after it.
fn retarget(p: *Plan, from: NodeId, kept: NodeId) void {
    var it = p.info.valueIterator();
    while (it.next()) |info| {
        if (info.alias == from) info.alias = kept;
    }
}

// N5b: a speculatable node goes to the innermost region with the fewest
// enclosing loops and lambdas between its latest region and its earliest,
// the innermost region that encloses everything it reads. What it reads is
// placed first, and an owner's regions' nodes before the owner
// (`hoistOrder`), so an owner is hoisted with what its regions read from
// outside them already placed.
fn hoist(p: *Plan, returns: *live_mod.Returns) Allocator.Error!void {
    const a = p.arena();
    var order: std.ArrayList(NodeId) = .empty;
    var seen: collections.DenseMapUnmanaged(NodeId, void) = .empty;
    try hoistOrder(p, a, p.store.row(p.row).body, &order, &seen);
    var reads: collections.DenseMapUnmanaged(RegionId, void) = .empty;
    for (order.items) |n| {
        const nd = p.store.node(n);
        if (!nd.flags.speculatable or pinned(p, returns, n)) continue;
        // A proved op placed outside the region of its facts, by N5c, is
        // not speculatable where it stands.
        if (p.store.fitFloor(n)) |floor| if (!within(p, p.info.get(n).?.place, floor)) continue;
        reads.clearRetainingCapacity();
        try readRegions(p, a, n, &reads);
        const body = p.store.row(p.row).body;
        var at = p.info.get(n).?.place;
        var best = at;
        // Loop depth relative to the latest region.
        var depth: i32 = 0;
        var best_depth: i32 = 0;
        while (at != body and !reads.contains(at)) {
            switch (p.store.region(at).kind) {
                .loop_body, .lambda_body => depth -= 1,
                .row_body, .arm, .join, .operand => {},
            }
            at = p.parentOf(at);
            if (depth < best_depth) {
                best = at;
                best_depth = depth;
            }
        }
        p.info.getPtr(n).?.place = best;
    }
    try fillMembers(p);
}

fn hoistOrder(p: *const Plan, a: Allocator, r: RegionId, order: *std.ArrayList(NodeId), seen: *collections.DenseMapUnmanaged(NodeId, void)) Allocator.Error!void {
    for (p.membersOf(r)) |m| try hoistNode(p, a, m, order, seen);
    for (try endReads(p, a, r)) |ref| if (ref.kind == .node) try hoistNode(p, a, p.aliasOf(ref.nodeId()), order, seen);
}

fn hoistNode(p: *const Plan, a: Allocator, n: NodeId, order: *std.ArrayList(NodeId), seen: *collections.DenseMapUnmanaged(NodeId, void)) Allocator.Error!void {
    if ((try seen.getOrPut(a, n)).found_existing) return;
    const nd = p.store.node(n);
    for (p.store.refSlice(nd.args)) |arg| if (arg.kind == .node) try hoistNode(p, a, p.aliasOf(arg.nodeId()), order, seen);
    for (p.store.regionSlice(nd.regions)) |sub| try hoistOrder(p, a, sub, order, seen);
    try order.append(a, n);
}

// The values region `r`'s end reads that the row reaches: an arm of a value
// switch gives only the outputs something reads.
fn endReads(p: *const Plan, a: Allocator, r: RegionId) Allocator.Error![]const Ref {
    const reg = p.store.region(r);
    const refs = p.store.refSlice(reg.end.refs);
    if (reg.owner == NodeId.none or reg.kind != .arm) return refs;
    const read = p.info.get(reg.owner).?.read;
    if (read.len == 0) return refs;
    var out: std.ArrayList(Ref) = .empty;
    for (refs, read) |ref, keep| if (keep) try out.append(a, ref);
    return out.items;
}

// The regions node `n` reads from: where each node it reads is placed, the
// region of each region parameter, and for a node that owns regions, the
// same for everything its regions read from outside them.
//
// A checked op N13u proved fits reads the region of its facts too, so it is
// hoisted no further out than that region, and neither is a node whose
// regions hold it (normal-form 1.1).
fn readRegions(p: *const Plan, a: Allocator, n: NodeId, out: *collections.DenseMapUnmanaged(RegionId, void)) Allocator.Error!void {
    const store = p.store;
    const nd = store.node(n);
    for (store.refSlice(nd.args)) |arg| try readRegion(p, a, arg, n, out);
    if (store.fitFloor(n)) |floor| try out.put(a, floor, {});
    if (!nd.op.ownsRegions()) return;
    var stack: std.ArrayList(RegionId) = .empty;
    try stack.appendSlice(a, store.regionSlice(nd.regions));
    while (stack.pop()) |r| {
        for (try endReads(p, a, r)) |ref| try readRegion(p, a, ref, n, out);
        for (p.membersOf(r)) |m| {
            for (store.refSlice(store.node(m).args)) |arg| try readRegion(p, a, arg, n, out);
            if (store.fitFloor(m)) |floor| if (!inside(p, floor, n)) try out.put(a, floor, {});
            try stack.appendSlice(a, store.regionSlice(store.node(m).regions));
        }
    }
}

fn readRegion(p: *const Plan, a: Allocator, ref: Ref, owner: NodeId, out: *collections.DenseMapUnmanaged(RegionId, void)) Allocator.Error!void {
    const r = switch (ref.kind) {
        .row_param, .input => return,
        .region_param => ref.regionId(),
        .node => p.info.get(p.aliasOf(ref.nodeId())).?.place,
    };
    // A value read from inside `owner`'s own regions is not read from outside.
    if (inside(p, r, owner)) return;
    try out.put(a, r, {});
}

// Whether region `r` is `outer` or nested in it, in the plan's tree.
fn within(p: *const Plan, r: RegionId, outer: RegionId) bool {
    var at = r;
    while (at != RegionId.none) : (at = p.parentOf(at)) {
        if (at == outer) return true;
    }
    return false;
}

// Whether region `r` is one of `owner`'s regions or nested in one.
fn inside(p: *const Plan, r: RegionId, owner: NodeId) bool {
    var at = r;
    while (at != RegionId.none) : (at = p.parentOf(at)) {
        if (p.store.region(at).owner == owner) return true;
    }
    return false;
}

// Each region's build order: what a node reads from the region first, and a
// node that owns no region before one that does whenever both could be next.
fn regionOrder(p: *Plan, returns: *live_mod.Returns) Allocator.Error!void {
    const a = p.arena();
    const store = p.store;
    // Per node: the nodes of its own region it must follow.
    var deps: collections.DenseMapUnmanaged(NodeId, std.ArrayList(NodeId)) = .empty;
    var uses = p.uses.iterator();
    while (uses.next()) |e| {
        const f = p.aliasOf(e.key_ptr.*);
        const home = p.info.get(f).?.place;
        for (e.value_ptr.items) |s| {
            var at = siteRegion(p, s);
            if (s == .node) {
                const m = p.aliasOf(s.node);
                if (p.info.get(m).?.place == home and m != f) try addEdge(a, &deps, m, f);
            }
            // The owner, placed in `f`'s region, whose regions hold the use.
            while (at != home) {
                const owner = store.region(at).owner;
                if (owner == NodeId.none) invariant("a use is not inside the region of the node it reads");
                const owner_place = p.info.get(owner).?.place;
                if (owner_place == home) {
                    try addEdge(a, &deps, owner, f);
                    break;
                }
                at = owner_place;
            }
        }
    }
    for (p.regions.items) |r| {
        var prev: ?NodeId = null;
        for (returns.members[r.index()]) |m| {
            if (!p.info.contains(m) or !pinned(p, returns, m)) continue;
            if (prev) |q| try addEdge(a, &deps, m, q);
            prev = m;
        }
    }
    var lists = p.members.iterator();
    while (lists.next()) |e| {
        const members = e.value_ptr.items;
        var remaining: collections.DenseMapUnmanaged(NodeId, u32) = .empty;
        var followers: collections.DenseMapUnmanaged(NodeId, std.ArrayList(NodeId)) = .empty;
        for (members) |m| {
            var count: u32 = 0;
            if (deps.get(m)) |ds| for (ds.items) |d| {
                // An edge can repeat; count each.
                count += 1;
                const gop = try followers.getOrPut(a, d);
                if (!gop.found_existing) gop.value_ptr.* = .empty;
                try gop.value_ptr.append(a, m);
            };
            try remaining.put(a, m, count);
        }
        var plain: std.ArrayList(NodeId) = .empty;
        var owners: std.ArrayList(NodeId) = .empty;
        for (members) |m| if (remaining.get(m).? == 0) try readyPush(a, store, m, &plain, &owners);
        var out: std.ArrayList(NodeId) = .empty;
        while (true) {
            const next = popTie(p, &plain) orelse popTie(p, &owners) orelse break;
            try out.append(a, next);
            if (followers.get(next)) |fs| for (fs.items) |m| {
                const c = remaining.getPtr(m).?;
                c.* -= 1;
                if (c.* == 0) try readyPush(a, store, m, &plain, &owners);
            };
        }
        if (out.items.len != members.len) invariant("a region's nodes depend on each other in a cycle");
        e.value_ptr.* = out;
    }
}

fn addEdge(a: Allocator, deps: *collections.DenseMapUnmanaged(NodeId, std.ArrayList(NodeId)), after: NodeId, before: NodeId) Allocator.Error!void {
    const gop = try deps.getOrPut(a, after);
    if (!gop.found_existing) gop.value_ptr.* = .empty;
    try gop.value_ptr.append(a, before);
}

fn readyPush(a: Allocator, store: *const ir.Store, n: NodeId, plain: *std.ArrayList(NodeId), owners: *std.ArrayList(NodeId)) Allocator.Error!void {
    if (store.node(n).op.ownsRegions()) try owners.append(a, n) else try plain.append(a, n);
}

// The next of the ready nodes `list` holds, by the plan's ties.
fn popTie(p: *const Plan, list: *std.ArrayList(NodeId)) ?NodeId {
    switch (p.ties) {
        .lowest => return popLowest(list),
        .shuffled => |random| {
            if (list.items.len == 0) return null;
            return list.swapRemove(random.uintLessThan(usize, list.items.len));
        },
    }
}

// The ready node with the lowest id, so the order is the same on every run.
fn popLowest(list: *std.ArrayList(NodeId)) ?NodeId {
    if (list.items.len == 0) return null;
    var at: usize = 0;
    for (list.items, 0..) |n, i| if (n.index() < list.items[at].index()) {
        at = i;
    };
    return list.swapRemove(at);
}

fn invariant(comptime message: []const u8) noreturn {
    @import("base").invariant("reify placement: " ++ message, .{});
}

const testing = std.testing;
const builder_mod = @import("builder.zig");
const types_mod = @import("types.zig");
const driver = @import("driver.zig");
const dump = @import("dump.zig");

// A row built with every rule off, so that only the driver simplifies it.
const Fixture = struct {
    store: ir.Store,
    types: types_mod.Types,
    b: builder_mod.Builder,

    fn init(self: *Fixture) void {
        self.store = ir.Store.init(testing.allocator);
        self.types = types_mod.Types.init(testing.allocator);
        self.b = builder_mod.Builder.init(testing.allocator, &self.store, &self.types);
        self.b.hooks.rules_off = true;
    }

    fn deinit(self: *Fixture) void {
        self.b.deinit();
        self.types.deinit();
        self.store.deinit();
    }

    // Run the driver with the rules on, and expect `want` as the site dump.
    fn expectSite(self: *Fixture, root: RowId, want: []const u8) (driver.Error || std.Io.Writer.Error || error{TestExpectedEqual})!void {
        self.b.hooks.rules_off = false;
        _ = try driver.run(testing.allocator, &self.b, root, &.{});
        var out: std.Io.Writer.Allocating = .init(testing.allocator);
        defer out.deinit();
        try dump.dumpSite(&out.writer, testing.allocator, &self.store, &self.types, root);
        try testing.expectEqualStrings(want, out.written());
    }
};

// `|n| for i in 0..10 (acc = 0) { for _ in 0..n (acc) { acc + (i + k) } }`.
fn nestedSum(f: *Fixture, k: i128) !RowId {
    const b = &f.b;
    const u8_ty = try f.types.intTy(.u8);
    const row = try b.beginRow(&.{u8_ty}, u8_ty);
    const zero = try b.litInt(u8_ty, 0);
    const outer = try b.openRegion(.loop_body, &.{ u8_ty, u8_ty });
    const i = Ref.regionParam(outer, 0);
    const inner = try b.openRegion(.loop_body, &.{ u8_ty, u8_ty });
    const step = try b.call(.u8, .plus, &.{ i, try b.litInt(u8_ty, k) });
    try b.close(.{ .continue_ = &.{try b.call(.u8, .plus, &.{ Ref.regionParam(inner, 1), step })} });
    const inner_loop = try b.loopOf(.for_range, &.{ zero, Ref.rowParam(0), Ref.regionParam(outer, 1) }, inner, &.{u8_ty});
    try b.close(.{ .continue_ = &.{inner_loop} });
    const outer_loop = try b.loopOf(.for_range, &.{ zero, try b.litInt(u8_ty, 10), zero }, outer, &.{u8_ty});
    try b.endRow(.{ .value = &.{outer_loop} });
    return row;
}

test "N5b with N13u: a checked plus proved to fit leaves the inner loop for the body whose index bounds it, and one not proved stays" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    // `i` is at most 9, so `i + 1` fits and is computed once per outer turn.
    try f.expectSite(try nestedSum(&f, 1),
        \\row r0 (U8) -> U8
        \\  n0 = 0 : U8
        \\  n1 = 10 : U8
        \\  n2 = 1 : U8
        \\  n6 = for_range(n0, n1, n0) : U8 !spec
        \\    body (s6.0: U8, s6.1: U8)
        \\      n3 = Num.U8.plus(s6.0, n2) : U8
        \\      n5 = for_range(n0, p0, s6.1) : U8 !spec
        \\        body (s5.0: U8, s5.1: U8)
        \\          n4 = Num.U8.plus(s5.1, n3) : U8 !spec
        \\          continue n4
        \\      continue n5
        \\  value n6
        \\
    );
    var g: Fixture = undefined;
    g.init();
    defer g.deinit();
    // `i + 250` can overflow, so it stays where the inner body computes it.
    try g.expectSite(try nestedSum(&g, 250),
        \\row r0 (U8) -> U8
        \\  n0 = 0 : U8
        \\  n1 = 10 : U8
        \\  n2 = 250 : U8
        \\  n6 = for_range(n0, n1, n0) : U8 !spec
        \\    body (s6.0: U8, s6.1: U8)
        \\      n5 = for_range(n0, p0, s6.1) : U8 !spec
        \\        body (s5.0: U8, s5.1: U8)
        \\          n3 = Num.U8.plus(s6.0, n2) : U8 !spec
        \\          n4 = Num.U8.plus(s5.1, n3) : U8 !spec
        \\          continue n4
        \\      continue n5
        \\  value n6
        \\
    );
}

test "N5d with N5b: a speculatable node in a branch in a loop lands just outside the loop, after the branch's fact simplified it" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const b = &f.b;
    const i64_ty = try f.types.intTy(.i64);
    const row = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const x = Ref.rowParam(0);
    const zero = try b.litInt(i64_ty, 0);
    const body = try b.openRegion(.loop_body, &.{ i64_ty, i64_ty });
    const c = try b.call(.i64, .is_lt, &.{ x, try b.litInt(i64_ty, 10) });
    const yes = try b.openArm(c, 1);
    // In the arm where `c` holds, `if c x + 1 else x * 3` is `x + 1`.
    const inner_no = try b.openArm(c, 0);
    try b.close(.{ .value = &.{try b.call(.i64, .times_wrap, &.{ x, try b.litInt(i64_ty, 3) })} });
    const inner_yes = try b.openArm(c, 1);
    try b.close(.{ .value = &.{try b.call(.i64, .plus_wrap, &.{ x, try b.litInt(i64_ty, 1) })} });
    const inner = try b.switchOn(c, &.{ inner_no, inner_yes }, &.{}, &.{i64_ty}, &.{});
    try b.close(.{ .value = &.{try b.call(.i64, .times_wrap, &.{ Ref.regionParam(body, 1), inner })} });
    const no = try b.openArm(c, 0);
    try b.close(.{ .value = &.{Ref.regionParam(body, 1)} });
    const next = try b.switchOn(c, &.{ no, yes }, &.{}, &.{i64_ty}, &.{});
    try b.close(.{ .continue_ = &.{next} });
    const loop = try b.loopOf(.for_range, &.{ zero, Ref.rowParam(1), zero }, body, &.{i64_ty});
    try b.endRow(.{ .value = &.{loop} });
    try f.expectSite(row,
        \\row r0 (I64, I64) -> I64
        \\  n0 = 0 : I64
        \\  n1 = 10 : I64
        \\  n2 = Num.I64.is_lt(p0, n1) : Bool
        \\  n3 = 1 : I64
        \\  n4 = Num.I64.plus_wrap(p0, n3) : I64
        \\  n7 = for_range(n0, p1, n0) : I64
        \\    body (s7.0: I64, s7.1: I64)
        \\      n6 = switch n2 : I64
        \\        arm 0
        \\          value s7.1
        \\        arm 1
        \\          n5 = Num.I64.times_wrap(s7.1, n4) : I64
        \\          value n5
        \\      continue n6
        \\  value n7
        \\
    );
}

test "N5d: a match written before an outer match on the same value and read in one arm is decided there" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const b = &f.b;
    const i64_ty = try f.types.intTy(.i64);
    const row = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const x = Ref.rowParam(0);
    const c = try b.call(.i64, .is_lt, &.{ x, Ref.rowParam(1) });
    const y_no = try b.openArm(c, 0);
    try b.close(.{ .value = &.{try b.call(.i64, .times, &.{ x, try b.litInt(i64_ty, 3) })} });
    const y_yes = try b.openArm(c, 1);
    try b.close(.{ .value = &.{try b.call(.i64, .plus, &.{ x, try b.litInt(i64_ty, 1) })} });
    const y = try b.switchOn(c, &.{ y_no, y_yes }, &.{}, &.{i64_ty}, &.{});
    const no = try b.openArm(c, 0);
    try b.close(.{ .value = &.{Ref.rowParam(1)} });
    const yes = try b.openArm(c, 1);
    try b.close(.{ .value = &.{y} });
    const out = try b.switchOn(c, &.{ no, yes }, &.{}, &.{i64_ty}, &.{});
    try b.endRow(.{ .value = &.{out} });
    try f.expectSite(row,
        \\row r0 (I64, I64) -> I64
        \\  n0 = Num.I64.is_lt(p0, p1) : Bool
        \\  n3 = switch n0 : I64 !spec
        \\    arm 0
        \\      value p1
        \\    arm 1
        \\      n1 = 1 : I64
        \\      n2 = Num.I64.plus(p0, n1) : I64 !spec
        \\      value n2
        \\  value n3
        \\
    );
}

test "N5c: a failing node every arm computes from values outside the arms is one node before the switch" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const b = &f.b;
    const i64_ty = try f.types.intTy(.i64);
    const row = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const x = Ref.rowParam(0);
    const c = try b.call(.i64, .is_lt, &.{ x, Ref.rowParam(1) });
    var arms: [2]RegionId = undefined;
    for (&arms, [_]i128{ 2, 3 }, 0..) |*arm, k, key| {
        arm.* = try b.openArm(c, @intCast(key));
        const sum = try b.call(.i64, .plus, &.{ x, Ref.rowParam(1) });
        try b.close(.{ .value = &.{try b.call(.i64, .times, &.{ sum, try b.litInt(i64_ty, k) })} });
    }
    const out = try b.switchOn(c, &arms, &.{}, &.{i64_ty}, &.{});
    try b.endRow(.{ .value = &.{out} });
    try f.expectSite(row,
        \\row r0 (I64, I64) -> I64
        \\  n0 = Num.I64.is_lt(p0, p1) : Bool
        \\  n1 = Num.I64.plus(p0, p1) : I64 !spec
        \\  n6 = switch n0 : I64 !spec
        \\    arm 0
        \\      n2 = 2 : I64
        \\      n3 = Num.I64.times(n1, n2) : I64 !spec
        \\      value n3
        \\    arm 1
        \\      n4 = 3 : I64
        \\      n5 = Num.I64.times(n1, n4) : I64 !spec
        \\      value n5
        \\  value n6
        \\
    );
}

test "N6: a dead failing node and a switch output nothing reads are dropped" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const b = &f.b;
    const i64_ty = try f.types.intTy(.i64);
    const row = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const x = Ref.rowParam(0);
    _ = try b.call(.i64, .div_trunc, &.{ x, Ref.rowParam(1) });
    const c = try b.call(.i64, .is_lt, &.{ x, Ref.rowParam(1) });
    const no = try b.openArm(c, 0);
    try b.close(.{ .value = &.{ x, try b.call(.i64, .times, &.{ x, x }) } });
    const yes = try b.openArm(c, 1);
    try b.close(.{ .value = &.{ Ref.rowParam(1), try b.call(.i64, .plus, &.{ x, x }) } });
    const sw = try b.switchOn(c, &.{ no, yes }, &.{}, &.{ i64_ty, i64_ty }, &.{});
    try b.endRow(.{ .value = &.{ir.Ref.node(sw.nodeId(), 0)} });
    try f.expectSite(row,
        \\row r0 (I64, I64) -> I64
        \\  n0 = Num.I64.is_lt(p0, p1) : Bool
        \\  n1 = switch n0 : I64
        \\    arm 0
        \\      value p0
        \\    arm 1
        \\      value p1
        \\  value n1
        \\
    );
}

// One row, `if a < b then a - b else a` over `a = x + y` and `b = x * x`,
// built in the order `shuffled` picks, with a dead node first when it is set.
fn buildShuffled(f: *Fixture, shuffled: bool) Allocator.Error!RowId {
    const b = &f.b;
    const i64_ty = try f.types.intTy(.i64);
    const row = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const x = Ref.rowParam(0);
    const y = Ref.rowParam(1);
    var sum: Ref = undefined;
    var sq: Ref = undefined;
    if (shuffled) {
        _ = try b.call(.i64, .div_trunc, &.{ y, x });
        sq = try b.call(.i64, .times, &.{ x, x });
        sum = try b.call(.i64, .plus, &.{ x, y });
    } else {
        sum = try b.call(.i64, .plus, &.{ x, y });
        sq = try b.call(.i64, .times, &.{ x, x });
    }
    const c = try b.call(.i64, .is_lt, &.{ sum, sq });
    var arms: [2]RegionId = undefined;
    const keys: [2]u32 = if (shuffled) .{ 1, 0 } else .{ 0, 1 };
    for (keys) |key| {
        arms[key] = try b.openArm(c, key);
        const v = if (key == 1) try b.call(.i64, .minus, &.{ sum, sq }) else sum;
        try b.close(.{ .value = &.{v} });
    }
    const out = try b.switchOn(c, &arms, &.{}, &.{i64_ty}, &.{});
    try b.endRow(.{ .value = &.{out} });
    return row;
}

test "N9: value numbering does not depend on the order the row was built in" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    var g: Fixture = undefined;
    g.init();
    defer g.deinit();
    const want =
        \\row r0 (I64, I64) -> I64
        \\  n0 = Num.I64.plus(p0, p1) : I64 !spec
        \\  n1 = Num.I64.times(p0, p0) : I64 !spec
        \\  n2 = Num.I64.is_lt(n0, n1) : Bool
        \\  n4 = switch n2 : I64 !spec
        \\    arm 0
        \\      value n0
        \\    arm 1
        \\      n3 = Num.I64.minus(n0, n1) : I64 !spec
        \\      value n3
        \\  value n4
        \\
    ;
    try f.expectSite(try buildShuffled(&f, false), want);
    try g.expectSite(try buildShuffled(&g, true), want);
}

test "N5c: a value switch every arm computes from values outside the arms is one switch before them" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const b = &f.b;
    const i64_ty = try f.types.intTy(.i64);
    const row = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const x = Ref.rowParam(0);
    const y = Ref.rowParam(1);
    const c = try b.call(.i64, .is_lt, &.{ x, y });
    var arms: [2]RegionId = undefined;
    for (&arms, [_]i128{ 2, 3 }, 0..) |*arm, k, key| {
        arm.* = try b.openArm(c, @intCast(key));
        // `if y < 5 then x + y else x`, in each arm.
        const d = try b.call(.i64, .is_lt, &.{ y, try b.litInt(i64_ty, 5) });
        const no = try b.openArm(d, 0);
        try b.close(.{ .value = &.{x} });
        const yes = try b.openArm(d, 1);
        try b.close(.{ .value = &.{try b.call(.i64, .plus, &.{ x, y })} });
        const inner = try b.switchOn(d, &.{ no, yes }, &.{}, &.{i64_ty}, &.{});
        try b.close(.{ .value = &.{try b.call(.i64, .times, &.{ inner, try b.litInt(i64_ty, k) })} });
    }
    const out = try b.switchOn(c, &arms, &.{}, &.{i64_ty}, &.{});
    try b.endRow(.{ .value = &.{out} });
    try f.expectSite(row,
        \\row r0 (I64, I64) -> I64
        \\  n0 = Num.I64.is_lt(p0, p1) : Bool
        \\  n1 = 5 : I64
        \\  n2 = Num.I64.is_lt(p1, n1) : Bool
        \\  n4 = switch n2 : I64 !spec
        \\    arm 0
        \\      value p0
        \\    arm 1
        \\      n3 = Num.I64.plus(p0, p1) : I64 !spec
        \\      value n3
        \\  n9 = switch n0 : I64 !spec
        \\    arm 0
        \\      n5 = 2 : I64
        \\      n6 = Num.I64.times(n4, n5) : I64 !spec
        \\      value n6
        \\    arm 1
        \\      n7 = 3 : I64
        \\      n8 = Num.I64.times(n4, n7) : I64 !spec
        \\      value n8
        \\  value n9
        \\
    );
}

test "N5c: a node merged out of an inner switch and then out of an outer one is built once, in the outer switch's region" {
    // `if b < 5 then a else if flag then 1 - a else a - b`: the `a` read of
    // the inner arms merges into the inner switch's region, which then
    // merges with the `a` read of the outer arm. The inner arms' nodes read
    // the node the rebuild builds, never the one that merged away.
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const b = &f.b;
    const i64_ty = try f.types.intTy(.i64);
    const bool_ty = try f.types.boolTy();
    const rec_ty = try f.types.recordTy(&.{ .{ .name = "a", .ty = i64_ty }, .{ .name = "b", .ty = i64_ty }, .{ .name = "flag", .ty = bool_ty } });
    const row = try b.beginRow(&.{rec_ty}, i64_ty);
    const input = Ref.rowParam(0);
    const small = try b.call(.i64, .is_lt, &.{ try b.field(input, 1), try b.litInt(i64_ty, 5) });
    const big_arm = try b.openArm(small, 0);
    const flag = try b.field(input, 2);
    const flag_off = try b.openArm(flag, 0);
    try b.close(.{ .value = &.{try b.call(.i64, .minus, &.{ try b.field(input, 0), try b.field(input, 1) })} });
    const flag_on = try b.openArm(flag, 1);
    try b.close(.{ .value = &.{try b.call(.i64, .minus, &.{ try b.litInt(i64_ty, 1), try b.field(input, 0) })} });
    const inner = try b.switchOn(flag, &.{ flag_off, flag_on }, &.{}, &.{i64_ty}, &.{});
    try b.close(.{ .value = &.{inner} });
    const small_arm = try b.openArm(small, 1);
    try b.close(.{ .value = &.{try b.field(input, 0)} });
    const out = try b.switchOn(small, &.{ big_arm, small_arm }, &.{}, &.{i64_ty}, &.{});
    try b.endRow(.{ .value = &.{out} });
    try f.expectSite(row,
        \\row r0 ({ a : I64, b : I64, flag : Bool }) -> I64
        \\  n0 = field 1(p0) : I64
        \\  n1 = 5 : I64
        \\  n2 = Num.I64.is_lt(n0, n1) : Bool
        \\  n4 = field 0(p0) : I64
        \\  n9 = switch n2 : I64 !spec
        \\    arm 0
        \\      n3 = field 2(p0) : Bool
        \\      n8 = switch n3 : I64 !spec
        \\        arm 0
        \\          n5 = Num.I64.minus(n4, n0) : I64 !spec
        \\          value n5
        \\        arm 1
        \\          n6 = 1 : I64
        \\          n7 = Num.I64.minus(n6, n4) : I64 !spec
        \\          value n7
        \\      value n8
        \\    arm 1
        \\      value n4
        \\  value n9
        \\
    );
}

// One row with every kind of placement: independent nodes, a speculatable
// test in a loop, a binding read in one arm, and a failing node every arm
// computes.
fn buildMixed(f: *Fixture) Allocator.Error!RowId {
    const b = &f.b;
    const i64_ty = try f.types.intTy(.i64);
    const row = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const x = Ref.rowParam(0);
    const y = Ref.rowParam(1);
    const zero = try b.litInt(i64_ty, 0);
    const sum = try b.call(.i64, .plus, &.{ x, y });
    const sq = try b.call(.i64, .times, &.{ x, x });
    const c = try b.call(.i64, .is_lt, &.{ sum, sq });
    const body = try b.openRegion(.loop_body, &.{ i64_ty, i64_ty });
    const big = try b.call(.i64, .is_lt, &.{ y, try b.litInt(i64_ty, 7) });
    const skip = try b.openArm(big, 0);
    try b.close(.{ .value = &.{Ref.regionParam(body, 1)} });
    const add = try b.openArm(big, 1);
    try b.close(.{ .value = &.{try b.call(.i64, .plus_wrap, &.{ Ref.regionParam(body, 1), Ref.regionParam(body, 0) })} });
    const step = try b.switchOn(big, &.{ skip, add }, &.{}, &.{i64_ty}, &.{});
    try b.close(.{ .continue_ = &.{step} });
    const loop = try b.loopOf(.for_range, &.{ zero, y, zero }, body, &.{i64_ty});
    var arms: [2]RegionId = undefined;
    for (&arms, 0..) |*arm, key| {
        arm.* = try b.openArm(c, @intCast(key));
        const shared = try b.call(.i64, .minus, &.{ sq, sum });
        const v = if (key == 0) try b.call(.i64, .times, &.{ shared, loop }) else try b.call(.i64, .plus, &.{ shared, sum });
        try b.close(.{ .value = &.{v} });
    }
    const out = try b.switchOn(c, &arms, &.{}, &.{i64_ty}, &.{});
    try b.endRow(.{ .value = &.{out} });
    return row;
}

fn mixedDump(ties: ?std.Random) (driver.Error || std.Io.Writer.Error)![]u8 {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const row = try buildMixed(&f);
    f.b.hooks.rules_off = false;
    f.b.hooks.shuffle = ties;
    _ = try driver.run(testing.allocator, &f.b, row, &.{});
    var out: std.Io.Writer.Allocating = .init(testing.allocator);
    errdefer out.deinit();
    try dump.dumpSite(&out.writer, testing.allocator, &f.store, &f.types, row);
    return out.toOwnedSlice();
}

test "L6: the site dump does not depend on how placement breaks ties" {
    const want = try mixedDump(null);
    defer testing.allocator.free(want);
    for (0..32) |seed| {
        var prng = std.Random.DefaultPrng.init(seed);
        const got = try mixedDump(prng.random());
        defer testing.allocator.free(got);
        try testing.expectEqualStrings(want, got);
    }
}
