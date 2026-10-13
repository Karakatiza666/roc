//! Canonical numbering (N9, normal-form 3.9): every list a translator reads,
//! in an order computed from the graph alone.
//!
//! | List | Order |
//! |---|---|
//! | a row's nodes | post-order of a depth-first walk from the body's end: a node's arguments in their positions, then the regions it owns in their order, then the node |
//! | a region's nodes | the row's order, restricted to the region |
//! | a switch's outputs | the order the walk first reads each |
//! | a switch's joins | the order the walk of its arms first reaches each |
//!
//! A loop whose body can end the row in `Return` is numbered where the walk
//! reaches it, and after every such loop built before it in its region, so
//! the order of two of them, which decides the row's value, is kept. One no
//! value reads is reached after its region's end.
//!
//! The walk reads no source position, so an edit changes the numbering only
//! where it changes the graph. The number stage (`driver.zig`) puts outputs
//! and joins in this order in the store; `inOrder` checks that it did.

const std = @import("std");
const collections = @import("collections");
const ir = @import("ir.zig");
const live_mod = @import("live.zig");

const Allocator = std.mem.Allocator;
const Ref = ir.Ref;
const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const RowId = ir.RowId;

/// One row's numbering.
pub const Numbering = struct {
    /// The row's nodes, in canonical order.
    order: std.ArrayList(NodeId) = .empty,
    /// Per node: its index in `order`.
    index: collections.DenseMapUnmanaged(NodeId, u32) = .empty,
    /// Per switch with more than one output: its outputs, in the order the
    /// walk first reads each.
    outputs: collections.DenseMapUnmanaged(NodeId, std.ArrayList(u32)) = .empty,
    /// Per switch with joins: its joins, in the order the walk first reaches each.
    joins: collections.DenseMapUnmanaged(NodeId, std.ArrayList(RegionId)) = .empty,
    /// The row's parameters, by index, in the order the walk first reads
    /// each (N8f). A parameter the row does not read is not in it.
    params: std.ArrayList(u32) = .empty,

    pub fn deinit(self: *Numbering, gpa: Allocator) void {
        self.order.deinit(gpa);
        self.params.deinit(gpa);
        self.index.deinit(gpa);
        var outs = self.outputs.valueIterator();
        while (outs.next()) |list| list.deinit(gpa);
        self.outputs.deinit(gpa);
        var joins = self.joins.valueIterator();
        while (joins.next()) |list| list.deinit(gpa);
        self.joins.deinit(gpa);
    }

    /// The index of node `n`, which the row reaches.
    pub fn of(self: *const Numbering, n: NodeId) u32 {
        return self.index.get(n).?;
    }

    /// The nodes of region `r`, in canonical order.
    pub fn regionNodes(self: *const Numbering, gpa: Allocator, store: *const ir.Store, r: RegionId) Allocator.Error![]NodeId {
        var out: std.ArrayList(NodeId) = .empty;
        errdefer out.deinit(gpa);
        const regions = store.nodes.items(.region);
        for (self.order.items) |n| if (regions[n.index()] == r) try out.append(gpa, n);
        return out.toOwnedSlice(gpa);
    }
};

/// Number the nodes `row` reaches. `returns` indexes the store's regions.
pub fn ofRow(gpa: Allocator, store: *const ir.Store, returns: *live_mod.Returns, row: RowId) Allocator.Error!Numbering {
    var w: Walk = .{ .gpa = gpa, .store = store, .returns = returns };
    errdefer w.out.deinit(gpa);
    defer w.visited.deinit(gpa);
    try w.region(store.row(row).body);
    return w.out;
}

const Walk = struct {
    gpa: Allocator,
    store: *const ir.Store,
    returns: *live_mod.Returns,
    out: Numbering = .{},
    visited: collections.DenseMapUnmanaged(NodeId, void) = .empty,

    fn region(w: *Walk, r: RegionId) Allocator.Error!void {
        const end = w.store.region(r).end;
        for (w.store.refSlice(end.refs)) |x| try w.ref(x);
        switch (end.kind) {
            .branch => try w.node(NodeId.of(end.target)),
            .jump => {
                const join = RegionId.of(end.target);
                const gop = try w.out.joins.getOrPut(w.gpa, w.store.region(join).owner);
                if (!gop.found_existing) gop.value_ptr.* = .empty;
                if (std.mem.findScalar(RegionId, gop.value_ptr.items, join) == null) try gop.value_ptr.append(w.gpa, join);
            },
            .open, .value, .return_, .continue_, .break_ => {},
        }
        // A loop that can return, which no value read.
        for (w.returns.members[r.index()]) |m| {
            if (w.returns.exits(w.store, m)) try w.node(m);
        }
    }

    fn ref(w: *Walk, r: Ref) Allocator.Error!void {
        if (r.kind == .row_param) {
            if (std.mem.findScalar(u32, w.out.params.items, r.output) == null) try w.out.params.append(w.gpa, r.output);
            return;
        }
        if (r.kind != .node) return;
        const n = r.nodeId();
        if (w.store.nodes.items(.tys)[n.index()].len > 1 and w.store.nodes.items(.op)[n.index()] == .switch_) {
            const gop = try w.out.outputs.getOrPut(w.gpa, n);
            if (!gop.found_existing) gop.value_ptr.* = .empty;
            if (std.mem.findScalar(u32, gop.value_ptr.items, r.output) == null) try gop.value_ptr.append(w.gpa, r.output);
        }
        try w.node(n);
    }

    fn node(w: *Walk, n: NodeId) Allocator.Error!void {
        if ((try w.visited.getOrPut(w.gpa, n)).found_existing) return;
        const nd = w.store.node(n);
        if (w.returns.exits(w.store, n)) {
            // Every loop that can return and was built before this one in its region comes first.
            for (w.returns.members[nd.region.index()]) |m| {
                if (m == n) break;
                if (w.returns.exits(w.store, m)) try w.node(m);
            }
        }
        for (w.store.refSlice(nd.args)) |a| try w.ref(a);
        for (w.store.regionSlice(nd.regions)) |sub| try w.region(sub);
        try w.out.index.put(w.gpa, n, @intCast(w.out.order.items.len));
        try w.out.order.append(w.gpa, n);
    }
};

/// Whether every switch of the row `numbering` numbers has its outputs and
/// joins in the order the walk reads them: the numbering is a fixpoint of
/// the number stage (plan 5.2).
pub fn inOrder(store: *const ir.Store, numbering: *const Numbering) bool {
    var outs = numbering.outputs.constIterator();
    while (outs.next()) |e| {
        const read = e.value_ptr.items;
        if (read.len != store.nodes.items(.tys)[e.key_ptr.index()].len) return false;
        for (read, 0..) |k, i| if (k != i) return false;
    }
    var joins = numbering.joins.constIterator();
    while (joins.next()) |e| {
        const nd = store.node(e.key_ptr.*);
        const stored = store.regionSlice(nd.regions)[nd.payload..];
        if (!std.mem.eql(RegionId, stored, e.value_ptr.items)) return false;
    }
    return true;
}

/// A 128-bit fingerprint of `row` as `numbering` numbers it: its parameter
/// and result types, and per node its op, payload, types, immediates, what
/// it reads by numbering, and the regions it owns, each by its kind,
/// parameter types and end. A region is named by its owner's number and its
/// place among the owner's regions, never by the region a node stands in or
/// by a depth, so two rows that differ only in where their nodes are placed
/// have one fingerprint. The speculatable flags are left out: a flag follows
/// from the rest and from the rows the row calls.
pub fn fingerprint(store: *const ir.Store, returns: *live_mod.Returns, numbering: *const Numbering, row: RowId) u128 {
    var h = std.crypto.hash.sha2.Sha256.init(.{});
    const words = struct {
        fn put(hh: *std.crypto.hash.sha2.Sha256, ws: []const u32) void {
            hh.update(std.mem.sliceAsBytes(ws));
        }
    }.put;
    const info = store.row(row);
    words(&h, &.{ info.params.len, info.result.index() });
    for (store.tySlice(info.params)) |t| words(&h, &.{t.index()});
    const F = struct {
        fn region(hh: *std.crypto.hash.sha2.Sha256, st: *const ir.Store, num: *const Numbering, r: RegionId) void {
            const reg = st.region(r);
            if (reg.owner == NodeId.none) return words(hh, &.{ std.math.maxInt(u32), 0 });
            const at = std.mem.findScalar(RegionId, st.regionSlice(st.node(reg.owner).regions), r).?;
            words(hh, &.{ num.of(reg.owner), @intCast(at) });
        }

        fn ref(hh: *std.crypto.hash.sha2.Sha256, st: *const ir.Store, num: *const Numbering, x: Ref) void {
            switch (x.kind) {
                .row_param => words(hh, &.{ 0, x.output }),
                .node => words(hh, &.{ 1, num.of(x.nodeId()), x.output }),
                .region_param => {
                    words(hh, &.{ 2, x.output });
                    region(hh, st, num, x.regionId());
                },
            }
        }
    };
    for (numbering.order.items) |n| {
        const nd = store.node(n);
        words(&h, &.{ @backingInt(nd.op), nd.payload, nd.tys.len, nd.aux.len, nd.args.len, nd.regions.len });
        for (store.tySlice(nd.tys)) |t| words(&h, &.{t.index()});
        words(&h, store.wordSlice(nd.aux));
        for (store.refSlice(nd.args)) |a| F.ref(&h, store, numbering, a);
        // A loop that can return stays in its region, which it is fingerprinted by.
        if (returns.exits(store, n)) F.region(&h, store, numbering, nd.region);
        for (store.regionSlice(nd.regions)) |sub| {
            const reg = store.region(sub);
            words(&h, &.{ @backingInt(reg.kind), reg.params.len, @backingInt(reg.end.kind), reg.end.refs.len });
            for (store.tySlice(reg.params)) |t| words(&h, &.{t.index()});
            for (store.refSlice(reg.end.refs)) |x| F.ref(&h, store, numbering, x);
            switch (reg.end.kind) {
                .jump => F.region(&h, store, numbering, RegionId.of(reg.end.target)),
                .branch => words(&h, &.{numbering.of(NodeId.of(reg.end.target))}),
                .open, .value, .return_, .continue_, .break_ => {},
            }
        }
    }
    const body = store.region(info.body);
    words(&h, &.{ @backingInt(body.end.kind), body.end.refs.len });
    for (store.refSlice(body.end.refs)) |x| F.ref(&h, store, numbering, x);
    if (body.end.kind == .branch) words(&h, &.{numbering.of(NodeId.of(body.end.target))});
    var out: [32]u8 = undefined;
    h.final(&out);
    return std.mem.readInt(u128, out[0..16], .little);
}

/// The rows a site whose root is `root` reaches through `Call` and `Closure`
/// nodes, root first, each where the walk of a row reached earlier first
/// meets it, depth first, as `code_emit` writes them.
pub fn siteRows(gpa: Allocator, store: *const ir.Store, returns: *live_mod.Returns, root: RowId, out: *ir.RowTable(Numbering)) Allocator.Error!void {
    const gop = try out.getOrPut(gpa, root);
    if (gop.found_existing) return;
    gop.value_ptr.* = .{};
    gop.value_ptr.* = try ofRow(gpa, store, returns, root);
    // The recursion below adds entries, which can move this one.
    const order = try gpa.dupe(NodeId, gop.value_ptr.order.items);
    defer gpa.free(order);
    for (order) |n| {
        const nd = store.node(n);
        switch (nd.op) {
            .call, .closure => try siteRows(gpa, store, returns, RowId.of(nd.payload), out),
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => {},
        }
    }
}

const testing = std.testing;
const builder_mod = @import("builder.zig");
const types_mod = @import("types.zig");

test "a row numbers arguments before their users and a region's nodes before its owner, whatever order they were built in" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    // Two independent nodes, built in either order, then their sum.
    var orders: [2][3]u32 = undefined;
    for (&orders, [_]bool{ false, true }) |*got, swapped| {
        const row = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
        const p0 = Ref.rowParam(0);
        const p1 = Ref.rowParam(1);
        var x: Ref = undefined;
        var y: Ref = undefined;
        if (swapped) {
            y = try b.call(.i64, .times_wrap, &.{ p1, p1 });
            x = try b.call(.i64, .plus_wrap, &.{ p0, p0 });
        } else {
            x = try b.call(.i64, .plus_wrap, &.{ p0, p0 });
            y = try b.call(.i64, .times_wrap, &.{ p1, p1 });
        }
        const sum = try b.call(.i64, .minus, &.{ x, y });
        try b.endRow(.{ .value = &.{sum} });
        var returns = try live_mod.Returns.init(testing.allocator, &store);
        defer returns.deinit(testing.allocator);
        var numbering = try ofRow(testing.allocator, &store, &returns, row);
        defer numbering.deinit(testing.allocator);
        got.* = .{ numbering.of(x.nodeId()), numbering.of(y.nodeId()), numbering.of(sum.nodeId()) };
    }
    try testing.expectEqual([3]u32{ 0, 1, 2 }, orders[0]);
    try testing.expectEqual(orders[0], orders[1]);
}
