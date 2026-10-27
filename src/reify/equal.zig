//! Structural equality of values and regions: whether two refs, or two
//! regions, compute one value by one computation.
//!
//! Two regions are equal when they end alike over equal values and their
//! loops that can end the row in `Return` (`live.exits`) are equal one by
//! one in id order, read or not: such a loop decides the row's value.
//!
//! Hash-consing makes two equal computations in one region chain one node,
//! so what is left to compare is computations in regions that do not enclose
//! each other, such as two arms, and the regions that region-owning nodes
//! own. A parameter of a region inside the comparison equals the parameter at
//! the same position of the region it was paired with.
//!
//! A comparison that holds can also give its correspondence: each pair of
//! nodes it found equal on the way. Two rows that share an equal node
//! differently (one node read from two arms against one per arm) are equal,
//! so a node can correspond to more than one node of the other side.

const std = @import("std");
const ir = @import("ir.zig");
const live = @import("live.zig");

const Allocator = std.mem.Allocator;
const Ref = ir.Ref;
const RegionId = ir.RegionId;
const TyId = ir.TyId;

/// Which rows a comparison of two rows takes as one (N8g): a callee
/// against itself, and members of the component being finalized against
/// the members they are paired with.
pub const RowPairing = struct {
    ctx: *const anyopaque,
    same: *const fn (ctx: *const anyopaque, a: ir.RowId, b: ir.RowId) bool,
};

/// A comparison over one store; `pairs` holds the regions paired so far.
pub const Comparison = struct {
    gpa: Allocator,
    store: *const ir.Store,
    pairs: std.ArrayList([2]RegionId) = .empty,
    /// Where set, a `Call` or `Closure` equals one whose row it pairs with.
    rows: ?RowPairing = null,
    /// Where set, every pair of nodes found equal is added to it, the node
    /// of the first side first. It is the correspondence only when the
    /// whole comparison holds: one that fails leaves partial pairs.
    matched: ?*std.ArrayList([2]ir.NodeId) = null,

    pub fn deinit(self: *Comparison) void {
        self.pairs.deinit(self.gpa);
    }

    /// Whether `a` and `b` are one value.
    pub fn values(self: *Comparison, a: Ref, b: Ref) Allocator.Error!bool {
        if (a == b) {
            if (a.kind == .node) try self.match(a.nodeId(), b.nodeId());
            return true;
        }
        if (a.kind != b.kind or a.output != b.output) return false;
        switch (a.kind) {
            .row_param, .input => return false,
            .region_param => {
                for (self.pairs.items) |p| if (p[0] == a.regionId() and p[1] == b.regionId()) return true;
                return false;
            },
            .node => {},
        }
        const store = self.store;
        const x = store.node(a.nodeId());
        const y = store.node(b.nodeId());
        if (x.op != y.op) return false;
        if (x.payload != y.payload) {
            const pairing = self.rows orelse return false;
            switch (x.op) {
                .call, .closure => if (!pairing.same(pairing.ctx, ir.RowId.of(x.payload), ir.RowId.of(y.payload))) return false,
                .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => return false,
            }
        }
        if (!std.mem.eql(TyId, store.tySlice(x.tys), store.tySlice(y.tys))) return false;
        if (!std.mem.eql(u32, store.wordSlice(x.aux), store.wordSlice(y.aux))) return false;
        const xa = store.refSlice(x.args);
        const ya = store.refSlice(y.args);
        if (xa.len != ya.len) return false;
        for (xa, ya) |p, q| if (!try self.values(p, q)) return false;
        const xr = store.regionSlice(x.regions);
        const yr = store.regionSlice(y.regions);
        if (xr.len != yr.len) return false;
        for (xr, yr) |p, q| if (!try self.regions(p, q)) return false;
        try self.match(a.nodeId(), b.nodeId());
        return true;
    }

    fn match(self: *Comparison, x: ir.NodeId, y: ir.NodeId) Allocator.Error!void {
        const out = self.matched orelse return;
        try out.append(self.gpa, .{ x, y });
    }

    /// Whether regions `a` and `b` end alike over equal values.
    pub fn regions(self: *Comparison, a: RegionId, b: RegionId) Allocator.Error!bool {
        const store = self.store;
        const x = store.region(a);
        const y = store.region(b);
        if (compared(x.kind) != compared(y.kind) or x.end.kind != y.end.kind) return false;
        if (!std.mem.eql(TyId, store.tySlice(x.params), store.tySlice(y.params))) return false;
        try self.pairs.append(self.gpa, .{ a, b });
        defer _ = self.pairs.pop();
        switch (x.end.kind) {
            .jump => if (!self.paired(RegionId.of(x.end.target), RegionId.of(y.end.target))) return false,
            .branch => if (!try self.values(Ref.of(ir.NodeId.of(x.end.target)), Ref.of(ir.NodeId.of(y.end.target)))) return false,
            .open, .value, .return_, .continue_, .break_ => {},
        }
        const xe = store.refSlice(x.end.refs);
        const ye = store.refSlice(y.end.refs);
        if (xe.len != ye.len) return false;
        for (xe, ye) |p, q| if (!try self.values(p, q)) return false;
        // A loop that can return decides the row's value whether a value
        // reads it or not, so the two regions' such loops are equal one by
        // one, in the order they run (`live.exits`).
        var xl = live.ExitLoops.of(store, a);
        var yl = live.ExitLoops.of(store, b);
        while (true) {
            const p = xl.next();
            const q = yl.next();
            if (p == null or q == null) return p == null and q == null;
            if (!try self.values(Ref.of(p.?), Ref.of(q.?))) return false;
        }
    }

    // An arm and an operand both deliver a value under a fact, so N7d can
    // pair a switch arm with an `And` or `Or` operand.
    fn compared(k: ir.RegionKind) ir.RegionKind {
        return switch (k) {
            .arm, .operand => .arm,
            .row_body, .join, .loop_body, .lambda_body => k,
        };
    }

    // A jump from inside the comparison names a join that is either the same
    // region or one of a pair of switches being compared.
    fn paired(self: *const Comparison, a: RegionId, b: RegionId) bool {
        if (a == b) return true;
        const store = self.store;
        const oa = store.region(a).owner;
        const ob = store.region(b).owner;
        if (oa == ir.NodeId.none or ob == ir.NodeId.none) return false;
        const sa = store.regionSlice(store.node(oa).regions);
        const sb = store.regionSlice(store.node(ob).regions);
        const ia = std.mem.findScalar(RegionId, sa, a) orelse return false;
        const ib = std.mem.findScalar(RegionId, sb, b) orelse return false;
        if (ia != ib) return false;
        for (self.pairs.items) |p| {
            if (store.region(p[0]).owner == oa and store.region(p[1]).owner == ob) return true;
        }
        return false;
    }
};

const testing = std.testing;
const builder_mod = @import("builder.zig");
const types_mod = @import("types.zig");

test "two arms computing one value by separate nodes are equal; a different value is not" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    const bool_ty = try types.boolTy();
    _ = try b.beginRow(&.{ bool_ty, i64_ty }, i64_ty);
    const c = Ref.rowParam(0);
    const x = Ref.rowParam(1);
    var arms: [3]RegionId = undefined;
    for (&arms, [_]i128{ 3, 3, 2 }) |*arm, k| {
        arm.* = try b.openArm(c, 0);
        const v = try b.call(.i64, .times_wrap, &.{ x, try b.litInt(i64_ty, k) });
        try b.close(.{ .value = &.{v} });
    }
    try b.endRow(.{ .value = &.{x} });
    try testing.expect(store.refSlice(store.region(arms[0]).end.refs)[0] != store.refSlice(store.region(arms[1]).end.refs)[0]);

    var cmp: Comparison = .{ .gpa = testing.allocator, .store = &store };
    defer cmp.deinit();
    try testing.expect(try cmp.regions(arms[0], arms[1]));
    try testing.expect(!try cmp.regions(arms[0], arms[2]));
}

test "an arm with a loop that can return and that nothing reads is not equal to one without it" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    const bool_ty = try types.boolTy();
    _ = try b.beginRow(&.{ bool_ty, i64_ty, i64_ty }, i64_ty);
    const c = Ref.rowParam(0);
    var arms: [3]RegionId = undefined;
    for (&arms, [_]bool{ true, true, false }) |*arm, looped| {
        arm.* = try b.openArm(c, 0);
        if (looped) {
            // for i in 0..<n { if i == k { return i } }
            const zero = try b.litInt(i64_ty, 0);
            const body = try b.openRegion(.loop_body, &.{i64_ty});
            const i = Ref.regionParam(body, 0);
            const t = try b.call(.i64, .is_eq, &.{ i, Ref.rowParam(2) });
            const go = try b.openArm(t, 0);
            try b.close(.{ .continue_ = &.{} });
            const out = try b.openArm(t, 1);
            try b.close(.{ .return_ = i });
            const sw = try b.exitingSwitch(t, &.{ go, out }, &.{}, &.{});
            try b.close(.{ .branch = sw });
            _ = try b.forRange(false, &.{ zero, Ref.rowParam(1) }, body, &.{});
        }
        try b.close(.{ .value = &.{Ref.rowParam(2)} });
    }
    try b.endRow(.{ .value = &.{Ref.rowParam(2)} });

    var cmp: Comparison = .{ .gpa = testing.allocator, .store = &store };
    defer cmp.deinit();
    try testing.expect(try cmp.regions(arms[0], arms[1]));
    try testing.expect(!try cmp.regions(arms[0], arms[2]));
    try testing.expect(!try cmp.regions(arms[2], arms[0]));
    const digest = @import("digest.zig");
    try testing.expectEqual(try digest.ofRegion(testing.allocator, &store, arms[0]), try digest.ofRegion(testing.allocator, &store, arms[1]));
    try testing.expect(try digest.ofRegion(testing.allocator, &store, arms[0]) != try digest.ofRegion(testing.allocator, &store, arms[2]));
}
