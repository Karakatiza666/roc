//! Scalar replacement (N14; normal-form 3.14, plan 3.4).
//!
//! A record or tuple that crosses a boundary the author controls is split
//! into its components, when the code only reads it by field or index:
//!
//! | Step | Boundary | Done by |
//! |---|---|---|
//! | N14a | a parameter of a non-root row | a `Call` of a finalized row is a `Call` of the row with that parameter split, over the argument's components (`Builder.scalarizedCall`, `driver.zig`) |
//! | N14b | a loop slot | the loop is copied as a rewrite that gives one slot per component (`loops.zig`, `rebuild.zig`) |
//!
//! This file holds what both read: how a value is used (`Usage`), and the
//! shape that says how much of a value splits (`Shape`). A value splits
//! when every use of it is a `Field` or `Index` of it; a component splits
//! again when every use of that read is one too. A use anywhere else, such
//! as an argument of a `Prim`, of a `Closure` or of a `Call`, an operand of
//! a construction, a scrutinee, or a value a region ends with, keeps the
//! value whole, because that something receives the aggregate. A tag union
//! is never split, because its components exist only in one arm, and a
//! record that a value may lack a member of is not split either.

const std = @import("std");
const ir = @import("ir.zig");
const types_mod = @import("types.zig");
const live_mod = @import("live.zig");
const place = @import("place.zig");

const Allocator = std.mem.Allocator;
const Ref = ir.Ref;
const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const RowId = ir.RowId;
const TyId = ir.TyId;
const Types = types_mod.Types;

/// The steps this file owns, for the normal-form fingerprint (`mod.zig`):
/// adding, removing or renaming a rule changes it, and so the version.
pub const steps = [_][]const u8{ "N14a", "N14b" };

/// How much of a value splits.
pub const Shape = union(enum) {
    /// The value stays one value.
    whole,
    /// The value is replaced by its components, one shape each.
    split: []const Shape,

    /// How many layers of aggregate this shape removes.
    pub fn layers(self: Shape) u32 {
        switch (self) {
            .whole => return 0,
            .split => |children| {
                var n: u32 = 1;
                for (children) |c| n += c.layers();
                return n;
            },
        }
    }

    /// How many values replace the value this shape splits.
    pub fn leafCount(self: Shape) u32 {
        switch (self) {
            .whole => return 1,
            .split => |children| {
                var n: u32 = 0;
                for (children) |c| n += c.leafCount();
                return n;
            },
        }
    }

    /// The position among the leaves of the leaf at `path`, or null when
    /// `path` does not end at a leaf.
    pub fn leafAt(self: Shape, path: []const u32) ?u32 {
        switch (self) {
            .whole => return if (path.len == 0) 0 else null,
            .split => |children| {
                if (path.len == 0) return null;
                var before: u32 = 0;
                for (children[0..path[0]]) |c| before += c.leafCount();
                return before + (children[path[0]].leafAt(path[1..]) orelse return null);
            },
        }
    }
};

/// A copy of `shape` in `a`.
pub fn cloneShape(a: Allocator, shape: Shape) Allocator.Error!Shape {
    switch (shape) {
        .whole => return .whole,
        .split => |children| {
            const out = try a.alloc(Shape, children.len);
            for (children, out) |c, *o| o.* = try cloneShape(a, c);
            return .{ .split = out };
        },
    }
}

/// Whether the shapes split anything.
pub fn splits(shapes: []const Shape) bool {
    for (shapes) |s| if (s != .whole) return true;
    return false;
}

/// One value that replaces a split one: the parameter or slot it comes from,
/// and the components to read from it, outermost first.
pub const Leaf = struct {
    index: u32,
    path: []const u32,
};

/// The leaves of `shapes`, one value per index and then depth first. `a`
/// owns the paths.
pub fn leavesOf(a: Allocator, shapes: []const Shape) Allocator.Error![]Leaf {
    var out: std.ArrayList(Leaf) = .empty;
    var path: std.ArrayList(u32) = .empty;
    for (shapes, 0..) |s, i| try addLeaves(a, &out, &path, @intCast(i), s);
    return out.toOwnedSlice(a);
}

fn addLeaves(a: Allocator, out: *std.ArrayList(Leaf), path: *std.ArrayList(u32), index: u32, shape: Shape) Allocator.Error!void {
    switch (shape) {
        .whole => try out.append(a, .{ .index = index, .path = try a.dupe(u32, path.items) }),
        .split => |children| for (children, 0..) |c, i| {
            try path.append(a, @intCast(i));
            try addLeaves(a, out, path, index, c);
            _ = path.pop();
        },
    }
}

/// The type of the value at `path` in a value of `ty`.
pub fn tyAt(types: *const Types, ty: TyId, path: []const u32) TyId {
    var at = ty;
    for (path) |i| at = types.componentTy(at, i);
    return at;
}

/// What a use is keyed by: a node's output, a row parameter, or a region
/// parameter.
pub const Key = u64;

pub fn nodeKey(n: NodeId, output: u32) Key {
    return (@as(u64, n.index()) << 30) | output;
}

pub fn rowParamKey(row: RowId, k: u32) Key {
    return (@as(u64, 1) << 62) | (@as(u64, row.index()) << 30) | k;
}

pub fn regionParamKey(r: RegionId, k: u32) Key {
    return (@as(u64, 2) << 62) | (@as(u64, r.index()) << 30) | k;
}

fn keyOf(ref: Ref, row: RowId) ?Key {
    return switch (ref.kind) {
        .node => nodeKey(ref.nodeId(), ref.output),
        .row_param => rowParamKey(row, ref.output),
        .region_param => regionParamKey(ref.regionId(), ref.output),
        .input => null,
    };
}

/// A read of a value by field or index: the node, and the component it reads.
pub const Proj = struct { node: NodeId, comp: u32 };

/// A value that a region ends with: the region, and the position among the
/// values it ends with.
pub const EndUse = struct { region: RegionId, pos: u32 };

/// Which of the ends of regions a value may be used in and still split.
pub const Tolerate = struct {
    ctx: *const anyopaque,
    ok: *const fn (ctx: *const anyopaque, use: EndUse) bool,
};

/// How the nodes and region ends of a row, or of a store, use values.
pub const Usage = struct {
    a: Allocator,
    /// Values read by a node in any way but a projection.
    arg_whole: std.AutoHashMapUnmanaged(Key, void) = .empty,
    /// Per value: the regions that end with it.
    end_reads: std.AutoHashMapUnmanaged(Key, std.ArrayList(EndUse)) = .empty,
    /// Per value: its reads by field or index.
    reads: std.AutoHashMapUnmanaged(Key, std.ArrayList(Proj)) = .empty,

    /// The uses in the row of `p`, over the nodes and regions it reaches.
    /// `a` owns everything, and is not freed here.
    pub fn ofPlan(a: Allocator, p: *const place.Plan) Allocator.Error!Usage {
        var u: Usage = .{ .a = a };
        var it = p.info.constKeyIterator();
        while (it.next()) |n| try u.noteNode(p.store, p.row, n);
        for (p.regions.items) |r| try u.noteEnd(p.store, p.row, r);
        return u;
    }

    /// The uses in every node and region `live` marks.
    pub fn ofStore(a: Allocator, store: *const ir.Store, live: live_mod.Live) Allocator.Error!Usage {
        var u: Usage = .{ .a = a };
        const regions = store.nodes.items(.region);
        for (live.nodes, 0..) |l, i| {
            if (!l) continue;
            try u.noteNode(store, store.region(regions[i]).row, NodeId.of(@intCast(i)));
        }
        for (live.regions, 0..) |l, i| {
            if (!l) continue;
            const r = RegionId.of(@intCast(i));
            try u.noteEnd(store, store.region(r).row, r);
        }
        return u;
    }

    fn noteNode(u: *Usage, store: *const ir.Store, row: RowId, n: NodeId) Allocator.Error!void {
        const nd = store.node(n);
        const args = store.refSlice(nd.args);
        const projection = (nd.op == .field or nd.op == .index) and args.len == 1;
        for (args, 0..) |ref, i| {
            const key = keyOf(ref, row) orelse continue;
            if (projection and i == 0) {
                const gop = try u.reads.getOrPut(u.a, key);
                if (!gop.found_existing) gop.value_ptr.* = .empty;
                try gop.value_ptr.append(u.a, .{ .node = n, .comp = nd.payload });
            } else try u.arg_whole.put(u.a, key, {});
        }
    }

    fn noteEnd(u: *Usage, store: *const ir.Store, row: RowId, r: RegionId) Allocator.Error!void {
        const end = store.region(r).end;
        for (store.refSlice(end.refs), 0..) |ref, pos| {
            const key = keyOf(ref, row) orelse continue;
            const gop = try u.end_reads.getOrPut(u.a, key);
            if (!gop.found_existing) gop.value_ptr.* = .empty;
            try gop.value_ptr.append(u.a, .{ .region = r, .pos = @intCast(pos) });
        }
    }

    /// How much of the value `key` of type `ty` splits. A value splits when
    /// something reads it and nothing else uses it, but for the region ends
    /// `tolerate` accepts; a component splits when the same holds for all
    /// its reads together. Memory comes from `a`.
    pub fn shapeOf(u: *const Usage, types: *const Types, key: Key, ty: TyId, tolerate: ?Tolerate) Allocator.Error!Shape {
        if (!types.isSplittable(ty)) return .whole;
        if (u.arg_whole.contains(key)) return .whole;
        if (u.end_reads.get(key)) |ends| for (ends.items) |e| {
            const t = tolerate orelse return .whole;
            if (!t.ok(t.ctx, e)) return .whole;
        };
        const reads = u.reads.get(key) orelse return .whole;
        const children = try u.a.alloc(Shape, types.componentCount(ty));
        for (children, 0..) |*child, i| {
            const component_ty = types.componentTy(ty, @intCast(i));
            var acc: ?Shape = null;
            for (reads.items) |r| {
                if (r.comp != i) continue;
                const s = try u.shapeOf(types, nodeKey(r.node, 0), component_ty, null);
                acc = if (acc) |prev| try meet(u.a, prev, s) else s;
            }
            child.* = acc orelse .whole;
        }
        return .{ .split = children };
    }

    /// The reads of the value `key`.
    pub fn readsOf(u: *const Usage, key: Key) []const Proj {
        const list = u.reads.get(key) orelse return &.{};
        return list.items;
    }
};

// What two shapes both split.
fn meet(a: Allocator, x: Shape, y: Shape) Allocator.Error!Shape {
    switch (x) {
        .whole => return .whole,
        .split => |xs| switch (y) {
            .whole => return .whole,
            .split => |ys| {
                const out = try a.alloc(Shape, xs.len);
                for (xs, ys, out) |p, q, *o| o.* = try meet(a, p, q);
                return .{ .split = out };
            },
        },
    }
}

/// Whether calls of `row` are split by N14a: it is finalized, it is not the
/// root or a row that keeps a closure's calling convention, and nothing
/// merged it away.
pub fn rowEligible(store: *const ir.Store, row: RowId) bool {
    const r = store.row(row);
    return r.digest != null and r.merged_into == null and !r.fixed_params;
}

/// The shape of each parameter of `row`, which is eligible.
pub fn rowShapes(u: *const Usage, store: *const ir.Store, types: *const Types, row: RowId) Allocator.Error![]Shape {
    const params = store.tySlice(store.row(row).params);
    const out = try u.a.alloc(Shape, params.len);
    for (params, out, 0..) |ty, *o, k| o.* = try u.shapeOf(types, rowParamKey(row, @intCast(k)), ty, null);
    return out;
}

/// The layers of aggregate that calls of rows hold, which N14a removes, per
/// row, over one store's liveness.
pub const Cache = struct {
    store: *const ir.Store,
    types: *const Types,
    live: live_mod.Live,
    arena: std.heap.ArenaAllocator,
    usage: ?Usage = null,
    layers: std.AutoHashMapUnmanaged(RowId, u32) = .empty,

    pub fn init(gpa: Allocator, store: *const ir.Store, types: *const Types, live: live_mod.Live) Cache {
        return .{ .store = store, .types = types, .live = live, .arena = std.heap.ArenaAllocator.init(gpa) };
    }

    pub fn deinit(self: *Cache) void {
        self.arena.deinit();
    }

    /// How many layers of aggregate N14a removes from a call of `row`.
    pub fn layersOf(self: *Cache, row: RowId) Allocator.Error!u32 {
        if (self.layers.get(row)) |known| return known;
        const a = self.arena.allocator();
        var total: u32 = 0;
        if (rowEligible(self.store, row)) {
            if (self.usage == null) self.usage = try Usage.ofStore(a, self.store, self.live);
            for (try rowShapes(&self.usage.?, self.store, self.types, row)) |s| total += s.layers();
        }
        try self.layers.put(a, row, total);
        return total;
    }
};

/// The shapes of the parameters of `row` when N14a splits any of them, in
/// `a`; null when it splits none. `gpa` serves what is needed meanwhile.
pub fn analyzeRow(a: Allocator, gpa: Allocator, store: *const ir.Store, types: *const Types, row: RowId) Allocator.Error!?[]const Shape {
    if (!rowEligible(store, row)) return null;
    var live = try live_mod.ofStore(gpa, store);
    defer live.deinit(gpa);
    var scratch = std.heap.ArenaAllocator.init(gpa);
    defer scratch.deinit();
    const usage = try Usage.ofStore(scratch.allocator(), store, live);
    const shapes = try rowShapes(&usage, store, types, row);
    if (!splits(shapes)) return null;
    const out = try a.alloc(Shape, shapes.len);
    for (shapes, out) |s, *o| o.* = try cloneShape(a, s);
    return out;
}

/// L2: whether no call of a row the site reaches is one N14a splits. A
/// fixpoint of the simplify rounds leaves none.
pub fn noneRewritable(gpa: Allocator, store: *const ir.Store, types: *const Types, reached: []const NodeId) Allocator.Error!bool {
    var live = try live_mod.ofStore(gpa, store);
    defer live.deinit(gpa);
    var cache = Cache.init(gpa, store, types, live);
    defer cache.deinit();
    for (reached) |n| {
        const nd = store.node(n);
        if (nd.op != .call) continue;
        if (try cache.layersOf(RowId.of(nd.payload)) != 0) return false;
    }
    return true;
}

const testing = std.testing;

test "a shape counts its layers and finds its leaves" {
    const leaf: Shape = .whole;
    const inner: Shape = .{ .split = &.{ leaf, leaf } };
    const outer: Shape = .{ .split = &.{ inner, leaf } };
    try testing.expectEqual(@as(u32, 2), outer.layers());
    try testing.expectEqual(@as(u32, 3), outer.leafCount());
    try testing.expectEqual(@as(?u32, 0), outer.leafAt(&.{ 0, 0 }));
    try testing.expectEqual(@as(?u32, 1), outer.leafAt(&.{ 0, 1 }));
    try testing.expectEqual(@as(?u32, 2), outer.leafAt(&.{1}));
    try testing.expectEqual(@as(?u32, null), outer.leafAt(&.{0}));
}

const builder_mod = @import("builder.zig");
const driver = @import("driver.zig");
const dump = @import("dump.zig");
const eval = @import("eval.zig");
const verify = @import("verify.zig");
const Builder = builder_mod.Builder;

const Fixture = struct {
    store: ir.Store,
    types: Types,
    b: Builder,

    fn init(self: *Fixture) void {
        self.store = ir.Store.init(testing.allocator);
        self.types = Types.init(testing.allocator);
        self.b = Builder.init(testing.allocator, &self.store, &self.types);
    }

    fn deinit(self: *Fixture) void {
        self.b.deinit();
        self.types.deinit();
        self.store.deinit();
    }

    // Run the driver over the site of `root` and dump it.
    fn site(self: *Fixture, root: RowId) ![]u8 {
        _ = try driver.runTo(testing.allocator, &self.b, root, &.{}, .finalized);
        var report = try verify.verifyAll(testing.allocator, &self.store, &self.types);
        defer report.deinit();
        try testing.expect(report.ok());
        var out: std.Io.Writer.Allocating = .init(testing.allocator);
        errdefer out.deinit();
        try dump.dumpSite(&out.writer, testing.allocator, &self.store, &self.types, root);
        return out.toOwnedSlice();
    }

    fn expectSite(self: *Fixture, root: RowId, want: []const u8) !void {
        const got = try self.site(root);
        defer testing.allocator.free(got);
        try testing.expectEqualStrings(want, got);
    }

    fn pairTy(self: *Fixture) !TyId {
        const i64_ty = try self.types.intTy(.i64);
        return self.types.recordTy(&.{ .{ .name = "a", .ty = i64_ty }, .{ .name = "b", .ty = i64_ty } });
    }

    // `|r| r.a * 2 + r.b * 3`, which takes the pair as one record.
    fn recordHelper(self: *Fixture) !RowId {
        const i64_ty = try self.types.intTy(.i64);
        const row = try self.b.beginRow(&.{try self.pairTy()}, i64_ty);
        const a = try self.b.field(Ref.rowParam(0), 0);
        const b = try self.b.field(Ref.rowParam(0), 1);
        const twice = try self.b.call(.i64, .times_wrap, &.{ a, try self.b.litInt(i64_ty, 2) });
        const thrice = try self.b.call(.i64, .times_wrap, &.{ b, try self.b.litInt(i64_ty, 3) });
        try self.b.endRow(.{ .value = &.{try self.b.call(.i64, .plus_wrap, &.{ twice, thrice })} });
        return row;
    }

    // `|t| t.0 * 2 + t.1 * 3`, which takes the pair as one tuple.
    fn tupleHelper(self: *Fixture) !RowId {
        const i64_ty = try self.types.intTy(.i64);
        const row = try self.b.beginRow(&.{try self.types.tupleTy(&.{ i64_ty, i64_ty })}, i64_ty);
        const a = try self.b.index(Ref.rowParam(0), 0);
        const b = try self.b.index(Ref.rowParam(0), 1);
        const twice = try self.b.call(.i64, .times_wrap, &.{ a, try self.b.litInt(i64_ty, 2) });
        const thrice = try self.b.call(.i64, .times_wrap, &.{ b, try self.b.litInt(i64_ty, 3) });
        try self.b.endRow(.{ .value = &.{try self.b.call(.i64, .plus_wrap, &.{ twice, thrice })} });
        return row;
    }

    // `|a, b| a * 2 + b * 3`.
    fn pairHelper(self: *Fixture) !RowId {
        const i64_ty = try self.types.intTy(.i64);
        const row = try self.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
        const twice = try self.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), try self.b.litInt(i64_ty, 2) });
        const thrice = try self.b.call(.i64, .times_wrap, &.{ Ref.rowParam(1), try self.b.litInt(i64_ty, 3) });
        try self.b.endRow(.{ .value = &.{try self.b.call(.i64, .plus_wrap, &.{ twice, thrice })} });
        return row;
    }
};

const two_calls_dump =
    \\row r0 (I64, I64) -> I64
    \\  n0 = call r1(p0, p1) : I64
    \\  n1 = call r1(p1, p0) : I64
    \\  n2 = Num.I64.plus_wrap(n0, n1) : I64
    \\  value n2
    \\row r1 (I64, I64) -> I64
    \\  n0 = 2 : I64
    \\  n1 = Num.I64.times_wrap(p0, n0) : I64
    \\  n2 = 3 : I64
    \\  n3 = Num.I64.times_wrap(p1, n2) : I64
    \\  n4 = Num.I64.plus_wrap(n1, n3) : I64
    \\  value n4
    \\
;

test "N14a: a record parameter that is only read by field is one parameter per component" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const pair = try f.pairTy();
    const helper = try f.recordHelper();
    // `|x, y| helper({ a: x, b: y }) + helper({ a: y, b: x })`
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const first = try f.b.callRow(helper, &.{try f.b.record(pair, &.{ Ref.rowParam(0), Ref.rowParam(1) })});
    const second = try f.b.callRow(helper, &.{try f.b.record(pair, &.{ Ref.rowParam(1), Ref.rowParam(0) })});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ first, second })} });
    try f.expectSite(root, two_calls_dump);
}

test "N14a: f(a, b), f({ a, b }) and f((a, b)) are one row" {
    // `|x, y| f(x, y) + f(y, x)`, once with each helper, each in a store of its own.
    for (0..3) |kind| {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        const i64_ty = try f.types.intTy(.i64);
        const pair = try f.pairTy();
        const tuple = try f.types.tupleTy(&.{ i64_ty, i64_ty });
        const plain = try f.pairHelper();
        const record = try f.recordHelper();
        const tupled = try f.tupleHelper();
        const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
        const x = Ref.rowParam(0);
        const y = Ref.rowParam(1);
        const calls = switch (kind) {
            0 => [2]Ref{ try f.b.callRow(plain, &.{ x, y }), try f.b.callRow(plain, &.{ y, x }) },
            1 => [2]Ref{ try f.b.callRow(record, &.{try f.b.record(pair, &.{ x, y })}), try f.b.callRow(record, &.{try f.b.record(pair, &.{ y, x })}) },
            else => [2]Ref{ try f.b.callRow(tupled, &.{try f.b.tuple(tuple, &.{ x, y })}), try f.b.callRow(tupled, &.{try f.b.tuple(tuple, &.{ y, x })}) },
        };
        try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ calls[0], calls[1] })} });
        try f.expectSite(root, two_calls_dump);
    }
}

test "N14a: a call that builds no record splits its argument by reading it" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const pair = try f.pairTy();
    const helper = try f.recordHelper();
    // `|r, s| helper(r) + helper(s)`
    const root = try f.b.beginRow(&.{ pair, pair }, i64_ty);
    const first = try f.b.callRow(helper, &.{Ref.rowParam(0)});
    const second = try f.b.callRow(helper, &.{Ref.rowParam(1)});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ first, second })} });
    try f.expectSite(root,
        \\row r0 ({ a : I64, b : I64 }, { a : I64, b : I64 }) -> I64
        \\  n0 = field 0(p0) : I64
        \\  n1 = field 1(p0) : I64
        \\  n2 = call r1(n0, n1) : I64
        \\  n3 = field 0(p1) : I64
        \\  n4 = field 1(p1) : I64
        \\  n5 = call r1(n3, n4) : I64
        \\  n6 = Num.I64.plus_wrap(n2, n5) : I64
        \\  value n6
        \\row r1 (I64, I64) -> I64
        \\  n0 = 2 : I64
        \\  n1 = Num.I64.times_wrap(p0, n0) : I64
        \\  n2 = 3 : I64
        \\  n3 = Num.I64.times_wrap(p1, n2) : I64
        \\  n4 = Num.I64.plus_wrap(n1, n3) : I64
        \\  value n4
        \\
    );
}

test "N14a: a record parameter the row also returns, or builds into a value, stays whole" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const pair = try f.pairTy();
    const both = try f.types.tupleTy(&.{ i64_ty, pair });
    // `|r| r`, and `|r| (r.a, r)`, which reads the record by a field and also builds it in.
    const whole = try f.b.beginRow(&.{pair}, pair);
    try f.b.endRow(.{ .value = &.{Ref.rowParam(0)} });
    const kept = try f.b.beginRow(&.{pair}, both);
    try f.b.endRow(.{ .value = &.{try f.b.tuple(both, &.{ try f.b.field(Ref.rowParam(0), 0), Ref.rowParam(0) })} });
    // `|x, y| whole({ x, y }).a + kept({ y, x }).0`
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const returned = try f.b.field(try f.b.callRow(whole, &.{try f.b.record(pair, &.{ Ref.rowParam(0), Ref.rowParam(1) })}), 0);
    const built = try f.b.index(try f.b.callRow(kept, &.{try f.b.record(pair, &.{ Ref.rowParam(1), Ref.rowParam(0) })}), 0);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ returned, built })} });
    const got = try f.site(root);
    defer testing.allocator.free(got);
    // Both helpers keep the record as their one parameter.
    try testing.expectEqual(@as(usize, 2), std.mem.count(u8, got, "({ a : I64, b : I64 }) ->"));
}

test "N14a: the root keeps the parameters of the type it is read at" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const pair = try f.pairTy();
    const root = try f.b.beginRow(&.{pair}, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.field(Ref.rowParam(0), 0)} });
    try f.expectSite(root,
        \\row r0 ({ a : I64, b : I64 }) -> I64
        \\  n0 = field 0(p0) : I64
        \\  value n0
        \\
    );
}

test "N14a: a component that is a record splits again, and a component nothing reads is dropped" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const pair = try f.pairTy();
    const outer = try f.types.recordTy(&.{ .{ .name = "inner", .ty = pair }, .{ .name = "k", .ty = i64_ty }, .{ .name = "unused", .ty = i64_ty } });
    // `|r| r.inner.b + r.k`, which reads three of the four leaves... two of them.
    const helper = try f.b.beginRow(&.{outer}, i64_ty);
    const inner = try f.b.field(Ref.rowParam(0), 0);
    const b = try f.b.field(inner, 1);
    const k = try f.b.field(Ref.rowParam(0), 1);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ b, k })} });
    // `|x, y| helper(..) + helper(..)`
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const zero = try f.b.litInt(i64_ty, 0);
    var calls: [2]Ref = undefined;
    for (&calls, [2][2]Ref{ .{ Ref.rowParam(0), Ref.rowParam(1) }, .{ Ref.rowParam(1), Ref.rowParam(0) } }) |*c, xy| {
        const made_inner = try f.b.record(pair, &.{ xy[0], xy[1] });
        c.* = try f.b.callRow(helper, &.{try f.b.record(outer, &.{ made_inner, xy[1], zero })});
    }
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ calls[0], calls[1] })} });
    try f.expectSite(root,
        \\row r0 (I64, I64) -> I64
        \\  n0 = call r1(p1, p1) : I64
        \\  n1 = call r1(p0, p0) : I64
        \\  n2 = Num.I64.plus_wrap(n0, n1) : I64
        \\  value n2
        \\row r1 (I64, I64) -> I64
        \\  n0 = Num.I64.plus_wrap(p0, p1) : I64
        \\  value n0
        \\
    );
}

test "N14a: the knockout stops it, and the check that none is left says so" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const pair = try f.pairTy();
    const helper = try f.recordHelper();
    f.b.hooks.algorithms_off.insert(.scalar_call);
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const first = try f.b.callRow(helper, &.{try f.b.record(pair, &.{ Ref.rowParam(0), Ref.rowParam(1) })});
    const second = try f.b.callRow(helper, &.{try f.b.record(pair, &.{ Ref.rowParam(1), Ref.rowParam(0) })});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ first, second })} });
    // The driver's L2 check finds the call of a row it should have split.
    try testing.expectError(error.InvariantBroken, driver.runTo(testing.allocator, &f.b, root, &.{}, .finalized));
    try testing.expect(f.store.rows.items[helper.index()].params.len == 1);
}

test "N14a: a tag union, and a record a value may lack a member of, are not split" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const union_ty = try f.types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{i64_ty} }, .{ .name = "B", .payload = &.{} } });
    const loose = try f.types.recordTy(&.{ .{ .name = "a", .ty = i64_ty }, .{ .name = "b", .ty = i64_ty, .optional = true } });
    const empty = try f.types.recordTy(&.{});
    try testing.expect(!f.types.isSplittable(union_ty));
    try testing.expect(!f.types.isSplittable(loose));
    try testing.expect(!f.types.isSplittable(empty));
    try testing.expect(f.types.isSplittable(try f.pairTy()));
    // A record of records counts a layer for each.
    const nested = try f.types.recordTy(&.{ .{ .name = "p", .ty = try f.pairTy() }, .{ .name = "q", .ty = union_ty } });
    try testing.expectEqual(@as(u32, 2), f.types.splitLayers(nested));
}

test "N14a: the split row computes what the original computes" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const pair = try f.pairTy();
    const helper = try f.recordHelper();
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const first = try f.b.callRow(helper, &.{try f.b.record(pair, &.{ Ref.rowParam(0), Ref.rowParam(1) })});
    const second = try f.b.callRow(helper, &.{try f.b.record(pair, &.{ Ref.rowParam(1), Ref.rowParam(0) })});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ first, second })} });
    var before = try eval.Evaluator.init(arena.allocator(), &f.store, &f.types, .strict);
    const was = try before.run(root, &.{ .{ .int = 4 }, .{ .int = 7 } });
    const got = try f.site(root);
    testing.allocator.free(got);
    var after = try eval.Evaluator.init(arena.allocator(), &f.store, &f.types, .strict);
    try testing.expect(was.eql(try after.run(root, &.{ .{ .int = 4 }, .{ .int = 7 } })));
    // (4 * 2 + 7 * 3) + (7 * 2 + 4 * 3)
    try testing.expect(was.eql(.{ .int = 55 }));
}
