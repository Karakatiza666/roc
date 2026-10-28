//! N13u: integer intervals with literal bounds (normal-form 3.13), and the
//! result range N8k records at finalize (normal-form 3.8).
//!
//! The builder gives every node of a builtin integer type an interval from
//! these sources, and keeps the facts they read on its fact stack:
//!
//! | Source | Interval | Here |
//! |---|---|---|
//! | `Lit(n)` | `[n, n]` | `point` |
//! | a dominating arm of `is_lt`, `is_lte` or `is_eq` between the node and a literal | the half line or point the arm implies | `ofTest` |
//! | the index of `ForRange(a, b, inclusive)` | `a`'s least value to `b`'s greatest, less one when exclusive | `ofIndex` |
//! | `plus`, `minus`, `times`, `plus_wrap`, `times_wrap` | interval arithmetic; a checked op met with its type, a `_wrap` op that leaves its type the full type | `of` |
//! | a `Call` of a finalized row | the row's result range (N8k) | `ir.Row.result_range` |
//! | anything else | the type's full range | `full` |
//!
//! An interval only narrows: it holds every value the node can have where
//! its facts hold and the body does not crash. A missing interval leaves a
//! rule unapplied; it is never a guess. Bounds are `i256`, so no bound of a
//! builtin integer type, and no sum or product of two of them, saturates
//! before it leaves every type.

const std = @import("std");
const ir = @import("ir.zig");
const prims = @import("prims.zig");
const types_mod = @import("types.zig");

pub const Interval = ir.Interval;
const IntTy = types_mod.IntTy;
const Method = prims.Method;

/// The interval with no value: a region that a contradiction of facts
/// guards, which never runs.
pub const empty: Interval = .{ .lo = 1, .hi = 0 };

/// Every value of `int`.
pub fn full(int: IntTy) Interval {
    return .{ .lo = int.min(), .hi = int.max() };
}

/// The one value `v`.
pub fn point(v: i256) Interval {
    return .{ .lo = v, .hi = v };
}

/// Whether `a` holds no value.
pub fn isEmpty(a: Interval) bool {
    return a.lo > a.hi;
}

/// The values both `a` and `b` hold.
pub fn meet(a: Interval, b: Interval) Interval {
    return .{ .lo = @max(a.lo, b.lo), .hi = @min(a.hi, b.hi) };
}

/// The least interval that holds `a` and `b` (N8k's union over returns).
pub fn hull(a: Interval, b: Interval) Interval {
    if (isEmpty(a)) return b;
    if (isEmpty(b)) return a;
    return .{ .lo = @min(a.lo, b.lo), .hi = @max(a.hi, b.hi) };
}

/// Whether every value of `a` is a value of `int`.
pub fn within(a: Interval, int: IntTy) bool {
    return isEmpty(a) or (a.lo >= int.min() and a.hi <= int.max());
}

/// Whether `a` holds `v`.
pub fn contains(a: Interval, v: i256) bool {
    return a.lo <= v and v <= a.hi;
}

/// Whether `a` is narrower than the full range of `int`.
pub fn narrows(a: Interval, int: IntTy) bool {
    return a.lo > int.min() or a.hi < int.max();
}

/// The interval of `method` over operands of intervals `args`, without a
/// type's bounds: every value the mathematical operation takes. Null for a
/// method that is not interval arithmetic. `plus` and the `_wrap` forms take
/// any number of operands, as a chain N15a flattened.
pub fn raw(method: Method, args: []const Interval) ?Interval {
    switch (method) {
        .plus, .minus, .times, .plus_wrap, .times_wrap => {},
        else => return null,
    }
    for (args) |a| if (isEmpty(a)) return empty;
    return switch (method) {
        .plus, .plus_wrap => blk: {
            var acc = args[0];
            for (args[1..]) |a| acc = .{ .lo = acc.lo +| a.lo, .hi = acc.hi +| a.hi };
            break :blk acc;
        },
        .minus => .{ .lo = args[0].lo -| args[1].hi, .hi = args[0].hi -| args[1].lo },
        .times, .times_wrap => blk: {
            var acc = args[0];
            for (args[1..]) |a| {
                const corners = [_]i256{ acc.lo *| a.lo, acc.lo *| a.hi, acc.hi *| a.lo, acc.hi *| a.hi };
                acc = .{ .lo = std.mem.min(i256, &corners), .hi = std.mem.max(i256, &corners) };
            }
            break :blk acc;
        },
        else => unreachable, // the methods were checked above
    };
}

/// The interval of `method` at `int` over operands of intervals `args`: a
/// checked op crashes outside its type, so its interval is met with the
/// type; a `_wrap` op whose interval leaves its type can take any value of
/// it. Null for a method that is not interval arithmetic.
pub fn of(int: IntTy, method: Method, args: []const Interval) ?Interval {
    const r = raw(method, args) orelse return null;
    return switch (method) {
        .plus, .minus, .times => meet(r, full(int)),
        .plus_wrap, .times_wrap => if (within(r, int)) r else full(int),
        else => unreachable, // raw gives null for every other method
    };
}

/// Whether checked `method` at `int` over operands of intervals `args`
/// cannot overflow: every value of its interval is one of `int`.
pub fn fits(int: IntTy, method: Method, args: []const Interval) bool {
    switch (method) {
        .plus, .minus, .times => {},
        else => return false,
    }
    return within(raw(method, args).?, int);
}

/// N15a's condition on a checked `plus` chain at `int`: the sum of its
/// operands' negative lower bounds and the sum of their positive upper bounds
/// both fit, so every partial sum of every grouping fits.
pub fn chainFits(int: IntTy, args: []const Interval) bool {
    var neg: i256 = 0;
    var pos: i256 = 0;
    for (args) |a| {
        if (isEmpty(a)) return false;
        neg +|= @min(a.lo, 0);
        pos +|= @max(a.hi, 0);
    }
    return neg >= int.min() and pos <= int.max();
}

/// The interval that operand `x` of a comparison `method` with the literal
/// `k` has at `int` in the arm where the test is `holds`. `x_first` says
/// that `x` is the first operand. Null where the arm implies no interval:
/// the `False` arm of `is_eq`.
pub fn ofTest(int: IntTy, method: Method, x_first: bool, k: i256, holds: bool) ?Interval {
    const below = struct {
        fn f(t: IntTy, hi: i256) Interval {
            return .{ .lo = t.min(), .hi = hi };
        }
    }.f;
    const above = struct {
        fn f(t: IntTy, lo: i256) Interval {
            return .{ .lo = lo, .hi = t.max() };
        }
    }.f;
    return switch (method) {
        // `x < k` or `k < x`.
        .is_lt => if (x_first)
            (if (holds) below(int, k - 1) else above(int, k))
        else
            (if (holds) above(int, k + 1) else below(int, k)),
        // `x <= k` or `k <= x`.
        .is_lte => if (x_first)
            (if (holds) below(int, k) else above(int, k + 1))
        else
            (if (holds) above(int, k) else below(int, k - 1)),
        .is_eq => if (holds) point(k) else null,
        else => null,
    };
}

/// The interval of the index of a `ForRange` whose start has interval
/// `start` and whose end has interval `end`.
pub fn ofIndex(start: Interval, end: Interval, inclusive: bool) Interval {
    if (isEmpty(start) or isEmpty(end)) return empty;
    return .{ .lo = start.lo, .hi = if (inclusive) end.hi else end.hi - 1 };
}

/// What the interval `x` decides about the comparison `method` of `x` with
/// the literal `k`, `x` first when `x_first`: the answer for every value of
/// `x`, or null where values of `x` give both answers. An empty interval
/// decides nothing, so a region that never runs keeps its tests.
pub fn decide(method: Method, x_first: bool, x: Interval, k: i256) ?bool {
    if (isEmpty(x)) return null;
    return switch (method) {
        .is_lt => if (x_first)
            (if (x.hi < k) true else if (x.lo >= k) false else null)
        else
            (if (x.lo > k) true else if (x.hi <= k) false else null),
        .is_lte => if (x_first)
            (if (x.hi <= k) true else if (x.lo > k) false else null)
        else
            (if (x.lo >= k) true else if (x.hi < k) false else null),
        .is_eq => if (x.lo == k and x.hi == k) true else if (k < x.lo or k > x.hi) false else null,
        else => null,
    };
}

/// N8k (normal-form 3.8): the result range of `row`, whose result is of a
/// builtin integer type: the union of N13u's intervals over the values it
/// returns, its body's value and each `Return` on its paths and in its
/// loops. A literal is its value, a node N13u gave an interval when it was
/// built has it (`ir.NodeRange`), and anything else has the type's full
/// range. It is computed from the finalized body, and a caller reads only
/// what it records. Null for another result type, and where the union is
/// the full range.
pub fn resultRange(gpa: std.mem.Allocator, store: *const ir.Store, types: *const types_mod.Types, row: ir.RowId) std.mem.Allocator.Error!?Interval {
    const info = store.row(row);
    const int = switch (types.get(info.result)) {
        .int => |i| i,
        .bool_, .str, .float, .dec, .record, .tuple, .list, .tag_union, .nominal, .func, .opaque_, .recursive => return null,
    };
    var acc = empty;
    const body_end = store.region(info.body).end;
    if (body_end.kind == .value) acc = hull(acc, refInterval(store, types, int, store.refSlice(body_end.refs)[0]));
    var stack: std.ArrayList(ir.RegionId) = .empty;
    defer stack.deinit(gpa);
    try stack.append(gpa, info.body);
    while (stack.pop()) |r| {
        const end = store.region(r).end;
        switch (end.kind) {
            .return_ => acc = hull(acc, refInterval(store, types, int, store.refSlice(end.refs)[0])),
            // The arms and joins of an exiting switch are on the row's paths.
            .branch => try stack.appendSlice(gpa, store.regionSlice(store.node(ir.NodeId.of(end.target)).regions)),
            .open, .value, .jump, .continue_, .break_ => {},
        }
        // A loop in the region can return; a lambda's `Return` is its own.
        for (store.region_members.items[r.index()].items) |n| {
            const nd = store.node(n);
            if (nd.op.isLoop()) try stack.append(gpa, store.regionSlice(nd.regions)[0]);
        }
    }
    if (!narrows(acc, int)) return null;
    return acc;
}

// The interval of the returned value `ref`, of the integer type `int`.
fn refInterval(store: *const ir.Store, types: *const types_mod.Types, int: IntTy, ref: ir.Ref) Interval {
    if (ref.kind != .node) return full(int);
    const nd = store.node(ref.nodeId());
    if (nd.op == .lit) {
        const lit = store.lit(ir.LitId.of(nd.payload));
        const bits = lit.value.int;
        return point(if (types.get(lit.ty).int.signed()) @as(i128, @bitCast(bits)) else bits);
    }
    if (store.ranges.get(ref.nodeId())) |r| return r.interval;
    return full(int);
}

const testing = std.testing;
const all_ints = [_]IntTy{ .u8, .i8, .u16, .i16, .u32, .i32, .u64, .i64, .u128, .i128 };

// Every value `prims.foldInt` computes over values of `a` and `b`, where it
// does not fail, is a value of `of(a, b)`: probed at the bounds of each
// interval and at values between them.
fn expectHolds(int: IntTy, method: Method, a: Interval, b: Interval) !void {
    const iv = of(int, method, &.{ a, b }).?;
    const fit = fits(int, method, &.{ a, b });
    const probes = struct {
        fn of_(x: Interval) [5]i256 {
            const mid = x.lo + @divTrunc(x.hi - x.lo, 2);
            return .{ x.lo, x.hi, mid, @min(x.hi, x.lo + 1), @max(x.lo, x.hi - 1) };
        }
    }.of_;
    for (probes(a)) |x| for (probes(b)) |y| {
        if (prims.foldInt(int, method, x, y)) |v| {
            try testing.expect(contains(iv, v.int));
        } else {
            // A checked op that fails somewhere does not fit.
            try testing.expect(!fit);
        }
    };
}

test "N13u: interval arithmetic holds every value of plus, minus, times and the wrapping forms, at every width, met with the type's bounds" {
    var prng = std.Random.DefaultPrng.init(0x13a);
    const random = prng.random();
    for (all_ints) |int| {
        const lo = int.min();
        const hi = int.max();
        // The bounds of the type, a point at each end, and intervals drawn at random.
        var cases: std.ArrayList(Interval) = .empty;
        defer cases.deinit(testing.allocator);
        try cases.appendSlice(testing.allocator, &.{ full(int), point(lo), point(hi), point(0), .{ .lo = 0, .hi = 10 }, .{ .lo = @max(lo, -5), .hi = 5 } });
        for (0..12) |_| {
            const span = hi - lo;
            const x = lo + @mod(@as(i256, random.int(u128)), span + 1);
            const y = lo + @mod(@as(i256, random.int(u128)), span + 1);
            try cases.append(testing.allocator, .{ .lo = @min(x, y), .hi = @max(x, y) });
        }
        for (cases.items) |a| for (cases.items) |b| {
            for ([_]Method{ .plus, .minus, .times, .plus_wrap, .times_wrap }) |m| try expectHolds(int, m, a, b);
        };
    }
}

test "N13u: a checked op's interval is met with its type, and a wrapping op that leaves its type is the full type" {
    try testing.expectEqual(Interval{ .lo = 250, .hi = 255 }, of(.u8, .plus, &.{ .{ .lo = 245, .hi = 250 }, point(5) }).?);
    try testing.expect(!fits(.u8, .plus, &.{ .{ .lo = 245, .hi = 251 }, point(5) }));
    try testing.expect(fits(.u8, .plus, &.{ .{ .lo = 245, .hi = 250 }, point(5) }));
    try testing.expectEqual(full(.u8), of(.u8, .plus_wrap, &.{ .{ .lo = 245, .hi = 251 }, point(5) }).?);
    try testing.expectEqual(Interval{ .lo = 250, .hi = 255 }, of(.u8, .plus_wrap, &.{ .{ .lo = 245, .hi = 250 }, point(5) }).?);
    // `minus` at an unsigned type crashes below zero, so its interval starts at zero.
    try testing.expectEqual(Interval{ .lo = 0, .hi = 5 }, of(.u64, .minus, &.{ .{ .lo = 0, .hi = 10 }, point(5) }).?);
    try testing.expect(!fits(.u64, .minus, &.{ .{ .lo = 0, .hi = 10 }, point(5) }));
    try testing.expectEqual(Interval{ .lo = -128, .hi = 126 }, of(.i8, .times, &.{ .{ .lo = -64, .hi = 63 }, point(2) }).?);
    try testing.expect(!fits(.i8, .times, &.{ .{ .lo = -65, .hi = 63 }, point(2) }));
    // The widest types multiply without saturating short of every type's bounds.
    try testing.expect(!fits(.u128, .times, &.{ full(.u128), full(.u128) }));
    try testing.expect(!fits(.i128, .times, &.{ full(.i128), point(-1) }));
    try testing.expect(fits(.i128, .times, &.{ .{ .lo = IntTy.i128.min() + 1, .hi = IntTy.i128.max() }, point(-1) }));
    // An operand with no value gives no value.
    try testing.expect(isEmpty(of(.u8, .plus, &.{ empty, full(.u8) }).?));
    try testing.expect(raw(.div_trunc, &.{ full(.u8), full(.u8) }) == null);
}

test "N13u: a chain fits when its negative lower bounds and its positive upper bounds sum within the type" {
    // `(a + b) + c` and `a + (b + c)` both fit where every partial sum does.
    try testing.expect(chainFits(.u8, &.{ .{ .lo = 0, .hi = 100 }, .{ .lo = 0, .hi = 100 }, .{ .lo = 0, .hi = 55 } }));
    try testing.expect(!chainFits(.u8, &.{ .{ .lo = 0, .hi = 100 }, .{ .lo = 0, .hi = 100 }, .{ .lo = 0, .hi = 56 } }));
    // `-1 + max + 1` succeeds left to right and overflows regrouped, so it does not fit.
    try testing.expect(!chainFits(.i8, &.{ point(-1), point(127), point(1) }));
    try testing.expect(chainFits(.i8, &.{ .{ .lo = -60, .hi = 60 }, .{ .lo = -60, .hi = 60 }, .{ .lo = -8, .hi = 7 } }));
    try testing.expect(!chainFits(.i8, &.{ .{ .lo = -60, .hi = 60 }, .{ .lo = -60, .hi = 60 }, .{ .lo = -9, .hi = 7 } }));
}

test "N13u: each arm of a comparison with a literal gives its half line or point, and decides only what it holds" {
    for (all_ints) |int| {
        for ([_]Method{ .is_lt, .is_lte, .is_eq }) |m| for ([_]bool{ true, false }) |x_first| for ([_]bool{ true, false }) |holds| {
            const k: i256 = if (int.signed()) -3 else 7;
            const arm = ofTest(int, m, x_first, k, holds) orelse {
                try testing.expect(m == .is_eq and !holds);
                continue;
            };
            // Every value of the arm's interval gives the arm's answer, and each
            // value just outside it gives the other.
            for ([_]i256{ arm.lo, arm.hi }) |x| {
                const answer = prims.foldInt(int, m, if (x_first) x else k, if (x_first) k else x).?.bool_;
                try testing.expectEqual(holds, answer);
                try testing.expectEqual(holds, decide(m, x_first, point(x), k).?);
            }
            try testing.expectEqual(holds, decide(m, x_first, arm, k).?);
            if (arm.lo > int.min()) try testing.expect(decide(m, x_first, point(arm.lo - 1), k).? != holds);
            if (arm.hi < int.max()) try testing.expect(decide(m, x_first, point(arm.hi + 1), k).? != holds);
        };
    }
    try testing.expect(decide(.is_lt, true, .{ .lo = 0, .hi = 10 }, 5) == null);
    try testing.expect(decide(.is_lt, true, empty, 5) == null);
}

test "N13u: the index of a range runs from the least start to the greatest end, less one when exclusive" {
    try testing.expectEqual(Interval{ .lo = 0, .hi = 9 }, ofIndex(point(0), point(10), false));
    try testing.expectEqual(Interval{ .lo = 0, .hi = 10 }, ofIndex(point(0), point(10), true));
    try testing.expectEqual(Interval{ .lo = 2, .hi = 254 }, ofIndex(.{ .lo = 2, .hi = 7 }, full(.u8), false));
    try testing.expect(isEmpty(ofIndex(point(0), empty, false)));
}

test "N8k: the union of the intervals over a row's returns holds each of them" {
    const u = hull(.{ .lo = 0, .hi = 3 }, .{ .lo = 10, .hi = 12 });
    try testing.expectEqual(Interval{ .lo = 0, .hi = 12 }, u);
    try testing.expectEqual(point(4), hull(empty, point(4)));
}

// The sources and rules of N13u in the builder.

const builder_mod = @import("builder.zig");
const Ref = ir.Ref;

const Fixture = struct {
    store: ir.Store,
    types: types_mod.Types,
    b: builder_mod.Builder,

    fn init(self: *Fixture) void {
        self.store = ir.Store.init(testing.allocator);
        self.types = types_mod.Types.init(testing.allocator);
        self.b = builder_mod.Builder.init(testing.allocator, &self.store, &self.types);
    }

    fn deinit(self: *Fixture) void {
        self.b.deinit();
        self.types.deinit();
        self.store.deinit();
    }

    fn interval(self: *const Fixture, ref: Ref) Interval {
        return self.b.rangeOf(ref).?.interval;
    }

    fn speculatable(self: *const Fixture, ref: Ref) bool {
        return self.store.node(ref.nodeId()).flags.speculatable;
    }
};

test "N13u sources: a literal, each arm of a test against a literal, a literal switch's arm, an And operand, a ForRange index, and arithmetic over them" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const b = &f.b;
    const u8_ty = try f.types.intTy(.u8);
    _ = try b.beginRow(&.{ u8_ty, u8_ty }, u8_ty);
    const x = Ref.rowParam(0);
    const ten = try b.litInt(u8_ty, 10);
    try testing.expectEqual(point(10), f.interval(ten));
    // Anything else has the type's full range.
    try testing.expectEqual(full(.u8), f.interval(x));
    const lt = try b.call(.u8, .is_lt, &.{ x, ten });
    const no = try b.openArm(lt, 0);
    try testing.expectEqual(Interval{ .lo = 10, .hi = 255 }, f.interval(x));
    try testing.expectEqual(no, b.rangeOf(x).?.holds_in);
    try b.close(.{ .value = &.{x} });
    const yes = try b.openArm(lt, 1);
    try testing.expectEqual(Interval{ .lo = 0, .hi = 9 }, f.interval(x));
    // `10 <= y`, with the literal first, is its other half line.
    const y = Ref.rowParam(1);
    const lte = try b.call(.u8, .is_lte, &.{ ten, y });
    const inner = try b.openArm(lte, 1);
    try testing.expectEqual(Interval{ .lo = 10, .hi = 255 }, f.interval(y));
    // Interval arithmetic over both: the arm facts of both hold here.
    const sum = try b.call(.u8, .plus, &.{ x, y });
    try testing.expectEqual(Interval{ .lo = 10, .hi = 255 }, f.interval(sum));
    try testing.expectEqual(inner, b.rangeOf(sum).?.holds_in);
    try b.close(.{ .value = &.{sum} });
    try b.close(.{ .value = &.{x} });
    _ = yes;
    // Outside the arms the facts are gone.
    try testing.expectEqual(full(.u8), f.interval(x));
    // A literal switch's keyed arm is the key; its default arm decides nothing.
    const seven = try b.internLit(u8_ty, .{ .int = 7 });
    const keyed = try b.openLitArm(x, &.{seven.index()}, 0);
    try testing.expectEqual(point(7), f.interval(x));
    try b.close(.{ .value = &.{x} });
    _ = keyed;
    _ = try b.openLitArm(x, &.{seven.index()}, 1);
    try testing.expectEqual(full(.u8), f.interval(x));
    try b.close(.{ .value = &.{x} });
    // An `And` operand after `x < 10` holds under it.
    _ = try b.openOperand(&.{lt}, .and_);
    try testing.expectEqual(Interval{ .lo = 0, .hi = 9 }, f.interval(x));
    try b.close(.{ .value = &.{try b.litBool(true)} });
    // The index of `for i in 2..x` runs from 2 to 254, and of `2..=10` to 10.
    const two = try b.litInt(u8_ty, 2);
    const body = try b.openRegion(.loop_body, &.{ u8_ty, u8_ty });
    try b.noteRangeLoop(body, two, x, false);
    try testing.expectEqual(Interval{ .lo = 2, .hi = 254 }, f.interval(Ref.regionParam(body, 0)));
    // A slot of the loop gets nothing from its edges.
    try testing.expectEqual(full(.u8), f.interval(Ref.regionParam(body, 1)));
    try b.close(.{ .continue_ = &.{Ref.regionParam(body, 1)} });
    const closed = try b.openRegion(.loop_body, &.{ u8_ty, u8_ty });
    try b.noteRangeLoop(closed, two, ten, true);
    try testing.expectEqual(Interval{ .lo = 2, .hi = 10 }, f.interval(Ref.regionParam(closed, 0)));
    try b.close(.{ .continue_ = &.{Ref.regionParam(closed, 1)} });
    try b.endRow(.{ .value = &.{x} });
}

test "N13u: a comparison with a literal that an interval decides is that literal, and the knockout stops it" {
    for ([_]bool{ false, true }) |knocked| {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        const b = &f.b;
        if (knocked) b.hooks.algorithms_off.insert(.range_compare);
        const u8_ty = try f.types.intTy(.u8);
        _ = try b.beginRow(&.{u8_ty}, u8_ty);
        const x = Ref.rowParam(0);
        const lt = try b.call(.u8, .is_lt, &.{ x, try b.litInt(u8_ty, 10) });
        _ = try b.openArm(lt, 1);
        const decided = [_]Ref{
            try b.call(.u8, .is_lt, &.{ x, try b.litInt(u8_ty, 20) }),
            try b.call(.u8, .is_eq, &.{ x, try b.litInt(u8_ty, 50) }),
            // `x > 9` is `9 < x`, which is `False` here.
            try b.call(.u8, .is_gt, &.{ x, try b.litInt(u8_ty, 9) }),
        };
        const answers = [_]bool{ true, false, false };
        for (decided, answers) |r, want| {
            const n = f.store.node(r.nodeId());
            if (knocked) {
                try testing.expect(n.op == .prim);
            } else {
                try testing.expect(n.op == .lit and f.store.lit(ir.LitId.of(n.payload)).value.bool_ == want);
            }
        }
        // `x < 5` takes both answers.
        try testing.expect(f.store.node((try b.call(.u8, .is_lt, &.{ x, try b.litInt(u8_ty, 5) })).nodeId()).op == .prim);
        try b.close(.{ .value = &.{x} });
        try b.endRow(.{ .value = &.{x} });
    }
}

test "N13u: a checked op proved to fit is speculatable in the region of its facts and no further out, and the knockout stops it" {
    for ([_]bool{ false, true }) |knocked| {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        const b = &f.b;
        if (knocked) b.hooks.algorithms_off.insert(.range_fit);
        const u8_ty = try f.types.intTy(.u8);
        _ = try b.beginRow(&.{u8_ty}, u8_ty);
        const x = Ref.rowParam(0);
        const one = try b.litInt(u8_ty, 1);
        const lt = try b.call(.u8, .is_lt, &.{ x, try b.litInt(u8_ty, 255) });
        const arm = try b.openArm(lt, 1);
        // `x` is at most 254 here, so `x + 1` fits, and `x * 2` and `x - 1` do not.
        const inside = try b.call(.u8, .plus, &.{ x, one });
        try testing.expectEqual(!knocked, f.speculatable(inside));
        if (!knocked) try testing.expectEqual(arm, f.store.fitFloor(inside.nodeId()).?);
        try testing.expect(!f.speculatable(try b.call(.u8, .times, &.{ x, try b.litInt(u8_ty, 2) })));
        try testing.expect(!f.speculatable(try b.call(.u8, .minus, &.{ x, one })));
        try b.close(.{ .value = &.{inside} });
        // Over the full range outside the arm `x + 1` can overflow.
        const outside = try b.call(.u8, .plus, &.{ x, one });
        try testing.expect(inside != outside);
        try testing.expect(!f.speculatable(outside));
        // Two literals' sum fits everywhere: no fact limits it.
        b.hooks.knocked_out = @splat(true);
        const lits = try b.call(.u8, .plus, &.{ one, one });
        try testing.expectEqual(!knocked, f.speculatable(lits));
        try testing.expect(f.store.fitFloor(lits.nodeId()) == null);
        b.hooks.knocked_out = @splat(false);
        try b.endRow(.{ .value = &.{x} });
    }
}

test "N13u: a node built under a fact keeps its interval inside that fact's region, and a sibling arm or the region outside builds its own" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const b = &f.b;
    const u8_ty = try f.types.intTy(.u8);
    _ = try b.beginRow(&.{u8_ty}, u8_ty);
    const x = Ref.rowParam(0);
    const one = try b.litInt(u8_ty, 1);
    const lt = try b.call(.u8, .is_lt, &.{ x, try b.litInt(u8_ty, 10) });
    // Where `x < 10`, `x + 1` is in 1..=10.
    const then_arm = try b.openArm(lt, 1);
    const inside = try b.call(.u8, .plus, &.{ x, one });
    try testing.expectEqual(Interval{ .lo = 1, .hi = 10 }, f.interval(inside));
    try testing.expectEqual(then_arm, b.rangeOf(inside).?.holds_in);
    try b.close(.{ .value = &.{inside} });
    // Where `x >= 10`, `x + 1` is a new node in 11..=255: `x + 1 < 50` is not decided.
    _ = try b.openArm(lt, 0);
    const sibling = try b.call(.u8, .plus, &.{ x, one });
    try testing.expect(sibling != inside);
    try testing.expectEqual(Interval{ .lo = 11, .hi = 255 }, f.interval(sibling));
    try testing.expect(f.store.node((try b.call(.u8, .is_lt, &.{ sibling, try b.litInt(u8_ty, 50) })).nodeId()).op == .prim);
    try b.close(.{ .value = &.{sibling} });
    // Outside both arms `x + 1` is a new node over the full range: `x + 1 > 100` is not decided.
    const outside = try b.call(.u8, .plus, &.{ x, one });
    try testing.expect(outside != inside and outside != sibling);
    try testing.expectEqual(Interval{ .lo = 1, .hi = 255 }, f.interval(outside));
    try testing.expect(f.store.node((try b.call(.u8, .is_gt, &.{ outside, try b.litInt(u8_ty, 100) })).nodeId()).op == .prim);
    // Built outside first, the node a later arm finds keeps the outside
    // interval, which holds there too: nothing it decides is wrong.
    const two = try b.litInt(u8_ty, 2);
    const first = try b.call(.u8, .plus, &.{ x, two });
    _ = try b.openArm(lt, 1);
    const again = try b.call(.u8, .plus, &.{ x, two });
    try testing.expectEqual(first, again);
    try testing.expectEqual(ir.RegionId.none, b.rangeOf(again).?.holds_in);
    try testing.expectEqual(Interval{ .lo = 2, .hi = 255 }, f.interval(again));
    try b.close(.{ .value = &.{again} });
    try b.endRow(.{ .value = &.{outside} });
}

test "N13u with N15a: a checked plus chain whose intervals prove no grouping overflows is one Prim, and one they do not prove keeps its grouping" {
    for ([_]bool{ false, true }) |knocked| {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        const b = &f.b;
        if (knocked) b.hooks.algorithms_off.insert(.range_chain);
        const u8_ty = try f.types.intTy(.u8);
        _ = try b.beginRow(&.{ u8_ty, u8_ty, u8_ty }, u8_ty);
        const p = Ref.rowParam;
        // Unbounded, `(a + b) + c` and `a + (b + c)` stay as written.
        const left = try b.call(.u8, .plus, &.{ try b.call(.u8, .plus, &.{ p(0), p(1) }), p(2) });
        try testing.expectEqual(@as(usize, 2), f.store.node(left.nodeId()).args.len);
        // Under `a < 80`, `b < 80` and `c < 80`, both are `plus(a, b, c)`.
        var arms: [3]ir.RegionId = undefined;
        for (&arms, 0..) |*arm, k| arm.* = try b.openArm(try b.call(.u8, .is_lt, &.{ p(@intCast(k)), try b.litInt(u8_ty, 80) }), 1);
        const l = try b.call(.u8, .plus, &.{ try b.call(.u8, .plus, &.{ p(0), p(1) }), p(2) });
        const r = try b.call(.u8, .plus, &.{ p(0), try b.call(.u8, .plus, &.{ p(1), p(2) }) });
        if (knocked) {
            try testing.expect(l != r);
        } else {
            try testing.expectEqual(l, r);
            try testing.expectEqualSlices(Ref, &.{ p(0), p(1), p(2) }, f.store.refSlice(f.store.node(l.nodeId()).args));
            try testing.expect(f.speculatable(l));
        }
        // A literal goes last before the chain flattens.
        const k = try b.call(.u8, .plus, &.{ try b.litInt(u8_ty, 1), try b.call(.u8, .plus, &.{ p(0), p(1) }) });
        if (!knocked) try testing.expectEqualSlices(Ref, &.{ p(0), p(1), try b.litInt(u8_ty, 1) }, f.store.refSlice(f.store.node(k.nodeId()).args));
        for (arms) |_| try b.close(.{ .value = &.{l} });
        try b.endRow(.{ .value = &.{p(0)} });
    }
}

test "N13u: a call of a finalized row has the row's result range (N8k), and one of a row being built has none" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const b = &f.b;
    const u8_ty = try f.types.intTy(.u8);
    const callee = try b.beginRow(&.{u8_ty}, u8_ty);
    try b.endRow(.{ .value = &.{try b.call(.u8, .plus, &.{ Ref.rowParam(0), try b.litInt(u8_ty, 1) })} });
    const range = (try resultRange(testing.allocator, &f.store, &f.types, callee)).?;
    try testing.expectEqual(Interval{ .lo = 1, .hi = 255 }, range);
    _ = try b.beginRow(&.{u8_ty}, u8_ty);
    try testing.expectEqual(full(.u8), f.interval(try b.callRow(callee, &.{Ref.rowParam(0)})));
    f.store.rows.items[callee.index()].result_range = range;
    f.store.rows.items[callee.index()].digest = 1;
    const call = try b.callRow(callee, &.{try b.litInt(u8_ty, 3)});
    try testing.expectEqual(range, f.interval(call));
    // So `0 < f(3)` is decided.
    try testing.expect(f.store.node((try b.call(.u8, .is_lt, &.{ try b.litInt(u8_ty, 0), call })).nodeId()).op == .lit);
    try b.endRow(.{ .value = &.{call} });
}
