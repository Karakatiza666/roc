//! The views of a site (normal-form 5.1, plan 1.3 "views").
//!
//! | View | Step | Rows it keeps |
//! |---|---|---|
//! | `graph` | V1 | recursive components, rows whose body can end in `Return` (see below), rows called from two or more places, and rows a closure names; a row called from one place is inlined there, and the count is taken again until it stops changing |
//! | `inline` | V2 | recursive components, and rows whose body can end in `Return` (see below); every other call is inlined, and a `Closure` of a non-recursive row is a `Lambda` region in place |
//!
//! The driver runs V1 once every component is final, then simplifies the
//! rows it changed and finalizes the site's rows again (plan 3.5), because
//! inlining can merge two calls that were distinct only because their
//! arguments differed before simplification. V2 runs over the `graph` view
//! the same way.
//!
//! A row whose body can end in `Return`, in its own region or in any region
//! nested in it but a lambda body, is not inlined: inlining it would
//! turn each `Return` into a jump to the code after the call, which the
//! rebuild does not build yet (plan 4.1, M3). Its closures still become
//! lambdas, because a `Return` in a lambda body ends the lambda.

const std = @import("std");
const ir = @import("ir.zig");
const live_mod = @import("live.zig");
const number = @import("number.zig");

const Allocator = std.mem.Allocator;
const RowId = ir.RowId;

/// What a view inlines in one turn: the rows whose calls it inlines, the
/// rows whose closures become lambdas, and the rows that hold those calls
/// and closures.
pub const Turn = struct {
    inlined: []RowId,
    lambdas: []RowId,
    callers: []RowId,

    pub fn deinit(self: *Turn, gpa: Allocator) void {
        gpa.free(self.inlined);
        gpa.free(self.lambdas);
        gpa.free(self.callers);
    }
};

/// V1 over the site of `root`: every row but the root that is not
/// recursive, that one `Call` names and no `Closure` does, and whose body
/// ends in one value; and the rows that hold those calls, in the order the
/// site reaches them.
pub fn singleUse(gpa: Allocator, store: *const ir.Store, root: RowId) Allocator.Error!Turn {
    return turnOf(gpa, store, root, .graph);
}

/// V2 over the site of `root`: every row but the root that is not
/// recursive, that a `Call` names, and whose body ends in one value; every
/// row but the root that is not recursive and that a `Closure` names; and
/// the rows that hold those calls and closures, in the order the site
/// reaches them.
pub fn everyHelper(gpa: Allocator, store: *const ir.Store, root: RowId) Allocator.Error!Turn {
    return turnOf(gpa, store, root, .inline_);
}

const Kind = enum { graph, inline_ };

fn turnOf(gpa: Allocator, store: *const ir.Store, root: RowId, kind: Kind) Allocator.Error!Turn {
    var returns = try live_mod.Returns.init(gpa, store);
    defer returns.deinit(gpa);
    var reached: ir.RowTable(number.Numbering) = .empty;
    defer {
        for (reached.values()) |*n| n.deinit(gpa);
        reached.deinit(gpa);
    }
    try number.siteRows(gpa, store, &returns, root, &reached);
    const calls = try gpa.alloc(u32, store.rows.items.len);
    defer gpa.free(calls);
    @memset(calls, 0);
    const named = try gpa.alloc(bool, store.rows.items.len);
    defer gpa.free(named);
    @memset(named, false);
    var inlined: std.ArrayList(RowId) = .empty;
    defer inlined.deinit(gpa);
    var lambdas: std.ArrayList(RowId) = .empty;
    defer lambdas.deinit(gpa);
    for (reached.values()) |numbering| for (numbering.order.items) |n| {
        const nd = store.node(n);
        switch (nd.op) {
            .call => calls[nd.payload] +|= 1,
            .closure => named[nd.payload] = true,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => {},
        }
    };
    for (reached.keys()) |r| {
        const info = store.row(r);
        if (r == root or info.recursive) continue;
        const end = store.region(info.body).end;
        // A `Return` nested in a loop or an arm would end the caller if
        // the body were inlined, so such a row is not one value.
        const one_value = end.kind == .value and end.refs.len == 1 and !returns.regionHolds(store, info.body);
        switch (kind) {
            .graph => if (calls[r.index()] == 1 and !named[r.index()] and one_value) try inlined.append(gpa, r),
            .inline_ => {
                if (calls[r.index()] > 0 and one_value) try inlined.append(gpa, r);
                if (named[r.index()]) try lambdas.append(gpa, r);
            },
        }
    }
    var callers: std.ArrayList(RowId) = .empty;
    errdefer callers.deinit(gpa);
    for (reached.keys(), reached.values()) |r, numbering| for (numbering.order.items) |n| {
        const nd = store.node(n);
        const set = switch (nd.op) {
            .call => inlined.items,
            .closure => lambdas.items,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => continue,
        };
        if (std.mem.findScalar(RowId, set, RowId.of(nd.payload)) == null) continue;
        if (std.mem.findScalar(RowId, callers.items, r) == null) try callers.append(gpa, r);
        break;
    };
    const inlined_out = try inlined.toOwnedSlice(gpa);
    errdefer gpa.free(inlined_out);
    const lambdas_out = try lambdas.toOwnedSlice(gpa);
    errdefer gpa.free(lambdas_out);
    return .{ .inlined = inlined_out, .lambdas = lambdas_out, .callers = try callers.toOwnedSlice(gpa) };
}

const testing = std.testing;
const types_mod = @import("types.zig");
const builder_mod = @import("builder.zig");
const driver = @import("driver.zig");
const dump = @import("dump.zig");
const digest_mod = @import("digest.zig");
const verify_mod = @import("verify.zig");
const TyId = ir.TyId;
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

    fn expectGraph(self: *Fixture, root: RowId, want: []const u8) (driver.Error || std.Io.Writer.Error || error{TestExpectedEqual})!void {
        return self.expectView(root, .graph, want);
    }

    fn expectView(self: *Fixture, root: RowId, view: driver.View, want: []const u8) (driver.Error || std.Io.Writer.Error || error{TestExpectedEqual})!void {
        _ = try driver.runTo(testing.allocator, &self.b, root, &.{}, view);
        var out: std.Io.Writer.Allocating = .init(testing.allocator);
        defer out.deinit();
        try dump.dumpSite(&out.writer, testing.allocator, &self.store, &self.types, root);
        try testing.expectEqualStrings(want, out.written());
    }
};

// `|z| z * z`.
fn squareRow(f: *Fixture) Allocator.Error!RowId {
    const i64_ty = try f.types.intTy(.i64);
    const r = try f.b.beginRow(&.{i64_ty}, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) })} });
    return r;
}

test "V1: a row called from one place is inlined, and one called from two places stays a row" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const once = try squareRow(&f);
    const twice = try f.b.beginRow(&.{i64_ty}, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(0), try f.b.litInt(i64_ty, 1) })} });
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const a = try f.b.callRow(once, &.{Ref.rowParam(0)});
    const b1 = try f.b.callRow(twice, &.{Ref.rowParam(0)});
    const b2 = try f.b.callRow(twice, &.{Ref.rowParam(1)});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ a, try f.b.call(.i64, .bitwise_xor, &.{ b1, b2 }) })} });
    try f.expectGraph(root,
        \\row r0 (I64, I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p0) : I64
        \\  n1 = call r1(p0) : I64
        \\  n2 = call r1(p1) : I64
        \\  n3 = Num.I64.bitwise_xor(n0, n1, n2) : I64
        \\  value n3
        \\row r1 (I64) -> I64
        \\  n0 = 1 : I64
        \\  n1 = Num.I64.plus_wrap(p0, n0) : I64
        \\  value n1
        \\
    );
}

test "V1: the count is taken again, so a row two merged callers called becomes single-use and is inlined" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const sq = try squareRow(&f);
    // `f1` and `f2` are both `|a| sq(a + 1)`: N8g merges them, the two
    // calls merge, and V1 inlines the one row left, then `sq`.
    var callers: [2]RowId = undefined;
    for (&callers) |*c| {
        c.* = try f.b.beginRow(&.{i64_ty}, i64_ty);
        const next = try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(0), try f.b.litInt(i64_ty, 1) });
        try f.b.endRow(.{ .value = &.{try f.b.callRow(sq, &.{next})} });
    }
    const root = try f.b.beginRow(&.{i64_ty}, i64_ty);
    const x = try f.b.callRow(callers[0], &.{Ref.rowParam(0)});
    const y = try f.b.callRow(callers[1], &.{Ref.rowParam(0)});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ x, y })} });
    try f.expectGraph(root,
        \\row r0 (I64) -> I64
        \\  n0 = 1 : I64
        \\  n1 = Num.I64.plus_wrap(p0, n0) : I64
        \\  n2 = Num.I64.times_wrap(n1, n1) : I64
        \\  n3 = Num.I64.bitwise_xor(n2, n2) : I64
        \\  value n3
        \\
    );
}

test "V2: a row called from two places is inlined at both" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const sq = try squareRow(&f);
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const a = try f.b.callRow(sq, &.{Ref.rowParam(0)});
    const b1 = try f.b.callRow(sq, &.{Ref.rowParam(1)});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ a, b1 })} });
    try f.expectView(root, .inline_,
        \\row r0 (I64, I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p0) : I64
        \\  n1 = Num.I64.times_wrap(p1, p1) : I64
        \\  n2 = Num.I64.bitwise_xor(n0, n1) : I64
        \\  value n2
        \\
    );
}

test "V2: a closure of a row that is not recursive is a lambda in place, over its captures" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const fn_ty = try f.types.funcTy(&.{i64_ty}, i64_ty);
    // `|n| |x| sq(x) + n`, whose helper `sq` is inlined into the lambda.
    const sq = try squareRow(&f);
    const add = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ try f.b.callRow(sq, &.{Ref.rowParam(1)}), Ref.rowParam(0) })} });
    const root = try f.b.beginRow(&.{i64_ty}, fn_ty);
    try f.b.endRow(.{ .value = &.{try f.b.closure(add, &.{Ref.rowParam(0)}, fn_ty)} });
    try f.expectView(root, .inline_,
        \\row r0 (I64) -> (I64 -> I64)
        \\  n2 = lambda() : (I64 -> I64)
        \\    lambda (s2.0: I64)
        \\      n0 = Num.I64.times_wrap(s2.0, s2.0) : I64
        \\      n1 = Num.I64.plus_wrap(n0, p0) : I64
        \\      value n1
        \\  value n2
        \\
    );
}

test "V2: a recursive row stays a row, and the helper it calls is inlined into it" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const sq = try squareRow(&f);
    // `down = |n| if n == 0 then 0 else sq(n) + down(n - 1)`, called twice.
    const down = try f.b.beginRow(&.{i64_ty}, i64_ty);
    const zero = try f.b.litInt(i64_ty, 0);
    const done = try f.b.call(.i64, .is_eq, &.{ Ref.rowParam(0), zero });
    const arm0 = try f.b.openArm(done, 0);
    const rest = try f.b.callRow(down, &.{try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(0), try f.b.litInt(i64_ty, -1) })});
    try f.b.close(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ try f.b.callRow(sq, &.{Ref.rowParam(0)}), rest })} });
    const arm1 = try f.b.openArm(done, 1);
    try f.b.close(.{ .value = &.{zero} });
    try f.b.endRow(.{ .value = &.{try f.b.switchOn(done, &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{})} });
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const x = try f.b.callRow(down, &.{Ref.rowParam(0)});
    const y = try f.b.callRow(down, &.{Ref.rowParam(1)});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ x, y })} });
    try f.expectView(root, .inline_,
        \\row r0 (I64, I64) -> I64
        \\  n0 = call r1(p0) : I64 !spec
        \\  n1 = call r1(p1) : I64 !spec
        \\  n2 = Num.I64.bitwise_xor(n0, n1) : I64
        \\  value n2
        \\row r1 (I64) -> I64 recursive
        \\  n6 = switch p0 : I64 !spec
        \\    arm 0
        \\      n0 = 0 : I64
        \\      value n0
        \\    default
        \\      n1 = Num.I64.times_wrap(p0, p0) : I64
        \\      n2 = -1 : I64
        \\      n3 = Num.I64.plus_wrap(p0, n2) : I64
        \\      n4 = call r1(n3) : I64 !spec
        \\      n5 = Num.I64.plus_wrap(n1, n4) : I64
        \\      value n5
        \\  value n6
        \\
    );
}

test "V2: inlining a helper called twice cancels the record it builds against the field the caller reads" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const rec_ty = try f.types.recordTy(&.{ .{ .name = "x", .ty = i64_ty }, .{ .name = "y", .ty = i64_ty } });
    // `mk = |a| { x: a, y: a * a }`; the root is `mk(p0).y + mk(p1).x`.
    const mk = try f.b.beginRow(&.{i64_ty}, rec_ty);
    try f.b.endRow(.{ .value = &.{try f.b.record(rec_ty, &.{ Ref.rowParam(0), try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) }) })} });
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const y = try f.b.field(try f.b.callRow(mk, &.{Ref.rowParam(0)}), 1);
    const x = try f.b.field(try f.b.callRow(mk, &.{Ref.rowParam(1)}), 0);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ y, x })} });
    try f.expectView(root, .inline_,
        \\row r0 (I64, I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p0) : I64
        \\  n1 = Num.I64.bitwise_xor(n0, p1) : I64
        \\  value n1
        \\
    );
}

test "V2: a row whose body can end in Return stays a row, and its closure is still a lambda" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const fn_ty = try f.types.funcTy(&.{i64_ty}, i64_ty);
    // `early = |a| { if a == 0 { return 1 }; a * a + early_rest }`, where the
    // code after the `if` is a join two paths reach, so no exit rule folds it.
    const early = try f.b.beginRow(&.{i64_ty}, i64_ty);
    const zero = try f.b.litInt(i64_ty, 0);
    const c = try f.b.call(.i64, .is_lt, &.{ Ref.rowParam(0), zero });
    const join = try f.b.reserveJoin(&.{i64_ty});
    const arm0 = try f.b.openArm(c, 0);
    const d = try f.b.call(.i64, .is_eq, &.{ Ref.rowParam(0), zero });
    const inner0 = try f.b.openArm(d, 0);
    try f.b.close(.{ .jump = .{ .join = join, .args = &.{Ref.rowParam(0)} } });
    const inner1 = try f.b.openArm(d, 1);
    try f.b.close(.{ .return_ = try f.b.litInt(i64_ty, 1) });
    const inner = try f.b.exitingSwitch(d, &.{ inner0, inner1 }, &.{}, &.{});
    try f.b.close(.{ .branch = inner });
    const arm1 = try f.b.openArm(c, 1);
    try f.b.close(.{ .jump = .{ .join = join, .args = &.{try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) })} } });
    const sw = try f.b.exitingSwitch(c, &.{ arm0, arm1 }, &.{join}, &.{});
    try f.b.continueIn(sw, join);
    const v = Ref.regionParam(join, 0);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ v, v })} });
    const pair_ty = try f.types.tupleTy(&.{ i64_ty, fn_ty });
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, pair_ty);
    const twice = try f.b.call(.i64, .plus_wrap, &.{ try f.b.callRow(early, &.{Ref.rowParam(0)}), try f.b.callRow(early, &.{Ref.rowParam(1)}) });
    try f.b.endRow(.{ .value = &.{try f.b.tuple(pair_ty, &.{ twice, try f.b.closure(early, &.{}, fn_ty) })} });
    try f.expectView(root, .inline_,
        \\row r0 (I64, I64) -> (I64, (I64 -> I64))
        \\  n0 = call r1(p0) : I64 !spec
        \\  n1 = call r1(p1) : I64 !spec
        \\  n2 = Num.I64.plus_wrap(n0, n1) : I64
        \\  n3 = 0 : I64
        \\  n6 = 1 : I64
        \\  n11 = lambda() : (I64 -> I64)
        \\    lambda (s11.0: I64)
        \\      n4 = Num.I64.is_lt(s11.0, n3) : Bool
        \\      n10 = switch n4 : !spec
        \\        arm 0
        \\          n5 = Num.I64.is_eq(s11.0, n3) : Bool
        \\          n7 = switch n5 : !spec
        \\            arm 0
        \\              jump j0 s11.0
        \\            arm 1
        \\              return n6
        \\          branch n7
        \\        arm 1
        \\          n8 = Num.I64.plus_wrap(s11.0, s11.0) : I64
        \\          jump j0 n8
        \\        join j0 (s10.0: I64)
        \\          n9 = Num.I64.times_wrap(s10.0, s10.0) : I64
        \\          return n9
        \\      branch n10
        \\  n12 = tuple(n2, n11) : (I64, (I64 -> I64))
        \\  value n12
        \\row r1 (I64) -> I64
        \\  n0 = 0 : I64
        \\  n1 = Num.I64.is_lt(p0, n0) : Bool
        \\  n7 = switch n1 : !spec
        \\    arm 0
        \\      n2 = Num.I64.is_eq(p0, n0) : Bool
        \\      n4 = switch n2 : !spec
        \\        arm 0
        \\          jump j0 p0
        \\        arm 1
        \\          n3 = 1 : I64
        \\          return n3
        \\      branch n4
        \\    arm 1
        \\      n5 = Num.I64.plus_wrap(p0, p0) : I64
        \\      jump j0 n5
        \\    join j0 (s7.0: I64)
        \\      n6 = Num.I64.times_wrap(s7.0, s7.0) : I64
        \\      return n6
        \\  branch n7
        \\
    );
}

test "V2: the simplify rerun simplifies an inlined body's nodes under the facts of the arms they sink into" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const bool_ty = try f.types.boolTy();
    const pair_ty = try f.types.tupleTy(&.{ i64_ty, i64_ty });
    // `both = |c, a| (if c { a } else { a * a }, a + 1)`, called twice. The
    // root reads both parts of `both(p0, p1)` in the arms of a switch on
    // `p0`, so the call stands before the switch, and the `if` sinks into
    // the arm where `p0` is False, which decides it.
    const both = try f.b.beginRow(&.{ bool_ty, i64_ty }, pair_ty);
    const no = try f.b.openArm(Ref.rowParam(0), 0);
    try f.b.close(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(1), Ref.rowParam(1) })} });
    const yes = try f.b.openArm(Ref.rowParam(0), 1);
    try f.b.close(.{ .value = &.{Ref.rowParam(1)} });
    const first = try f.b.switchOn(Ref.rowParam(0), &.{ no, yes }, &.{}, &.{i64_ty}, &.{});
    try f.b.endRow(.{ .value = &.{try f.b.tuple(pair_ty, &.{ first, try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(1), try f.b.litInt(i64_ty, 1) }) })} });
    const root = try f.b.beginRow(&.{ bool_ty, i64_ty, bool_ty, i64_ty }, i64_ty);
    const t = try f.b.callRow(both, &.{ Ref.rowParam(0), Ref.rowParam(1) });
    const other = try f.b.index(try f.b.callRow(both, &.{ Ref.rowParam(2), Ref.rowParam(3) }), 1);
    const arm0 = try f.b.openArm(Ref.rowParam(0), 0);
    try f.b.close(.{ .value = &.{try f.b.index(t, 0)} });
    const arm1 = try f.b.openArm(Ref.rowParam(0), 1);
    try f.b.close(.{ .value = &.{try f.b.index(t, 1)} });
    const chosen = try f.b.switchOn(Ref.rowParam(0), &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ chosen, other })} });
    try f.expectView(root, .inline_,
        \\row r0 (Bool, I64, Bool, I64) -> I64
        \\  n1 = 1 : I64
        \\  n3 = switch p0 : I64
        \\    arm 0
        \\      n0 = Num.I64.times_wrap(p1, p1) : I64
        \\      value n0
        \\    arm 1
        \\      n2 = Num.I64.plus_wrap(p1, n1) : I64
        \\      value n2
        \\  n4 = Num.I64.plus_wrap(p3, n1) : I64
        \\  n5 = Num.I64.bitwise_xor(n3, n4) : I64
        \\  value n5
        \\
    );
}

test "V2: a lambda body whose exits fold ends in its value, as a row body does" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const fn_ty = try f.types.funcTy(&.{i64_ty}, i64_ty);
    const pair_ty = try f.types.tupleTy(&.{ i64_ty, fn_ty });
    // `g = |k, a| { if k < 0 { if a == 0 { return 1 } }; k * k }`, where the
    // code after the `if` is a join two paths reach. In the lambda over
    // `k = p0`, the join's `k * k` is the caller's `p0 * p0`, so the join has
    // no nodes of its own, and the exit rules fold the lambda's body to a
    // `Return`, which T6 makes its value.
    const g = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const zero = try f.b.litInt(i64_ty, 0);
    const c = try f.b.call(.i64, .is_lt, &.{ Ref.rowParam(0), zero });
    const join = try f.b.reserveJoin(&.{});
    const arm0 = try f.b.openArm(c, 0);
    try f.b.close(.{ .jump = .{ .join = join, .args = &.{} } });
    const arm1 = try f.b.openArm(c, 1);
    const d = try f.b.call(.i64, .is_eq, &.{ Ref.rowParam(1), zero });
    const inner0 = try f.b.openArm(d, 0);
    try f.b.close(.{ .jump = .{ .join = join, .args = &.{} } });
    const inner1 = try f.b.openArm(d, 1);
    try f.b.close(.{ .return_ = try f.b.litInt(i64_ty, 1) });
    const inner = try f.b.exitingSwitch(d, &.{ inner0, inner1 }, &.{}, &.{});
    try f.b.close(.{ .branch = inner });
    const sw = try f.b.exitingSwitch(c, &.{ arm0, arm1 }, &.{join}, &.{});
    try f.b.continueIn(sw, join);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) })} });
    const root = try f.b.beginRow(&.{i64_ty}, pair_ty);
    const sq = try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) });
    try f.b.endRow(.{ .value = &.{try f.b.tuple(pair_ty, &.{ sq, try f.b.closure(g, &.{Ref.rowParam(0)}, fn_ty) })} });
    try f.expectView(root, .inline_,
        \\row r0 (I64) -> (I64, (I64 -> I64))
        \\  n0 = Num.I64.times_wrap(p0, p0) : I64
        \\  n1 = 0 : I64
        \\  n2 = Num.I64.is_lt(p0, n1) : Bool
        \\  n5 = 1 : I64
        \\  n7 = lambda() : (I64 -> I64)
        \\    lambda (s7.0: I64)
        \\      n4 = and(n2) : Bool
        \\        operand
        \\          n3 = Num.I64.is_eq(s7.0, n1) : Bool
        \\          value n3
        \\      n6 = switch n4 : I64
        \\        arm 0
        \\          value n0
        \\        arm 1
        \\          value n5
        \\      value n6
        \\  n8 = tuple(n0, n7) : (I64, (I64 -> I64))
        \\  value n8
        \\
    );
}

// `|n| if n < 1 { B } else { A }`, its tags built at `tag_ty`.
fn pickRow(f: *Fixture, tag_ty: TyId) Allocator.Error!RowId {
    const i64_ty = try f.types.intTy(.i64);
    const a = try f.types.name("A");
    const b_name = try f.types.name("B");
    const row = try f.b.beginRow(&.{i64_ty}, tag_ty);
    const c = try f.b.call(.i64, .is_lt, &.{ Ref.rowParam(0), try f.b.litInt(i64_ty, 1) });
    const no = try f.b.openArm(c, 0);
    try f.b.close(.{ .value = &.{try f.b.tag(tag_ty, b_name, &.{})} });
    const yes = try f.b.openArm(c, 1);
    try f.b.close(.{ .value = &.{try f.b.tag(tag_ty, a, &.{})} });
    try f.b.endRow(.{ .value = &.{try f.b.switchOn(c, &.{ no, yes }, &.{}, &.{tag_ty}, &.{})} });
    return row;
}

// The view of `root`, its dump, and the digest of its body, which must verify.
fn inlinedForm(f: *Fixture, root: RowId, dump_out: *std.Io.Writer.Allocating) (driver.Error || std.Io.Writer.Error || Allocator.Error || error{TestUnexpectedResult})!digest_mod.Digest {
    _ = try driver.runTo(testing.allocator, &f.b, root, &.{}, .inline_);
    var report = try verify_mod.verifyAll(testing.allocator, &f.store, &f.types);
    defer report.deinit();
    try testing.expect(report.ok());
    try dump.dumpSite(&dump_out.writer, testing.allocator, &f.store, &f.types, root);
    return digest_mod.ofRegion(testing.allocator, &f.store, f.store.row(root).body);
}

test "V2: a call read at a wider union inlines to a body whose ends are built at that union" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const narrow = try f.types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{} } });
    const wide = try f.types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{} }, .{ .name = "C", .payload = &.{} } });
    // `pick` builds `[A, B]`, and the root calls it at `[A, B, C]`.
    const pick = try pickRow(&f, narrow);
    const root = try f.b.beginRow(&.{i64_ty}, wide);
    try f.b.endRow(.{ .value = &.{try f.b.callRowAt(pick, &.{Ref.rowParam(0)}, wide)} });
    // The same code written at `[A, B, C]`.
    const written = try pickRow(&f, wide);

    var got: std.Io.Writer.Allocating = .init(testing.allocator);
    defer got.deinit();
    var want: std.Io.Writer.Allocating = .init(testing.allocator);
    defer want.deinit();
    const got_digest = try inlinedForm(&f, root, &got);
    const want_digest = try inlinedForm(&f, written, &want);
    try testing.expectEqualStrings(
        \\row r0 (I64) -> [A, B, C]
        \\  n0 = 1 : I64
        \\  n1 = Num.I64.is_lt(p0, n0) : Bool
        \\  n4 = switch n1 : [A, B, C]
        \\    arm 0
        \\      n2 = tag B() : [A, B, C]
        \\      value n2
        \\    arm 1
        \\      n3 = tag A() : [A, B, C]
        \\      value n3
        \\  value n4
        \\
    , got.written());
    try testing.expectEqualStrings(want.written(), got.written());
    try testing.expectEqual(want_digest, got_digest);
}

test "V2: a call read at a wider union demands the payload types of a tag and the backing of a nominal" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const inner_narrow = try f.types.tagUnionTy(&.{.{ .name = "A", .payload = &.{} }});
    const inner_wide = try f.types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{} } });
    const some = try f.types.name("Some");
    const a = try f.types.name("A");
    // `Opt := [Some(inner, I64)]`, read at `Opt([A, B])`, built as `Opt([A])`.
    const narrow = try f.types.nominalTy("Opt", try f.types.tagUnionTy(&.{.{ .name = "Some", .payload = &.{ inner_narrow, i64_ty } }}));
    const wide = try f.types.nominalTy("Opt", try f.types.tagUnionTy(&.{.{ .name = "Some", .payload = &.{ inner_wide, i64_ty } }}));
    var rows: [2]RowId = undefined;
    for (&rows, [2]TyId{ narrow, wide }, [2]TyId{ inner_narrow, inner_wide }) |*row, ty, inner| {
        row.* = try f.b.beginRow(&.{i64_ty}, ty);
        const payload = try f.b.tag(inner, a, &.{});
        const backing = try f.types.unfold(ty);
        try f.b.endRow(.{ .value = &.{try f.b.wrap(ty, try f.b.tag(backing, some, &.{ payload, Ref.rowParam(0) }))} });
    }
    const root = try f.b.beginRow(&.{i64_ty}, wide);
    try f.b.endRow(.{ .value = &.{try f.b.callRowAt(rows[0], &.{Ref.rowParam(0)}, wide)} });

    var got: std.Io.Writer.Allocating = .init(testing.allocator);
    defer got.deinit();
    var want: std.Io.Writer.Allocating = .init(testing.allocator);
    defer want.deinit();
    const got_digest = try inlinedForm(&f, root, &got);
    const want_digest = try inlinedForm(&f, rows[1], &want);
    try testing.expectEqualStrings(
        \\row r0 (I64) -> Opt
        \\  n0 = tag A() : [A, B]
        \\  n1 = tag Some(n0, p0) : [Some([A, B], I64)]
        \\  n2 = wrap(n1) : Opt
        \\  value n2
        \\
    , got.written());
    try testing.expectEqualStrings(want.written(), got.written());
    try testing.expectEqual(want_digest, got_digest);
}

test "V2: a value another node also reads keeps its own type when the call is read at a wider union" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const inner_narrow = try f.types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{} } });
    const inner_wide = try f.types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{} }, .{ .name = "C", .payload = &.{} } });
    const narrow = try f.types.tagUnionTy(&.{.{ .name = "Some", .payload = &.{ inner_narrow, i64_ty } }});
    const wide = try f.types.tagUnionTy(&.{.{ .name = "Some", .payload = &.{ inner_wide, i64_ty } }});
    const names = [_]types_mod.NameId{ try f.types.name("A"), try f.types.name("B") };
    // `pick = |n| { s = if n < 1 { B } else { A }; Some(s, match s { A => 1, B => 2 }) }`:
    // the end demands `s` at `[A, B, C]`, and the match reads it at `[A, B]`.
    const pick = try f.b.beginRow(&.{i64_ty}, narrow);
    const c = try f.b.call(.i64, .is_lt, &.{ Ref.rowParam(0), try f.b.litInt(i64_ty, 1) });
    const no = try f.b.openArm(c, 0);
    try f.b.close(.{ .value = &.{try f.b.tag(inner_narrow, names[1], &.{})} });
    const yes = try f.b.openArm(c, 1);
    try f.b.close(.{ .value = &.{try f.b.tag(inner_narrow, names[0], &.{})} });
    const s = try f.b.switchOn(c, &.{ no, yes }, &.{}, &.{inner_narrow}, &.{});
    var arms: [2]ir.RegionId = undefined;
    for (&arms, names, 1..) |*arm, name, value| {
        arm.* = try f.b.openTagArm(s, name);
        try f.b.close(.{ .value = &.{try f.b.litInt(i64_ty, @intCast(value))} });
    }
    const read = try f.b.tagSwitchOn(s, &names, &arms, &.{}, &.{i64_ty});
    try f.b.endRow(.{ .value = &.{try f.b.tag(narrow, try f.types.name("Some"), &.{ s, read })} });
    const root = try f.b.beginRow(&.{i64_ty}, wide);
    try f.b.endRow(.{ .value = &.{try f.b.callRowAt(pick, &.{Ref.rowParam(0)}, wide)} });

    var got: std.Io.Writer.Allocating = .init(testing.allocator);
    defer got.deinit();
    _ = try inlinedForm(&f, root, &got);
    // `n4` stays at `[A, B]`, which the match needs, and conforms to the slot.
    try testing.expectEqualStrings(
        \\row r0 (I64) -> [Some([A, B, C], I64)]
        \\  n0 = 1 : I64
        \\  n1 = Num.I64.is_lt(p0, n0) : Bool
        \\  n4 = switch n1 : [A, B]
        \\    arm 0
        \\      n2 = tag B() : [A, B]
        \\      value n2
        \\    arm 1
        \\      n3 = tag A() : [A, B]
        \\      value n3
        \\  n6 = switch n4 : I64
        \\    arm 0
        \\      value n0
        \\    arm 1
        \\      n5 = 2 : I64
        \\      value n5
        \\  n7 = tag Some(n4, n6) : [Some([A, B, C], I64)]
        \\  value n7
        \\
    , got.written());
}
