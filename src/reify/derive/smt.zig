//! The SMT-LIB encoding of step 3 (`roc-reify-rule-derivation.md` 3.3).
//!
//! Each term becomes a defined bit and its value's parts, following the
//! most-defined semantics of 2.1, and a strict bit: whether strict
//! evaluation of the term runs without a crash. A variable gets free parts,
//! and a component of a construction may be undefined on its own.
//!
//! | Sort | Parts |
//! |---|---|
//! | `Bool`, integers | `v` |
//! | `[A(I64), B]` | `a` (the tag is `A`), `pd`, `pv` (the payload's defined bit and value) |
//! | `{ x : I64, y : Bool }`, `(I64, Bool)` | `xd`, `xv`, `yd`, `yv` |
//! | the nominal `N` over `I64` | `v`, its backing value |

const std = @import("std");
const reify = @import("reify");
const term = @import("term.zig");
const sig_mod = @import("sig.zig");

const Allocator = std.mem.Allocator;
const Term = term.Term;
const Sort = sig_mod.Sort;
const IntTy = reify.types.IntTy;

/// A side condition a proof assumes, over a term variable.
pub const Assume = union(enum) {
    /// The variable's value is defined, with every component.
    defined: term.Var,
    /// The variable is defined and not zero.
    nonzero: term.Var,
};

/// What a query asks.
pub const Query = enum {
    /// Satisfiable when the two terms differ somewhere.
    differ,
    /// Satisfiable when strict evaluation of the first runs and of the second crashes.
    crashes_more,
};

/// What encoding can fail with: the script is written to memory.
pub const Error = Allocator.Error || std.Io.Writer.Error;

const Val = struct {
    d: []const u8,
    parts: [4][]const u8 = @splat(""),
    /// Strict evaluation does not crash.
    sd: []const u8,
};

const Encoder = struct {
    arena: Allocator,
    out: *std.Io.Writer,
    vars: sig_mod.Vars,
    width: IntTy,
    next: u32 = 0,

    fn print(self: *Encoder, comptime fmt: []const u8, args: anytype) Error![]const u8 {
        return std.fmt.allocPrint(self.arena, fmt, args);
    }

    fn bv(self: *Encoder) Error![]const u8 {
        return self.print("(_ BitVec {d})", .{self.width.bits()});
    }

    fn define(self: *Encoder, ty: []const u8, expr: []const u8) Error![]const u8 {
        const name = try self.print("n{d}", .{self.next});
        self.next += 1;
        try self.out.print("(define-fun {s} () {s} {s})\n", .{ name, ty, expr });
        return name;
    }

    fn partTy(self: *Encoder, sort: Sort, i: usize) Error![]const u8 {
        return switch (sort) {
            .bool => "Bool",
            .i64, .nominal_i64 => self.bv(),
            .union_ab => if (i == 2) self.bv() else "Bool",
            .record_xy, .tuple_ib => if (i == 1) self.bv() else "Bool",
            .f64, .str, .union_abc, .list_i64 => unreachable, // only the sorts the encoder supports reach it (no f64, str, union_abc or list_i64)
        };
    }

    fn partCount(sort: Sort) usize {
        return switch (sort) {
            .bool, .i64, .nominal_i64 => 1,
            .union_ab => 3,
            .record_xy, .tuple_ib => 4,
            .f64, .str, .union_abc, .list_i64 => unreachable, // only the sorts the encoder supports reach it (no f64, str, union_abc or list_i64)
        };
    }

    fn lit(self: *Encoder, n: i64) Error![]const u8 {
        const bits = self.width.bits();
        const mask: u128 = if (bits == 128) std.math.maxInt(u128) else (@as(u128, 1) << @intCast(bits)) - 1;
        const unsigned: u128 = @as(u128, @bitCast(@as(i128, n))) & mask;
        return self.print("(_ bv{d} {d})", .{ unsigned, bits });
    }

    /// Declare variable `k`'s parts.
    fn declare(self: *Encoder, k: term.Var) Error!void {
        const sort = self.vars.of(k);
        try self.out.print("(declare-const x{d}_d Bool)\n", .{k});
        for (0..partCount(sort)) |i| try self.out.print("(declare-const x{d}_{d} {s})\n", .{ k, i, try self.partTy(sort, i) });
    }

    fn varVal(self: *Encoder, k: term.Var) Error!Val {
        const sort = self.vars.of(k);
        var v: Val = .{ .d = try self.print("x{d}_d", .{k}), .sd = undefined };
        for (0..partCount(sort)) |i| v.parts[i] = try self.print("x{d}_{d}", .{ k, i });
        v.sd = try self.deepDefined(sort, v);
        return v;
    }

    fn deepDefined(self: *Encoder, sort: Sort, v: Val) Error![]const u8 {
        return switch (sort) {
            .bool, .i64, .nominal_i64 => v.d,
            .union_ab => self.print("(and {s} (=> {s} {s}))", .{ v.d, v.parts[0], v.parts[1] }),
            .record_xy, .tuple_ib => self.print("(and {s} {s} {s})", .{ v.d, v.parts[0], v.parts[2] }),
            .f64, .str, .union_abc, .list_i64 => unreachable, // only the sorts the encoder supports reach it (no f64, str, union_abc or list_i64)
        };
    }

    /// Whether `a` and `b`, both of `sort`, are one value: ⊥ equals only ⊥.
    fn same(self: *Encoder, sort: Sort, a: Val, b: Val) Error![]const u8 {
        const inner = switch (sort) {
            .bool, .i64, .nominal_i64 => try self.print("(= {s} {s})", .{ a.parts[0], b.parts[0] }),
            .union_ab => try self.print("(and (= {s} {s}) (=> {s} (and (= {s} {s}) (=> {s} (= {s} {s})))))", .{ a.parts[0], b.parts[0], a.parts[0], a.parts[1], b.parts[1], a.parts[1], a.parts[2], b.parts[2] }),
            .record_xy, .tuple_ib => try self.print("(and (= {s} {s}) (=> {s} (= {s} {s})) (= {s} {s}) (=> {s} (= {s} {s})))", .{ a.parts[0], b.parts[0], a.parts[0], a.parts[1], b.parts[1], a.parts[2], b.parts[2], a.parts[2], a.parts[3], b.parts[3] }),
            .f64, .str, .union_abc, .list_i64 => unreachable, // only the sorts the encoder supports reach it (no f64, str, union_abc or list_i64)
        };
        return self.print("(and (= {s} {s}) (=> {s} {s}))", .{ a.d, b.d, a.d, inner });
    }

    fn val(self: *Encoder, sort: Sort, d: []const u8, parts: []const []const u8, sd: []const u8) Error!Val {
        var v: Val = .{ .d = try self.define("Bool", d), .sd = try self.define("Bool", sd) };
        for (parts, 0..) |p, i| v.parts[i] = try self.define(try self.partTy(sort, i), p);
        return v;
    }

    fn signed(self: *const Encoder) bool {
        return self.width.signed();
    }

    fn encode(self: *Encoder, t: Term) Error!Val {
        const x = switch (t) {
            .var_ => |k| return self.varVal(k),
            .app => |x| x,
        };
        const sort = sig_mod.sortOf(self.vars, t);
        switch (x.sym.op) {
            .lit => {
                const v = if (x.sym.lit) |b| (if (b) "true" else "false") else try self.lit(x.sym.int.?);
                return self.val(sort, "true", &.{v}, "true");
            },
            .prim => {
                const a = try self.encode(x.args[0]);
                const m = x.sym.method.?;
                if (m == .not) return self.val(sort, a.d, &.{try self.print("(not {s})", .{a.parts[0]})}, a.sd);
                // An associative chain has any number of operands (N15a), and its
                // SMT-LIB op is left-associative over them; every other builtin has two.
                var ds: std.ArrayList(u8) = .empty;
                var sds: std.ArrayList(u8) = .empty;
                var parts: std.ArrayList(u8) = .empty;
                try ds.print(self.arena, "(and {s}", .{a.d});
                try sds.print(self.arena, "(and {s}", .{a.sd});
                try parts.appendSlice(self.arena, a.parts[0]);
                var b: Val = undefined;
                for (x.args[1..]) |arg| {
                    b = try self.encode(arg);
                    try ds.print(self.arena, " {s}", .{b.d});
                    try sds.print(self.arena, " {s}", .{b.sd});
                    try parts.print(self.arena, " {s}", .{b.parts[0]});
                }
                try ds.append(self.arena, ')');
                try sds.append(self.arena, ')');
                const d = ds.items;
                const sd = sds.items;
                const s = self.signed();
                // The op of a builtin that never fails, or null for checked arithmetic.
                const total: ?[]const u8 = switch (m) {
                    .is_eq => "=",
                    .is_lt => if (s) "bvslt" else "bvult",
                    .is_lte => if (s) "bvsle" else "bvule",
                    .is_gt => if (s) "bvsgt" else "bvugt",
                    .is_gte => if (s) "bvsge" else "bvuge",
                    .plus_wrap => "bvadd",
                    .times_wrap => "bvmul",
                    .bitwise_and => "bvand",
                    .bitwise_or => "bvor",
                    .bitwise_xor => "bvxor",
                    .plus, .minus, .times, .div_trunc => null,
                    .not, .concat, .len, .get => unreachable, // these methods are not total bit-vector ops and are handled by earlier prongs
                    .is_empty, .append, .map, .keep_if, .fold, .collect, .first, .last, .prepend, .single, .with_capacity, .set, .drop_first, .take_first, .repeat, .map2, .map_with_index, .fold_rev, .sum, .any, .all => unreachable, // the builtins of layer L are not enumerated signature symbols
                };
                if (total) |op| return self.val(sort, d, &.{try self.print("({s} {s})", .{ op, parts.items })}, sd);
                std.debug.assert(x.args.len == 2);
                const op = switch (m) {
                    .plus => "bvadd",
                    .minus => "bvsub",
                    .times => "bvmul",
                    .div_trunc => if (s) "bvsdiv" else "bvudiv",
                    .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect, .first, .last, .prepend, .single, .with_capacity, .set, .drop_first, .take_first, .repeat, .map2, .map_with_index, .fold_rev, .sum, .any, .all => unreachable, // the total ops were handled above, leaving only these four
                };
                const value = try self.print("({s} {s} {s})", .{ op, a.parts[0], b.parts[0] });
                // Checked arithmetic fails where the result leaves the type, which
                // SMT-LIB's overflow predicates state; the same test at twice the
                // width is exact too, but `z3` times out on it for `times` and `//`.
                const sign = if (s) "s" else "u";
                const overflows = switch (m) {
                    .plus => try self.print("(bv{s}addo {s} {s})", .{ sign, a.parts[0], b.parts[0] }),
                    .minus => try self.print("(bv{s}subo {s} {s})", .{ sign, a.parts[0], b.parts[0] }),
                    .times => try self.print("(bv{s}mulo {s} {s})", .{ sign, a.parts[0], b.parts[0] }),
                    // An unsigned quotient never leaves its type.
                    .div_trunc => if (s) try self.print("(bvsdivo {s} {s})", .{ a.parts[0], b.parts[0] }) else "false",
                    .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect, .first, .last, .prepend, .single, .with_capacity, .set, .drop_first, .take_first, .repeat, .map2, .map_with_index, .fold_rev, .sum, .any, .all => unreachable, // the overflow check applies only to plus, minus, times and div_trunc
                };
                const in_range = try self.print("(not {s})", .{overflows});
                const ok = try self.define("Bool", if (m == .div_trunc) try self.print("(and (not (= {s} {s})) {s})", .{ b.parts[0], try self.lit(0), in_range }) else in_range);
                return self.val(sort, try self.print("(and {s} {s})", .{ d, ok }), &.{value}, try self.print("(and {s} {s})", .{ sd, ok }));
            },
            .and_, .or_ => {
                // Short-circuit And and Or are associative, so a chain folds to the right.
                const a = try self.encode(x.args[0]);
                const b = if (x.args.len == 2) try self.encode(x.args[1]) else try self.encode(.{ .app = .{ .sym = x.sym, .args = x.args[1..] } });
                const is_and = x.sym.op == .and_;
                // The value that decides: False for And, True for Or.
                const decide_a = try self.print("(and {s} {s})", .{ a.d, if (is_and) try self.print("(not {s})", .{a.parts[0]}) else a.parts[0] });
                const decide_b = try self.print("(and {s} {s})", .{ b.d, if (is_and) try self.print("(not {s})", .{b.parts[0]}) else b.parts[0] });
                const d = try self.print("(or {s} {s} (and {s} {s}))", .{ decide_a, decide_b, a.d, b.d });
                const v = if (is_and)
                    try self.print("(and {s} {s} {s} {s})", .{ a.d, a.parts[0], b.d, b.parts[0] })
                else
                    try self.print("(or (and {s} {s}) (and {s} {s}))", .{ a.d, a.parts[0], b.d, b.parts[0] });
                const sd = if (is_and)
                    try self.print("(and {s} (or (not {s}) {s}))", .{ a.sd, a.parts[0], b.sd })
                else
                    try self.print("(and {s} (or {s} {s}))", .{ a.sd, a.parts[0], b.sd });
                return self.val(sort, d, &.{v}, sd);
            },
            .switch_ => if (term.litKeys(x)) |n| return self.litSwitch(x, n, sort) else {
                const c = try self.encode(x.args[0]);
                const f = try self.encode(x.args[1]);
                const tr = try self.encode(x.args[2]);
                // Whether the second arm is taken: `True`, or tag `B`.
                const second = switch (sig_mod.sortOf(self.vars, x.args[0])) {
                    .bool => c.parts[0],
                    .union_ab => try self.print("(not {s})", .{c.parts[0]}),
                    .i64, .record_xy, .f64, .str, .union_abc, .list_i64, .tuple_ib, .nominal_i64 => unreachable, // a switch scrutinee is a Bool or a two-tag union in signatures
                };
                const d = try self.print("(ite {s} (ite {s} {s} {s}) (and {s} {s}))", .{ c.d, second, tr.d, f.d, f.d, try self.same(sort, f, tr) });
                var parts: [4][]const u8 = undefined;
                const n = partCount(sort);
                for (0..n) |i| parts[i] = try self.print("(ite (and {s} {s}) {s} {s})", .{ c.d, second, tr.parts[i], f.parts[i] });
                const sd = try self.print("(and {s} (ite {s} {s} {s}))", .{ c.sd, second, tr.sd, f.sd });
                return self.val(sort, d, parts[0..n], sd);
            },
            .tag => {
                if (x.sym.index.? == 1) return self.val(sort, "true", &.{ "false", "false", try self.lit(0) }, "true");
                const p = try self.encode(x.args[0]);
                return self.val(sort, "true", &.{ "true", p.d, p.parts[0] }, p.sd);
            },
            .payload => {
                const u = try self.encode(x.args[0]);
                return self.val(sort, try self.print("(and {s} {s} {s})", .{ u.d, u.parts[0], u.parts[1] }), &.{u.parts[2]}, try self.print("(and {s} {s})", .{ u.sd, u.parts[0] }));
            },
            .record, .tuple => {
                const a = try self.encode(x.args[0]);
                const b = try self.encode(x.args[1]);
                return self.val(sort, "true", &.{ a.d, a.parts[0], b.d, b.parts[0] }, try self.print("(and {s} {s})", .{ a.sd, b.sd }));
            },
            .field, .index => {
                const r = try self.encode(x.args[0]);
                const k: usize = x.sym.index.? * 2;
                return self.val(sort, try self.print("(and {s} {s})", .{ r.d, r.parts[k] }), &.{r.parts[k + 1]}, r.sd);
            },
            // A nominal's parts are its backing value's.
            .wrap, .unwrap => return self.encode(x.args[0]),
            .crash, .derived, .list, .closure, .elem, .opt_field, .call, .for_range, .for_list, .loop, .lambda, .apply => unreachable, // signature terms are built only from the enumerated symbols (derive/enumerate.zig)
        }
    }

    // A literal switch takes the arm of the first key equal to its
    // scrutinee, else its default arm. Where the scrutinee or a key is
    // undefined it is defined when every arm is, with one value.
    fn litSwitch(self: *Encoder, x: @FieldType(Term, "app"), n: u32, sort: Sort) Error!Val {
        const c = try self.encode(x.args[0]);
        const keys = try self.arena.alloc(Val, n);
        for (keys, x.args[1 .. 1 + n]) |*k, t| k.* = try self.encode(t);
        const arms = try self.arena.alloc(Val, n + 1);
        for (arms, x.args[1 + n ..]) |*a, t| a.* = try self.encode(t);
        var decided: []const u8 = c.d;
        for (keys) |k| decided = try self.print("(and {s} {s})", .{ decided, k.d });
        var agree: []const u8 = arms[0].d;
        for (arms[1..]) |a| agree = try self.print("(and {s} {s} {s})", .{ agree, a.d, try self.same(sort, arms[0], a) });
        // Each part, and the defined and strict bits, chosen by the keys in order.
        const Pick = struct {
            fn chain(e: *Encoder, cv: []const u8, ks: []const Val, xs: []const []const u8) Error![]const u8 {
                var out = xs[xs.len - 1];
                var i = ks.len;
                while (i > 0) {
                    i -= 1;
                    out = try e.print("(ite (= {s} {s}) {s} {s})", .{ cv, ks[i].parts[0], xs[i], out });
                }
                return out;
            }
        };
        const texts = try self.arena.alloc([]const u8, n + 1);
        for (texts, arms) |*t, a| t.* = a.d;
        const d = try self.print("(ite {s} {s} {s})", .{ decided, try Pick.chain(self, c.parts[0], keys, texts), agree });
        var parts: [4][]const u8 = undefined;
        const count = partCount(sort);
        for (0..count) |i| {
            for (texts, arms) |*t, a| t.* = a.parts[i];
            parts[i] = try self.print("(ite {s} {s} {s})", .{ decided, try Pick.chain(self, c.parts[0], keys, texts), arms[0].parts[i] });
        }
        for (texts, arms) |*t, a| t.* = a.sd;
        var sd: []const u8 = c.sd;
        for (keys) |k| sd = try self.print("(and {s} {s})", .{ sd, k.sd });
        sd = try self.print("(and {s} {s})", .{ sd, try Pick.chain(self, c.parts[0], keys, texts) });
        return self.val(sort, d, parts[0..count], sd);
    }
};

fn collectVars(t: Term, seen: []bool) void {
    switch (t) {
        .var_ => |v| seen[v] = true,
        .app => |x| for (x.args) |a| collectVars(a, seen),
    }
}

/// The variables `l` and `r` read, in increasing order.
pub fn varsOf(arena: Allocator, vars: sig_mod.Vars, l: Term, r: Term) Allocator.Error![]term.Var {
    const seen = try arena.alloc(bool, vars.sorts.items.len);
    @memset(seen, false);
    collectVars(l, seen);
    collectVars(r, seen);
    var out: std.ArrayList(term.Var) = .empty;
    for (seen, 0..) |s, v| if (s) try out.append(arena, @intCast(v));
    return out.toOwnedSlice(arena);
}

/// The SMT-LIB script of `query` over `l` and `r` at integer `width`, under
/// `assume`. It asks for the variables' parts after `check-sat`, so a
/// satisfiable answer comes with its counterexample.
pub fn script(arena: Allocator, vars: sig_mod.Vars, l: Term, r: Term, assume: []const Assume, width: IntTy, query: Query) Error![]const u8 {
    var out: std.Io.Writer.Allocating = .init(arena);
    const w = &out.writer;
    try w.writeAll("(set-option :produce-models true)\n(set-logic QF_BV)\n");
    var e: Encoder = .{ .arena = arena, .out = w, .vars = vars, .width = width };
    const used = try varsOf(arena, vars, l, r);
    for (used) |v| try e.declare(v);
    const a = try e.encode(l);
    const b = try e.encode(r);
    for (assume) |c| switch (c) {
        .defined => |k| try w.print("(assert {s})\n", .{(try e.varVal(k)).sd}),
        .nonzero => |k| {
            const v = try e.varVal(k);
            try w.print("(assert (and {s} (not (= {s} {s}))))\n", .{ v.sd, v.parts[0], try e.lit(0) });
        },
    };
    switch (query) {
        .differ => try w.print("(assert (not {s}))\n", .{try e.same(sig_mod.sortOf(vars, l), a, b)}),
        .crashes_more => try w.print("(assert (and {s} (not {s})))\n", .{ a.sd, b.sd }),
    }
    try w.writeAll("(check-sat)\n");
    if (used.len > 0) {
        try w.writeAll("(get-value (");
        for (used) |v| {
            try w.print(" x{d}_d", .{v});
            for (0..Encoder.partCount(vars.of(v))) |i| try w.print(" x{d}_{d}", .{ v, i });
        }
        try w.writeAll("))\n");
    }
    return out.written();
}
