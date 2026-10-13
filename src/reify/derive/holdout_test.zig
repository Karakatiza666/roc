//! Criterion 5 of the gate (`roc-reify-rule-derivation.md` 6.1): the
//! refactor pairs of M4 in S1's scope, which no run uses as a seed or a
//! witness, have one normal form. Over S1, x0 and x1 are `Bool`, x2 and x3
//! are `I64`, x4 and x5 are `[A(I64), B]`, x6 and x7 are `{ x : I64, y : Bool }`,
//! x8 and x9 are `(I64, Bool)`, x10 and x11 are the nominal `N` over `I64`,
//! and `switch_(c, e, t)` is `if c t else e`: arm 0 is the `False` arm.

const std = @import("std");
const reify = @import("reify");
const term = @import("term.zig");
const sig_mod = @import("sig.zig");

const Pair = struct {
    refactor: []const u8,
    lhs: []const u8,
    rhs: []const u8,
    /// The rule still to come that joins the pair; until it lands the two
    /// sides stay apart, and a pair that meets names its entry to update.
    open: ?[]const u8 = null,
};

/// The holdout of 6.1, frozen in the gate record.
pub const pairs = [_]Pair{
    .{ .refactor = "and as its if", .lhs = "switch_(x0, False, x1)", .rhs = "and_(x0, x1)" },
    .{ .refactor = "or as its if", .lhs = "switch_(x0, x1, True)", .rhs = "or_(x0, x1)" },
    .{ .refactor = "nested ifs as and", .lhs = "switch_(x0, x3, switch_(x1, x3, x2))", .rhs = "switch_(and_(x0, x1), x3, x2)" },
    .{ .refactor = "nested ifs as or", .lhs = "switch_(x0, switch_(x1, x3, x2), x2)", .rhs = "switch_(or_(x0, x1), x3, x2)" },
    .{ .refactor = "if a False else b", .lhs = "switch_(x0, x1, False)", .rhs = "and_(Bool.not(x0), x1)" },
    .{ .refactor = "if a b else True", .lhs = "switch_(x0, True, x1)", .rhs = "or_(Bool.not(x0), x1)" },
    .{ .refactor = "a >= b as !(a < b)", .lhs = "Num.I64.is_gte(x2, x3)", .rhs = "Bool.not(Num.I64.is_lt(x2, x3))" },
    .{ .refactor = "a > b as b < a", .lhs = "Num.I64.is_gt(x2, x3)", .rhs = "Num.I64.is_lt(x3, x2)" },
    .{ .refactor = "negate and swap", .lhs = "switch_(Bool.not(x0), x2, x3)", .rhs = "switch_(x0, x3, x2)" },
    .{ .refactor = "negate a comparison and swap", .lhs = "switch_(Bool.not(Num.I64.is_lt(x2, x3)), x2, x3)", .rhs = "switch_(Num.I64.is_lt(x2, x3), x3, x2)" },
    .{ .refactor = "flip a comparison under an if", .lhs = "switch_(Num.I64.is_gte(x2, x3), x2, x3)", .rhs = "switch_(Num.I64.is_lt(x2, x3), x3, x2)" },
    .{ .refactor = "nested ifs under a negation as and", .lhs = "switch_(Bool.not(x0), x3, switch_(x1, x3, x2))", .rhs = "switch_(and_(Bool.not(x0), x1), x3, x2)" },
    .{ .refactor = "De Morgan in a value", .lhs = "Bool.not(and_(x0, x1))", .rhs = "or_(Bool.not(x0), Bool.not(x1))" },
    .{ .refactor = "build a record and read it back", .lhs = "field#0(record(x2, x0))", .rhs = "x2" },
    .{ .refactor = "build a tag and read it back", .lhs = "payload#0(tag#0(x2))", .rhs = "x2" },
    .{ .refactor = "build a tuple and read it back", .lhs = "index#1(tuple(x2, x0))", .rhs = "x0" },
    .{ .refactor = "wrap a value in a nominal and unwrap it", .lhs = "Num.I64.plus(unwrap(wrap(x2)), 1)", .rhs = "Num.I64.plus(x2, 1)" },
    .{ .refactor = "match on a known tag", .lhs = "switch_(tag#0(x2), x3, Num.I64.plus(x2, 1))", .rhs = "x3" },
    .{ .refactor = "match on a known payload-less tag", .lhs = "switch_(tag#1(), x2, x3)", .rhs = "x3" },
    .{ .refactor = "repeat a test a dominating branch made", .lhs = "switch_(x0, x3, switch_(x0, x3, x2))", .rhs = "switch_(x0, x3, x2)" },
    .{ .refactor = "name a constant computed from literals", .lhs = "Num.I64.plus(1, 1)", .rhs = "2" },
    .{ .refactor = "De Morgan in a condition", .lhs = "switch_(or_(Bool.not(x0), Bool.not(x1)), x2, x3)", .rhs = "switch_(and_(x0, x1), x3, x2)" },
};

test "criterion 5: every holdout pair has one normal form, but those still open" {
    const testing = std.testing;
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const vars = try sig_mod.Vars.base(a, sig_mod.find("S1").?);
    const none: [reify.rules.count]bool = @splat(false);
    var failed = false;
    for (pairs) |p| {
        const l = try sig_mod.normalize(a, testing.allocator, vars, try term.parse(a, p.lhs), &none);
        const r = try sig_mod.normalize(a, testing.allocator, vars, try term.parse(a, p.rhs), &none);
        if (l.eql(r) == (p.open == null)) continue;
        failed = true;
        if (p.open) |rule| {
            std.debug.print("holdout pair `{s}` now meets: {s} landed, so the pair's entry is no longer open\n", .{ p.refactor, rule });
            continue;
        }
        var w: std.Io.Writer.Allocating = .init(a);
        try term.write(&w.writer, l);
        try w.writer.writeAll(" versus ");
        try term.write(&w.writer, r);
        std.debug.print("holdout pair `{s}` normalizes apart: {s}\n", .{ p.refactor, w.written() });
    }
    try testing.expect(!failed);
}
