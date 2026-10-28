//! A generator of small typed Roc functions for the reification fuzzers, L4
//! and L5 of `roc-reify-normalization-plan.md` 5.1.
//!
//! One input gives one term: small typed constructs over `U64` and `Bool`,
//! composed at random. The term is printed twice. Each print picks its own
//! spelling at every construct, from the refactors in R:
//!
//! | Milestone | Refactors |
//! |---|---|
//! | M1 | renamed locals, operator or method, literal spelling, parentheses, `and` and `or` or the `if` they mean, `??` or its `match`, a binding or a `var`, an `expect` that describes as nothing, `return` last |
//! | M2 | two independent bindings in either order, a value bound twice, an unused binding, a binding moved into each branch that reads it |
//! | M4 | an `if` as a `match` on `Bool` in either arm order, an `if` on `c` as an `if` on `!c` with the branches swapped, an `if` on `x == k` as a `match` on the literal `k`, `a < b` as `b > a`, `!(a < b)` as `a >= b` |
//! | M5 | an `if` on `a and b` or `a or b` as nested `if`s that repeat a leaf arm, `(a and b) and c` or `(a or b) or c` regrouped, `!(a and b)` as `!a or !b` and `!(a or b)` as `!a and !b` |
//! | M6 | a `for` over a list, over its `.iter()`, or a `while` over its indices |
//! | M7 | a loop `var` as one scalar, as a record or as a tuple that carries a field nothing changes; a private helper that takes `a, b`, `{ a, b }`, `(a, b)`, or either destructured, called twice |
//! | M11 | a literal operand of `+`, `*` and `==` first or last; a sum over `0..=n` under a test that bounds `n`, as a `for` over the range or a `while $i <= n` |
//! | M12 | a sum over `0..<n` as a `for` over the range, a `while $i < n`, or a `while !$done` whose `else` sets the flag; a second counter from `j0` as a `var` stepped by 1 with the index, or as `i + j0` |
//! | M13 | an M7 helper defined in the app's own module, or in a module `Lib` of another package that the app calls it through, outside every cut (N8l) |
//!
//! The two prints must describe as one normal form (L4), and the normal form
//! must compute what Roc computes wherever Roc does not crash (L5, C2).
//! `minus` crashes where its result is below zero, so some terms crash, and
//! an unused or moved binding of one crashes in one print and not the other.
//!
//! Every userspace name comes from `fresh`; builtin names are the only names
//! written here (`test/fuzzing/README.md`).

const std = @import("std");

const Allocator = std.mem.Allocator;

/// What a case may use.
pub const Options = struct {
    /// The constructs of M7 (a loop `var` as a record or tuple, a private
    /// helper that takes its arguments in several shapes). With it off, a
    /// case is the one the generator made before M7 for the same bytes.
    m7: bool = true,
    /// The constructs of M10 (a sum written as `List.fold`, a test of the
    /// list being empty). A case with them is compared in the `lawful` view,
    /// where layer L makes the spellings meet.
    m10: bool = false,
    /// The constructs of M11 (a literal operand on either side, a sum over
    /// an inclusive range that a test bounds), whose spellings meet through
    /// N15c and through N13u's intervals.
    m11: bool = false,
    /// The constructs of M12 (a loop controlled by a `$done` flag, a second
    /// counter stepped with the index), whose spellings meet through N11n
    /// and N11o.
    m12: bool = false,
    /// The choice of M13: an M7 helper in the app, or in a package `lib`,
    /// which the walk reads by its body because no cut lists it (N8l).
    m13: bool = false,
};

/// Bytes the generator reads its choices from. Past the end it reads zeros,
/// so every input gives a term.
pub const Reader = struct {
    bytes: []const u8,
    at: usize = 0,

    fn byte(self: *Reader) u8 {
        if (self.at >= self.bytes.len) return 0;
        defer self.at += 1;
        return self.bytes[self.at];
    }

    /// A choice among `n` options.
    fn pick(self: *Reader, n: u8) u8 {
        return self.byte() % n;
    }
};

/// The two types a term has.
pub const Type = enum { u64_, bool_ };

const Node = union(enum) {
    lit_u64: u64,
    lit_bool: bool,
    /// A `U64` field of the input, by index.
    field_u64: u8,
    field_bool,
    /// A binding in scope, by index into the scope.
    local: u16,
    plus: [2]*const Node,
    /// `a - b`, which crashes where `b` is greater than `a`.
    minus: [2]*const Node,
    /// `a * k` with a literal `k` from 1 to 3, so no value grows past `U64`.
    times: struct { value: *const Node, k: u64 },
    is_lt: [2]*const Node,
    is_eq: [2]*const Node,
    is_ne: [2]*const Node,
    and_: [2]*const Node,
    or_: [2]*const Node,
    not: *const Node,
    if_: struct { cond: *const Node, then: *const Node, other: *const Node },
    /// `name = value` then `body`, with `name` bound at scope index `slot`.
    let: struct { value: *const Node, body: *const Node, slot: u16 },
    /// A `Try` built by `if`, read by `??`.
    default: struct { cond: *const Node, ok: *const Node, fallback: *const Node, tag: u32 },
    /// A `for` over the list field that adds `step` to an accumulator per
    /// item; `step` sees the item at scope index `slot`.
    sum: struct { start: *const Node, step: *const Node, slot: u16 },
    /// A private helper `|p, q| p + q * k` called twice, as `h(x1, y1) + h(x2, y2)`.
    twice: struct { args: [4]*const Node, k: u64 },
    /// Whether the list field is empty, or with `negated` whether it is not.
    empty: struct { negated: bool },
    /// `if n < limit { the sum of step over i in 0..=n } else other`, with
    /// `n` a `U64` field or literal; `step` sees `i` at scope index `slot`.
    upto: struct { bound: *const Node, limit: u64, init: u64, step: *const Node, slot: u16, other: *const Node },
    /// `if n < limit { the sum of step over i in 0..<n } else other`, with
    /// `n` a `U64` field or literal; `step` sees `i` at scope index `slot`
    /// and the second counter `j = i + j0` at `slot + 1`.
    counted: struct { bound: *const Node, limit: u64, init: u64, j0: u64, step: *const Node, slot: u16, other: *const Node },
};

/// One generated case: the module text and the input it is run on.
pub const Case = struct {
    /// The module body: the input's type, the two prints, and the constant
    /// Roc computes the answer in.
    source: []u8,
    /// The parameter names of the two prints, which the driver finds the
    /// lambdas by, and the name of the constant Roc computes the answer in.
    left_param: []u8,
    right_param: []u8,
    answer: []u8,
    input: Input,
    /// Set where the case may hold the constructs of M10.
    lawful: bool,
    /// The body of the module `Lib` of a package `lib`, the helpers M13 put
    /// there, or empty where the case calls into no other package.
    lib_source: []u8,

    pub fn deinit(self: *Case, gpa: Allocator) void {
        gpa.free(self.source);
        gpa.free(self.lib_source);
        gpa.free(self.left_param);
        gpa.free(self.right_param);
        gpa.free(self.answer);
        gpa.free(self.input.items);
    }
};

/// The input record's value, in the record type's field order: the two
/// `U64` fields, the `Bool` field, then the list field.
pub const Input = struct {
    a: u64,
    b: u64,
    flag: bool,
    items: []u64,
};

const max_depth = 4;
const max_scope = 16;

const Scope = struct {
    types: [max_scope]Type = undefined,
    len: u16 = 0,
};

/// Builds one term from a reader.
const Builder = struct {
    arena: Allocator,
    reader: *Reader,
    /// A second stream of choices, so that what M7 adds changes no choice the
    /// older constructs read from `reader`.
    extra: *Reader,
    /// Set inside a `twice`, whose arguments hold none.
    inside_twice: bool = false,
    options: Options = .{},

    fn node(self: *Builder, value: Node) Allocator.Error!*const Node {
        const n = try self.arena.create(Node);
        n.* = value;
        return n;
    }

    fn local(self: *Builder, scope: *const Scope, ty: Type) ?u16 {
        var found: [max_scope]u16 = undefined;
        var count: u8 = 0;
        for (scope.types[0..scope.len], 0..) |t, i| {
            if (t == ty) {
                found[count] = @intCast(i);
                count += 1;
            }
        }
        if (count == 0) return null;
        return found[self.reader.pick(count)];
    }

    fn term(self: *Builder, ty: Type, scope: Scope, depth: u8) Allocator.Error!*const Node {
        if (depth >= max_depth) return self.leaf(ty, &scope);
        return switch (ty) {
            .u64_ => self.u64Term(scope, depth),
            .bool_ => self.boolTerm(scope, depth),
        };
    }

    fn leaf(self: *Builder, ty: Type, scope: *const Scope) Allocator.Error!*const Node {
        // M7: some `U64` leaves are a helper called twice, which the older
        // choices do not see: its arguments come from the extra stream.
        if (self.options.m7 and ty == .u64_ and !self.inside_twice and self.extra.pick(16) == 0) return self.twiceTerm(scope);
        const kind = self.reader.pick(3);
        if (kind == 0) {
            if (self.local(scope, ty)) |slot| return self.node(.{ .local = slot });
        }
        if (kind == 1) return switch (ty) {
            .u64_ => self.node(.{ .field_u64 = self.reader.pick(2) }),
            .bool_ => self.node(.field_bool),
        };
        return switch (ty) {
            .u64_ => self.node(.{ .lit_u64 = self.reader.pick(20) }),
            .bool_ => self.node(.{ .lit_bool = self.reader.pick(2) == 1 }),
        };
    }

    fn u64Term(self: *Builder, scope: Scope, depth: u8) Allocator.Error!*const Node {
        const d = depth + 1;
        // M11: a sum over an inclusive range, from the extra stream.
        if (self.options.m11 and self.extra.pick(8) == 0) return self.uptoTerm(scope, d);
        // M12: a counted sum with a second counter, from the extra stream.
        if (self.options.m12 and self.extra.pick(6) == 0) return self.countedTerm(scope, d);
        return switch (self.reader.pick(9)) {
            0 => self.leaf(.u64_, &scope),
            1 => self.node(.{ .plus = .{ try self.term(.u64_, scope, d), try self.term(.u64_, scope, d) } }),
            8 => self.node(.{ .minus = .{ try self.term(.u64_, scope, d), try self.term(.u64_, scope, d) } }),
            2 => self.node(.{ .times = .{ .value = try self.term(.u64_, scope, d), .k = 1 + @as(u64, self.reader.pick(3)) } }),
            3 => self.node(.{ .if_ = .{
                .cond = try self.term(.bool_, scope, d),
                .then = try self.term(.u64_, scope, d),
                .other = try self.term(.u64_, scope, d),
            } }),
            4, 5 => self.letTerm(.u64_, scope, d),
            6 => self.node(.{ .default = .{
                .cond = try self.term(.bool_, scope, d),
                .ok = try self.term(.u64_, scope, d),
                .fallback = try self.term(.u64_, scope, d),
                .tag = self.reader.byte(),
            } }),
            else => self.sumTerm(scope, d),
        };
    }

    fn boolTerm(self: *Builder, scope: Scope, depth: u8) Allocator.Error!*const Node {
        const d = depth + 1;
        // M10: a test of the list being empty, from the extra stream.
        if (self.options.m10 and self.extra.pick(8) == 0) return self.node(.{ .empty = .{ .negated = self.extra.pick(2) == 1 } });
        return switch (self.reader.pick(8)) {
            0 => self.leaf(.bool_, &scope),
            1 => self.node(.{ .is_lt = .{ try self.term(.u64_, scope, d), try self.term(.u64_, scope, d) } }),
            2 => self.node(.{ .is_eq = .{ try self.term(.u64_, scope, d), try self.term(.u64_, scope, d) } }),
            3 => self.node(.{ .is_ne = .{ try self.term(.u64_, scope, d), try self.term(.u64_, scope, d) } }),
            4 => self.node(.{ .and_ = .{ try self.term(.bool_, scope, d), try self.term(.bool_, scope, d) } }),
            5 => self.node(.{ .or_ = .{ try self.term(.bool_, scope, d), try self.term(.bool_, scope, d) } }),
            6 => self.node(.{ .not = try self.term(.bool_, scope, d) }),
            else => self.node(.{ .if_ = .{
                .cond = try self.term(.bool_, scope, d),
                .then = try self.term(.bool_, scope, d),
                .other = try self.term(.bool_, scope, d),
            } }),
        };
    }

    fn twiceTerm(self: *Builder, scope: *const Scope) Allocator.Error!*const Node {
        var inner: Builder = .{ .arena = self.arena, .reader = self.extra, .extra = self.extra, .inside_twice = true, .options = self.options };
        var args: [4]*const Node = undefined;
        for (&args) |*a| a.* = try inner.term(.u64_, scope.*, max_depth - 2);
        return self.node(.{ .twice = .{ .args = args, .k = 1 + @as(u64, self.extra.pick(3)) } });
    }

    fn letTerm(self: *Builder, ty: Type, scope: Scope, depth: u8) Allocator.Error!*const Node {
        if (scope.len >= max_scope) return self.leaf(ty, &scope);
        const bound: Type = if (self.reader.pick(3) == 0) .bool_ else .u64_;
        const value = try self.term(bound, scope, depth);
        var inner = scope;
        inner.types[inner.len] = bound;
        inner.len += 1;
        return self.node(.{ .let = .{ .value = value, .body = try self.term(ty, inner, depth), .slot = scope.len } });
    }

    fn uptoTerm(self: *Builder, scope: Scope, depth: u8) Allocator.Error!*const Node {
        if (scope.len >= max_scope) return self.leaf(.u64_, &scope);
        const bound = if (self.extra.pick(2) == 0)
            try self.node(.{ .field_u64 = self.extra.pick(2) })
        else
            try self.node(.{ .lit_u64 = self.extra.pick(12) });
        const limit = 1 + @as(u64, self.extra.pick(16));
        // The sum starts above the index's 0. A sum that starts at 0 and
        // steps by 1 is the index itself, which N11i merges with the
        // counter, and the counter read after the loop keeps it a `Loop`.
        const init = 1 + @as(u64, self.extra.pick(8));
        var inner = scope;
        inner.types[inner.len] = .u64_;
        inner.len += 1;
        // The step is small: it runs once per index and nests no deeper.
        const step = try self.term(.u64_, inner, max_depth - 1);
        return self.node(.{ .upto = .{ .bound = bound, .limit = limit, .init = init, .step = step, .slot = scope.len, .other = try self.term(.u64_, scope, depth) } });
    }

    fn countedTerm(self: *Builder, scope: Scope, depth: u8) Allocator.Error!*const Node {
        if (scope.len + 2 > max_scope) return self.leaf(.u64_, &scope);
        // A literal bound is above 0. Under the bound 0, N13u decides
        // `$i < 0` wherever a rebuild builds the test again, and an exiting
        // switch on a known test stays a switch, while `for i in 0..<0` stays
        // a `ForRange`: the gap of normal-form 3.11 that `while $i < 0` with
        // a dead slot shows without M12.
        const bound = if (self.extra.pick(2) == 0)
            try self.node(.{ .field_u64 = self.extra.pick(2) })
        else
            try self.node(.{ .lit_u64 = 1 + @as(u64, self.extra.pick(11)) });
        const limit = 1 + @as(u64, self.extra.pick(16));
        // The sum starts above 0, as `upto`'s does: N11i merges a sum from 0
        // stepped by 1 with the counter of a `while`, which the read after
        // the loop keeps a `Loop` (normal-form 3.11). N11o does not close
        // that gap: it reads a counter that nothing after the loop reads.
        const init = 1 + @as(u64, self.extra.pick(8));
        const j0 = @as(u64, self.extra.pick(8));
        var inner = scope;
        inner.types[inner.len] = .u64_;
        inner.types[inner.len + 1] = .u64_;
        inner.len += 2;
        // The step is small: it runs once per index and nests no deeper.
        const step = try self.term(.u64_, inner, max_depth - 1);
        return self.node(.{ .counted = .{ .bound = bound, .limit = limit, .init = init, .j0 = j0, .step = step, .slot = scope.len, .other = try self.term(.u64_, scope, depth) } });
    }

    fn sumTerm(self: *Builder, scope: Scope, depth: u8) Allocator.Error!*const Node {
        if (scope.len >= max_scope) return self.leaf(.u64_, &scope);
        const start = try self.term(.u64_, scope, depth);
        var inner = scope;
        inner.types[inner.len] = .u64_;
        inner.len += 1;
        // The step is small: a sum runs once per item and nests no deeper.
        return self.node(.{ .sum = .{ .start = start, .step = try self.term(.u64_, inner, max_depth - 1), .slot = scope.len } });
    }
};

/// The names one print gives the input and its bindings.
const Names = struct {
    param: []const u8,
    fields: [4][]const u8,
    /// Per scope index, the name bound there in this print.
    locals: [max_scope][]const u8 = undefined,
    /// Per scope index, a second name bound to the same value, if any.
    twins: [max_scope]?[]const u8 = @splat(null),
};

// Whether `n` reads the binding at scope index `slot`.
fn isLeaf(n: *const Node) bool {
    return switch (n.*) {
        .lit_u64, .lit_bool, .field_u64, .field_bool, .local => true,
        else => false,
    };
}

fn reads(n: *const Node, slot: u16) bool {
    return switch (n.*) {
        .lit_u64, .lit_bool, .field_u64, .field_bool => false,
        .local => |s| s == slot,
        .plus, .minus, .is_lt, .is_eq, .is_ne, .and_, .or_ => |pair| reads(pair[0], slot) or reads(pair[1], slot),
        .times => |t| reads(t.value, slot),
        .not => |inner| reads(inner, slot),
        .if_ => |i| reads(i.cond, slot) or reads(i.then, slot) or reads(i.other, slot),
        .let => |l| reads(l.value, slot) or reads(l.body, slot),
        .default => |d| reads(d.cond, slot) or reads(d.ok, slot) or reads(d.fallback, slot),
        .sum => |x| reads(x.start, slot) or reads(x.step, slot),
        .twice => |t| reads(t.args[0], slot) or reads(t.args[1], slot) or reads(t.args[2], slot) or reads(t.args[3], slot),
        .empty => false,
        .upto => |u| reads(u.bound, slot) or reads(u.step, slot) or reads(u.other, slot),
        .counted => |u| reads(u.bound, slot) or reads(u.step, slot) or reads(u.other, slot),
    };
}

/// Prints one term, choosing a spelling at every construct.
const Printer = struct {
    gpa: Allocator,
    out: *std.ArrayList(u8),
    choices: *Reader,
    /// The choices M7 adds, apart from `choices` so that the older ones keep their bytes.
    extra: *Reader,
    names: *Names,
    symbols: *Symbols,
    /// The private helpers this print defines at the top level, before its function.
    helpers: *std.ArrayList(u8),
    /// The helpers this print defines in the module `Lib` of another package
    /// (M13), which its calls name through `Lib.`.
    lib_helpers: *std.ArrayList(u8),
    options: Options = .{},

    fn write(self: *Printer, text: []const u8) Allocator.Error!void {
        try self.out.appendSlice(self.gpa, text);
    }

    fn print(self: *Printer, comptime fmt: []const u8, args: anytype) Allocator.Error!void {
        try self.out.print(self.gpa, fmt, args);
    }

    /// `a op b` for a commutative `op`; under M11, with a literal operand
    /// and another that is not, in some prints the literal first (N15c).
    fn commuting(self: *Printer, pair: [2]*const Node, operator: []const u8, method: []const u8) Allocator.Error!void {
        const one_literal = (pair[0].* == .lit_u64) != (pair[1].* == .lit_u64);
        if (self.options.m11 and one_literal and self.extra.pick(2) == 0) return self.two(.{ pair[1], pair[0] }, operator, method);
        return self.two(pair, operator, method);
    }

    fn two(self: *Printer, pair: [2]*const Node, operator: []const u8, method: []const u8) Allocator.Error!void {
        if (self.choices.pick(2) == 0) {
            try self.write("(");
            try self.expr(pair[0]);
            try self.print(" {s} ", .{operator});
            try self.expr(pair[1]);
            try self.write(")");
        } else {
            try self.write("(");
            try self.expr(pair[0]);
            try self.print(").{s}(", .{method});
            try self.expr(pair[1]);
            try self.write(")");
        }
    }

    /// `a < b`, in some prints as `b > a`.
    fn lessThan(self: *Printer, pair: [2]*const Node) Allocator.Error!void {
        switch (self.choices.pick(4)) {
            0 => try self.two(pair, "<", "is_lt"),
            1 => {
                try self.write("(");
                try self.expr(pair[0]);
                try self.write(").is_lt(");
                try self.expr(pair[1]);
                try self.write(")");
            },
            2 => try self.two(.{ pair[1], pair[0] }, ">", "is_gt"),
            else => {
                try self.write("(");
                try self.expr(pair[1]);
                try self.write(").is_gt(");
                try self.expr(pair[0]);
                try self.write(")");
            },
        }
    }

    fn expr(self: *Printer, n: *const Node) Allocator.Error!void {
        // Reformatting: parentheses around any expression.
        const wrapped = self.choices.pick(4) == 0;
        if (wrapped) try self.write("(");
        try self.bare(n);
        if (wrapped) try self.write(")");
    }

    fn bare(self: *Printer, n: *const Node) Allocator.Error!void {
        switch (n.*) {
            // Every spelling carries its type, so no literal is left to a default.
            .lit_u64 => |value| {
                const spelling = self.choices.pick(3);
                if (spelling == 1) {
                    try self.print("0x{x}.U64", .{value});
                } else if (spelling == 2 and value >= 10) {
                    try self.print("{d}_{d}.U64", .{ value / 10, value % 10 });
                } else try self.print("{d}.U64", .{value});
            },
            .lit_bool => |value| try self.write(if (value) "Bool.True" else "Bool.False"),
            .field_u64 => |index| try self.print("{s}.{s}", .{ self.names.param, self.names.fields[index] }),
            .field_bool => try self.print("{s}.{s}", .{ self.names.param, self.names.fields[2] }),
            .local => |slot| {
                const twin = self.names.twins[slot];
                try self.write(if (twin != null and self.choices.pick(2) == 0) twin.? else self.names.locals[slot]);
            },
            .plus => |pair| try self.commuting(pair, "+", "plus"),
            .minus => |pair| try self.two(pair, "-", "minus"),
            .times => |t| {
                // M11: the literal factor first.
                if (self.options.m11 and t.value.* != .lit_u64 and self.extra.pick(2) == 0) {
                    try self.print("({d}.U64 * ", .{t.k});
                    try self.expr(t.value);
                    try self.write(")");
                    return;
                }
                try self.write("(");
                try self.expr(t.value);
                if (self.choices.pick(2) == 0) try self.print(" * {d})", .{t.k}) else try self.print(").times({d})", .{t.k});
            },
            .is_lt => |pair| try self.lessThan(pair),
            .is_eq => |pair| try self.commuting(pair, "==", "is_eq"),
            .is_ne => |pair| if (self.choices.pick(2) == 0) {
                try self.write("(");
                try self.expr(pair[0]);
                try self.write(" != ");
                try self.expr(pair[1]);
                try self.write(")");
            } else {
                try self.write("!(");
                try self.commuting(pair, "==", "is_eq");
                try self.write(")");
            },
            .and_ => |pair| switch (self.choices.pick(3)) {
                0 => {
                    try self.write("(");
                    try self.expr(pair[0]);
                    try self.write(" and ");
                    try self.expr(pair[1]);
                    try self.write(")");
                },
                // `(a and b) and c` is `a and (b and c)`.
                2 => if (pair[0].* == .and_) {
                    try self.write("(");
                    try self.expr(pair[0].and_[0]);
                    try self.write(" and (");
                    try self.expr(pair[0].and_[1]);
                    try self.write(" and ");
                    try self.expr(pair[1]);
                    try self.write("))");
                } else {
                    try self.write("(");
                    try self.expr(pair[0]);
                    try self.write(" and ");
                    try self.expr(pair[1]);
                    try self.write(")");
                },
                else => {
                    try self.write("(if ");
                    try self.expr(pair[0]);
                    try self.write(" ");
                    try self.expr(pair[1]);
                    try self.write(" else Bool.False)");
                },
            },
            .or_ => |pair| switch (self.choices.pick(3)) {
                0 => {
                    try self.write("(");
                    try self.expr(pair[0]);
                    try self.write(" or ");
                    try self.expr(pair[1]);
                    try self.write(")");
                },
                // `(a or b) or c` is `a or (b or c)`.
                2 => if (pair[0].* == .or_) {
                    try self.write("(");
                    try self.expr(pair[0].or_[0]);
                    try self.write(" or (");
                    try self.expr(pair[0].or_[1]);
                    try self.write(" or ");
                    try self.expr(pair[1]);
                    try self.write("))");
                } else {
                    try self.write("(");
                    try self.expr(pair[0]);
                    try self.write(" or ");
                    try self.expr(pair[1]);
                    try self.write(")");
                },
                else => {
                    try self.write("(if ");
                    try self.expr(pair[0]);
                    try self.write(" Bool.True else ");
                    try self.expr(pair[1]);
                    try self.write(")");
                },
            },
            .not => |inner| switch (self.choices.pick(4)) {
                // De Morgan: `!(a and b)` is `!a or !b`, `!(a or b)` is `!a and !b`.
                3 => if (inner.* == .and_ or inner.* == .or_) {
                    const pair = if (inner.* == .and_) inner.and_ else inner.or_;
                    try self.write("(!");
                    try self.expr(pair[0]);
                    try self.write(if (inner.* == .and_) " or !" else " and !");
                    try self.expr(pair[1]);
                    try self.write(")");
                } else {
                    try self.write("!(");
                    try self.expr(inner);
                    try self.write(")");
                },
                0 => {
                    try self.write("!(");
                    try self.expr(inner);
                    try self.write(")");
                },
                1 => {
                    try self.write("Bool.not(");
                    try self.expr(inner);
                    try self.write(")");
                },
                // `!(a < b)` is `a >= b` over integers.
                else => if (inner.* == .is_lt) {
                    try self.two(inner.is_lt, ">=", "is_gte");
                } else {
                    try self.write("!(");
                    try self.expr(inner);
                    try self.write(")");
                },
            },
            .if_ => |i| try self.ifTerm(i.cond, i.then, i.other),
            .let => |l| try self.let(l.value, l.body, l.slot),
            .default => |d| {
                const tag = try self.symbols.tag(d.tag);
                try self.write("{ ");
                const made = try self.symbols.fresh("lc");
                // The annotation makes the value a `Try` in both spellings: a
                // `match` on `Ok` and `Err` alone infers a structural union.
                try self.print("{s} : Try(U64, [{s}])\n{s} = if ", .{ made, tag, made });
                try self.expr(d.cond);
                try self.write(" Ok(");
                try self.expr(d.ok);
                try self.print(") else Err({s})\n", .{tag});
                if (self.choices.pick(2) == 0) {
                    try self.print("{s} ?? ", .{made});
                    try self.expr(d.fallback);
                } else {
                    const v = try self.symbols.fresh("lc");
                    try self.print("match {s} {{\n Ok({s}) => {s}\n Err(_) => ", .{ made, v, v });
                    try self.expr(d.fallback);
                    try self.write("\n}");
                }
                try self.write(" }");
            },
            .sum => |s| {
                const acc = try self.symbols.fresh("$ac");
                const item = try self.symbols.fresh("lc");
                // M7: the accumulator as a scalar, as a record, or as a tuple,
                // the last two with a field that nothing changes.
                const shape = if (self.options.m7) self.extra.pick(3) else 0;
                const f1 = try self.symbols.fresh("fo");
                const f2 = try self.symbols.fresh("fo");
                // M10: a scalar sum as `List.fold` over a lambda (N16c).
                if (self.options.m10 and shape == 0 and self.extra.pick(2) == 0) {
                    const state = try self.symbols.fresh("lc");
                    try self.print("{s}.{s}.fold(", .{ self.names.param, self.names.fields[3] });
                    try self.expr(s.start);
                    // The start may bind this slot in a block of its own.
                    self.names.locals[s.slot] = item;
                    self.names.twins[s.slot] = null;
                    try self.print(", |{s}, {s}| {s} + ", .{ state, item, state });
                    try self.expr(s.step);
                    try self.write(")");
                    return;
                }
                try self.print("{{\nvar {s} = ", .{acc});
                switch (shape) {
                    0 => try self.expr(s.start),
                    1 => {
                        try self.print("{{ {s}: ", .{f1});
                        try self.expr(s.start);
                        try self.print(", {s}: 0.U64 }}", .{f2});
                    },
                    else => {
                        try self.write("(");
                        try self.expr(s.start);
                        try self.write(", 0.U64)");
                    },
                }
                // The start may bind this slot in a block of its own.
                self.names.locals[s.slot] = item;
                self.names.twins[s.slot] = null;
                const list = try std.fmt.allocPrint(self.gpa, "{s}.{s}", .{ self.names.param, self.names.fields[3] });
                defer self.gpa.free(list);
                // M6: a `for` over the list, over its iterator, or a `while` over its indices.
                switch (self.choices.pick(3)) {
                    0 => try self.print("\nfor {s} in {s} {{\n", .{ item, list }),
                    1 => try self.print("\nfor {s} in {s}.iter() {{\n", .{ item, list }),
                    else => {
                        const at = try self.symbols.fresh("$ix");
                        try self.print("\nvar {s} = 0\nwhile {s} < {s}.len() {{\n{s} = {s}.get({s}) ?? 0\n", .{ at, at, list, item, list, at });
                        try self.accStep(shape, acc, f1, f2, s.step);
                        try self.print("\n{s} = {s} + 1\n}}\n", .{ at, at });
                        try self.accResult(shape, acc, f1);
                        try self.write("\n}");
                        return;
                    },
                }
                try self.accStep(shape, acc, f1, f2, s.step);
                try self.write("\n}\n");
                try self.accResult(shape, acc, f1);
                try self.write("\n}");
            },
            .twice => |t| try self.twice(t.args, t.k),
            .upto => |u| try self.upto(u.bound, u.limit, u.init, u.step, u.slot, u.other),
            .counted => |u| try self.counted(u.bound, u.limit, u.init, u.j0, u.step, u.slot, u.other),
            .empty => |e| {
                const list = try std.fmt.allocPrint(self.gpa, "{s}.{s}", .{ self.names.param, self.names.fields[3] });
                defer self.gpa.free(list);
                // N16f: each spelling is `List.is_empty` or its negation.
                if (e.negated) switch (self.extra.pick(4)) {
                    0 => try self.print("({s}.len() > 0.U64)", .{list}),
                    1 => try self.print("!({s}.is_empty())", .{list}),
                    2 => try self.print("({s}.len() != 0.U64)", .{list}),
                    else => try self.print("(0.U64 < {s}.len())", .{list}),
                } else switch (self.extra.pick(3)) {
                    0 => try self.print("({s}.len() == 0.U64)", .{list}),
                    1 => try self.print("{s}.is_empty()", .{list}),
                    else => try self.print("(0.U64 == {s}.len())", .{list}),
                }
            },
        }
    }

    /// `if n < limit { sum } else other`, the sum over `i` in `0..=n` written
    /// as a `for` over the range or as a `while $i <= n`, which N11l raises
    /// to the range only where N13u bounds `n` below the type's highest value.
    fn upto(self: *Printer, bound: *const Node, limit: u64, init: u64, step: *const Node, slot: u16, other: *const Node) Allocator.Error!void {
        const acc = try self.symbols.fresh("$ac");
        try self.write("(if ");
        try self.expr(bound);
        try self.print(" < {d}.U64 {{\nvar {s} = {d}.U64\n", .{ limit, acc, init });
        if (self.extra.pick(2) == 0) {
            const index = try self.symbols.fresh("lc");
            self.names.locals[slot] = index;
            self.names.twins[slot] = null;
            try self.print("for {s} in 0..=", .{index});
            try self.expr(bound);
            try self.print(" {{\n{s} = {s} + ", .{ acc, acc });
            try self.expr(step);
            try self.write("\n}\n");
        } else {
            const index = try self.symbols.fresh("$ix");
            self.names.locals[slot] = index;
            self.names.twins[slot] = null;
            try self.print("var {s} = 0.U64\nwhile {s} <= ", .{ index, index });
            try self.expr(bound);
            try self.print(" {{\n{s} = {s} + ", .{ acc, acc });
            try self.expr(step);
            try self.print("\n{s} = {s} + 1\n}}\n", .{ index, index });
        }
        try self.print("{s}\n}} else ", .{acc});
        try self.expr(other);
        try self.write(")");
    }

    /// `if n < limit { sum } else other`, the sum over `i` in `0..<n`
    /// written as a `for` over the range, as a `while $i < n`, or as a
    /// `while !$done` whose `else` sets the flag, which N11n makes the
    /// `while`; and the second counter `j` as a `var` from `j0` stepped by 1
    /// with the index, which N11o makes `i + j0`, or as `i + j0` itself.
    fn counted(self: *Printer, bound: *const Node, limit: u64, init: u64, j0: u64, step: *const Node, slot: u16, other: *const Node) Allocator.Error!void {
        const acc = try self.symbols.fresh("$ac");
        try self.write("(if ");
        try self.expr(bound);
        try self.print(" < {d}.U64 {{\nvar {s} = {d}.U64\n", .{ limit, acc, init });
        const form = self.extra.pick(3);
        const index = try self.symbols.fresh(if (form == 0) "lc" else "$ix");
        const stepped = self.extra.pick(2) == 0;
        const j = try self.symbols.fresh(if (stepped) "$jx" else "lc");
        self.names.locals[slot] = index;
        self.names.twins[slot] = null;
        self.names.locals[slot + 1] = j;
        self.names.twins[slot + 1] = null;
        if (stepped) try self.print("var {s} = {d}.U64\n", .{ j, j0 });
        switch (form) {
            0 => {
                try self.print("for {s} in 0..<", .{index});
                try self.expr(bound);
                try self.write(" {\n");
                try self.countedStep(acc, index, j, j0, stepped, step);
                try self.write("}\n");
            },
            1 => {
                try self.print("var {s} = 0.U64\nwhile {s} < ", .{ index, index });
                try self.expr(bound);
                try self.write(" {\n");
                try self.countedStep(acc, index, j, j0, stepped, step);
                try self.print("{s} = {s} + 1\n}}\n", .{ index, index });
            },
            else => {
                const done = try self.symbols.fresh("$dn");
                try self.print("var {s} = 0.U64\nvar {s} = Bool.False\nwhile !{s} {{\nif {s} < ", .{ index, done, done, index });
                try self.expr(bound);
                try self.write(" {\n");
                try self.countedStep(acc, index, j, j0, stepped, step);
                try self.print("{s} = {s} + 1\n}} else {{\n{s} = Bool.True\n}}\n}}\n", .{ index, index, done });
            },
        }
        try self.print("{s}\n}} else ", .{acc});
        try self.expr(other);
        try self.write(")");
    }

    /// One turn of `counted`: the second counter as `i + j0`, the step added
    /// to the sum, and the counter stepped where it is a `var`.
    fn countedStep(self: *Printer, acc: []const u8, index: []const u8, j: []const u8, j0: u64, stepped: bool, step: *const Node) Allocator.Error!void {
        if (!stepped) try self.print("{s} = {s} + {d}.U64\n", .{ j, index, j0 });
        try self.print("{s} = {s} + ", .{ acc, acc });
        try self.expr(step);
        try self.write("\n");
        if (stepped) try self.print("{s} = {s} + 1\n", .{ j, j });
    }

    /// The statement that adds `step` to the accumulator.
    fn accStep(self: *Printer, shape: u8, acc: []const u8, f1: []const u8, f2: []const u8, step: *const Node) Allocator.Error!void {
        switch (shape) {
            0 => try self.print("{s} = {s} + ", .{ acc, acc }),
            1 => try self.print("{s} = {{ {s}: {s}.{s} + ", .{ acc, f1, acc, f1 }),
            else => try self.print("{s} = ({s}.0 + ", .{ acc, acc }),
        }
        try self.expr(step);
        switch (shape) {
            0 => {},
            1 => try self.print(", {s}: {s}.{s} }}", .{ f2, acc, f2 }),
            else => try self.print(", {s}.1)", .{acc}),
        }
    }

    /// The accumulator's value.
    fn accResult(self: *Printer, shape: u8, acc: []const u8, f1: []const u8) Allocator.Error!void {
        switch (shape) {
            0 => try self.write(acc),
            1 => try self.print("{s}.{s}", .{ acc, f1 }),
            else => try self.print("{s}.0", .{acc}),
        }
    }

    /// `h(x1, y1) + h(x2, y2)` for a private helper `h(p, q) = p + q * k`,
    /// which takes its arguments as two, as a record, as a tuple, or as
    /// either of the last two destructured.
    fn twice(self: *Printer, args: [4]*const Node, k: u64) Allocator.Error!void {
        const name = try self.symbols.fresh("hp");
        const p = try self.symbols.fresh("lc");
        const q = try self.symbols.fresh("lc");
        const whole = try self.symbols.fresh("lc");
        const shape = self.extra.pick(5);
        // M13: the helper in another package, called through its module.
        const away = self.options.m13 and self.extra.pick(2) == 0;
        const into = if (away) self.lib_helpers else self.helpers;
        switch (shape) {
            0 => try into.print(self.gpa, "{s} : U64, U64 -> U64\n{s} = |{s}, {s}| {s} + {s} * {d}\n\n", .{ name, name, p, q, p, q, k }),
            1 => try into.print(self.gpa, "{s} : {{ {s} : U64, {s} : U64 }} -> U64\n{s} = |{s}| {s}.{s} + {s}.{s} * {d}\n\n", .{ name, p, q, name, whole, whole, p, whole, q, k }),
            2 => try into.print(self.gpa, "{s} : (U64, U64) -> U64\n{s} = |{s}| {s}.0 + {s}.1 * {d}\n\n", .{ name, name, whole, whole, whole, k }),
            3 => try into.print(self.gpa, "{s} : {{ {s} : U64, {s} : U64 }} -> U64\n{s} = |{{ {s}, {s} }}| {s} + {s} * {d}\n\n", .{ name, p, q, name, p, q, p, q, k }),
            else => try into.print(self.gpa, "{s} : (U64, U64) -> U64\n{s} = |({s}, {s})| {s} + {s} * {d}\n\n", .{ name, name, p, q, p, q, k }),
        }
        const callee = if (away) try std.fmt.allocPrint(self.symbols.arena, "Lib.{s}", .{name}) else name;
        try self.write("(");
        for (0..2) |call| {
            if (call == 1) try self.write(" + ");
            const x = args[call * 2];
            const y = args[call * 2 + 1];
            switch (shape) {
                0 => {
                    try self.print("{s}(", .{callee});
                    try self.expr(x);
                    try self.write(", ");
                    try self.expr(y);
                    try self.write(")");
                },
                1, 3 => {
                    try self.print("{s}({{ {s}: ", .{ callee, p });
                    try self.expr(x);
                    try self.print(", {s}: ", .{q});
                    try self.expr(y);
                    try self.write(" })");
                },
                else => {
                    try self.print("{s}((", .{callee});
                    try self.expr(x);
                    try self.write(", ");
                    try self.expr(y);
                    try self.write("))");
                },
            }
        }
        try self.write(")");
    }

    /// `if cond then else other`, in some prints braced, as a `match` on
    /// `Bool` in either arm order, as an `if` on the negation with the
    /// branches swapped, and, when `cond` tests a `U64` against a literal, as
    /// a `match` on the literal.
    fn ifTerm(self: *Printer, cond: *const Node, then: *const Node, other: *const Node) Allocator.Error!void {
        const literal_test = cond.* == .is_eq and cond.is_eq[1].* == .lit_u64;
        // The last choice nests the `if`s of an `and` or `or` condition, which
        // repeats the arm the connective shares, so that arm must be a leaf.
        const nestable = (cond.* == .and_ and isLeaf(other)) or (cond.* == .or_ and isLeaf(then));
        const plain: u8 = if (literal_test) 6 else 5;
        const choice = self.choices.pick(plain + 1);
        switch (if (choice == plain and !nestable) 0 else choice) {
            0 => {
                try self.write("(if ");
                try self.expr(cond);
                try self.write(" ");
                try self.expr(then);
                try self.write(" else ");
                try self.expr(other);
                try self.write(")");
            },
            1 => {
                try self.write("(if ");
                try self.expr(cond);
                try self.write(" { ");
                try self.expr(then);
                try self.write(" } else { ");
                try self.expr(other);
                try self.write(" })");
            },
            2, 3 => |k| {
                try self.write("(match ");
                try self.expr(cond);
                try self.write(" {\n");
                const Arm = struct { tag: []const u8, body: *const Node };
                const true_arm: Arm = .{ .tag = "Bool.True", .body = then };
                const false_arm: Arm = .{ .tag = "Bool.False", .body = other };
                const arms = if (k == 2) [_]Arm{ true_arm, false_arm } else [_]Arm{ false_arm, true_arm };
                for (arms) |arm| {
                    try self.print("{s} => ", .{arm.tag});
                    try self.expr(arm.body);
                    try self.write("\n");
                }
                try self.write("})");
            },
            4 => {
                try self.write("(if !(");
                try self.expr(cond);
                try self.write(") ");
                try self.expr(other);
                try self.write(" else ");
                try self.expr(then);
                try self.write(")");
            },
            5 => if (literal_test) {
                try self.write("(match ");
                try self.expr(cond.is_eq[0]);
                try self.write(" {\n");
                // A pattern takes no parentheses and gets its type from the scrutinee.
                try self.print("{d} => ", .{cond.is_eq[1].lit_u64});
                try self.expr(then);
                try self.write("\n_ => ");
                try self.expr(other);
                try self.write("\n})");
            } else try self.nestedIf(cond, then, other),
            else => try self.nestedIf(cond, then, other),
        }
    }

    /// `if a and b t else o` as `if a { if b t else o } else o`, and
    /// `if a or b t else o` as `if a t else { if b t else o }`.
    fn nestedIf(self: *Printer, cond: *const Node, then: *const Node, other: *const Node) Allocator.Error!void {
        if (cond.* == .and_) {
            try self.write("(if ");
            try self.expr(cond.and_[0]);
            try self.write(" { (if ");
            try self.expr(cond.and_[1]);
            try self.write(" ");
            try self.expr(then);
            try self.write(" else ");
            try self.expr(other);
            try self.write(") } else ");
            try self.expr(other);
            try self.write(")");
        } else {
            try self.write("(if ");
            try self.expr(cond.or_[0]);
            try self.write(" ");
            try self.expr(then);
            try self.write(" else (if ");
            try self.expr(cond.or_[1]);
            try self.write(" ");
            try self.expr(then);
            try self.write(" else ");
            try self.expr(other);
            try self.write("))");
        }
    }

    /// A binding and its body. In some prints: the binding after an
    /// independent binding of the body, or inside each branch of the body
    /// that reads it.
    fn let(self: *Printer, value: *const Node, body: *const Node, slot: u16) Allocator.Error!void {
        switch (body.*) {
            .let => |inner| if (!reads(inner.value, slot) and self.choices.pick(3) == 0) {
                try self.write("{\n");
                try self.bind(inner.value, inner.slot);
                // A binding inside `value` can take the inner slot.
                const name = self.names.locals[inner.slot];
                const twin = self.names.twins[inner.slot];
                try self.bind(value, slot);
                self.names.locals[inner.slot] = name;
                self.names.twins[inner.slot] = twin;
                try self.expr(inner.body);
                try self.write("\n}");
                return;
            },
            // Into each branch that reads it.
            .if_ => |i| if (!reads(i.cond, slot) and (reads(i.then, slot) or reads(i.other, slot)) and self.choices.pick(3) == 0) {
                try self.write("(if ");
                try self.expr(i.cond);
                for ([_]*const Node{ i.then, i.other }, [_][]const u8{ " { ", " } else { " }) |arm, open| {
                    try self.write(open);
                    if (reads(arm, slot)) try self.let(value, arm, slot) else try self.expr(arm);
                }
                try self.write(" })");
                return;
            },
            .lit_u64, .lit_bool, .field_u64, .field_bool, .local, .plus, .minus, .times, .is_lt, .is_eq, .is_ne, .and_, .or_, .not, .default, .sum, .twice, .empty, .upto, .counted => {},
        }
        try self.write("{\n");
        try self.bind(value, slot);
        try self.expr(body);
        try self.write("\n}");
    }

    /// `name = value` on a line, as a plain binding or as a `var` that is
    /// never reassigned, and in some prints an unused binding of the value
    /// before it, a second binding of it after it, and an `expect` after them.
    fn bind(self: *Printer, value: *const Node, slot: u16) Allocator.Error!void {
        if (self.choices.pick(4) == 0) {
            try self.print("{s} = ", .{try self.symbols.fresh("_lc")});
            try self.expr(value);
            try self.write("\n");
        }
        const as_var = self.choices.pick(2) == 0;
        const name = try self.symbols.fresh(if (as_var) "$lc" else "lc");
        if (as_var) try self.write("var ");
        try self.print("{s} = ", .{name});
        try self.expr(value);
        try self.write("\n");
        self.names.twins[slot] = null;
        if (self.choices.pick(4) == 0) {
            const twin = try self.symbols.fresh("lc");
            try self.print("{s} = ", .{twin});
            try self.expr(value);
            try self.write("\n");
            self.names.twins[slot] = twin;
        }
        self.names.locals[slot] = name;
        if (self.choices.pick(3) == 0) {
            try self.write("expect ");
            try self.print("{s}.{s} == {s}.{s}", .{ self.names.param, self.names.fields[0], self.names.param, self.names.fields[0] });
            try self.write("\n");
        }
    }
};

/// The symbol generator: every userspace name is a kind prefix and an id.
const Symbols = struct {
    arena: Allocator,
    next: u32 = 0,

    fn fresh(self: *Symbols, prefix: []const u8) Allocator.Error![]const u8 {
        defer self.next += 1;
        return std.fmt.allocPrint(self.arena, "{s}{d}", .{ prefix, self.next });
    }

    fn tag(self: *Symbols, id: u32) Allocator.Error![]const u8 {
        return std.fmt.allocPrint(self.arena, "Tg{d}", .{id % 4});
    }
};

/// Generate one case from `bytes`.
pub fn generate(gpa: Allocator, bytes: []const u8) Allocator.Error!Case {
    return generateWith(gpa, bytes, .{});
}

/// Generate one case from `bytes`, with the constructs `options` allows.
pub fn generateWith(gpa: Allocator, bytes: []const u8, options: Options) Allocator.Error!Case {
    var arena_impl = std.heap.ArenaAllocator.init(gpa);
    defer arena_impl.deinit();
    const arena = arena_impl.allocator();

    var reader: Reader = .{ .bytes = bytes };
    // The extra choices read the same bytes from the other end.
    const reversed = try arena.dupe(u8, bytes);
    std.mem.reverse(u8, reversed);
    var extra: Reader = .{ .bytes = reversed };
    var builder: Builder = .{ .arena = arena, .reader = &reader, .extra = &extra, .options = options };
    const root = try builder.term(.u64_, .{}, 0);

    var symbols: Symbols = .{ .arena = arena };
    const fields = [4][]const u8{ try symbols.fresh("fa"), try symbols.fresh("fb"), try symbols.fresh("fc"), try symbols.fresh("fd") };
    const input_ty = try symbols.fresh("In");
    const left_fn = try symbols.fresh("fn");
    const right_fn = try symbols.fresh("fn");
    const answer = try symbols.fresh("an");
    var left_names: Names = .{ .param = try symbols.fresh("pa"), .fields = fields };
    var right_names: Names = .{ .param = try symbols.fresh("pa"), .fields = fields };

    const input: Input = .{
        .a = reader.pick(20),
        .b = reader.pick(20),
        .flag = reader.pick(2) == 1,
        .items = blk: {
            const items = try gpa.alloc(u64, reader.pick(4));
            for (items) |*item| item.* = reader.pick(10);
            break :blk items;
        },
    };
    errdefer gpa.free(input.items);

    var out = std.ArrayList(u8).empty;
    errdefer out.deinit(gpa);
    var lib = std.ArrayList(u8).empty;
    errdefer lib.deinit(gpa);
    try out.print(gpa, "{s} : {{ {s} : U64, {s} : U64, {s} : Bool, {s} : List(U64) }}\n\n", .{ input_ty, fields[0], fields[1], fields[2], fields[3] });

    // The two prints read their spelling choices from what follows the
    // term, one byte stream each, so they differ wherever the bytes do.
    const rest = bytes[@min(reader.at, bytes.len)..];
    const half = rest.len / 2;
    var left_choices: Reader = .{ .bytes = rest[0..half] };
    var right_choices: Reader = .{ .bytes = rest[half..] };
    const left_reversed = try arena.dupe(u8, rest[0..half]);
    std.mem.reverse(u8, left_reversed);
    const right_reversed = try arena.dupe(u8, rest[half..]);
    std.mem.reverse(u8, right_reversed);
    var left_extra: Reader = .{ .bytes = left_reversed };
    var right_extra: Reader = .{ .bytes = right_reversed };
    for ([_]struct { name: []const u8, names: *Names, choices: *Reader, extra: *Reader }{
        .{ .name = left_fn, .names = &left_names, .choices = &left_choices, .extra = &left_extra },
        .{ .name = right_fn, .names = &right_names, .choices = &right_choices, .extra = &right_extra },
    }) |side| {
        // The body first: the helpers it defines come before the function.
        var body: std.ArrayList(u8) = .empty;
        defer body.deinit(gpa);
        var helpers: std.ArrayList(u8) = .empty;
        defer helpers.deinit(gpa);
        var lib_helpers: std.ArrayList(u8) = .empty;
        defer lib_helpers.deinit(gpa);
        var printer: Printer = .{ .gpa = gpa, .out = &body, .choices = side.choices, .extra = side.extra, .names = side.names, .symbols = &symbols, .helpers = &helpers, .lib_helpers = &lib_helpers, .options = options };
        // `return` last, in some prints.
        if (side.choices.pick(3) == 0) {
            try body.appendSlice(gpa, "{\nreturn ");
            try printer.expr(root);
            try body.appendSlice(gpa, "\n}");
        } else try printer.expr(root);
        try out.appendSlice(gpa, helpers.items);
        // A helper of `Lib` is an associated item of its type, so its lines
        // are indented into the type's block.
        var lines = std.mem.splitScalar(u8, lib_helpers.items, '\n');
        while (lib_helpers.items.len != 0) {
            const line = lines.next() orelse break;
            if (line.len != 0) try lib.print(gpa, "    {s}", .{line});
            try lib.append(gpa, '\n');
        }
        try out.print(gpa, "{s} : {s} -> U64\n{s} = |{s}| ", .{ side.name, input_ty, side.name, side.names.param });
        try out.appendSlice(gpa, body.items);
        try out.appendSlice(gpa, "\n\n");
    }

    try out.print(gpa, "{s} : U64\n{s} = {s}({{ {s}: {d}, {s}: {d}, {s}: {s}, {s}: [", .{
        answer,    answer,    left_fn,
        fields[0], input.a,   fields[1],
        input.b,   fields[2], if (input.flag) "Bool.True" else "Bool.False",
        fields[3],
    });
    for (input.items, 0..) |item, i| try out.print(gpa, "{s}{d}", .{ if (i == 0) "" else ", ", item });
    try out.appendSlice(gpa, "] })\n");

    return .{
        .source = try out.toOwnedSlice(gpa),
        .left_param = try gpa.dupe(u8, left_names.param),
        .right_param = try gpa.dupe(u8, right_names.param),
        .answer = try gpa.dupe(u8, answer),
        .lawful = options.m10,
        .input = input,
        .lib_source = try lib.toOwnedSlice(gpa),
    };
}

test "M13 puts some helpers in the module of another package, and calls them through it" {
    var prng = std.Random.DefaultPrng.init(0x0d13);
    var bytes: [96]u8 = undefined;
    const placed = for (0..200) |_| {
        prng.random().bytes(&bytes);
        var case = try generateWith(std.testing.allocator, &bytes, .{ .m13 = true });
        defer case.deinit(std.testing.allocator);
        if (case.lib_source.len == 0) continue;
        try std.testing.expect(std.mem.find(u8, case.source, "Lib.hp") != null);
        break true;
    } else false;
    try std.testing.expect(placed);
}

test "a case prints two functions and the constant of their answer" {
    var case = try generate(std.testing.allocator, &.{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 });
    defer case.deinit(std.testing.allocator);
    try std.testing.expect(std.mem.find(u8, case.source, case.left_param) != null);
    try std.testing.expect(std.mem.find(u8, case.source, case.right_param) != null);
    try std.testing.expect(std.mem.find(u8, case.source, case.answer) != null);
}
