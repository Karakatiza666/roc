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

    pub fn deinit(self: *Case, gpa: Allocator) void {
        gpa.free(self.source);
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

    fn letTerm(self: *Builder, ty: Type, scope: Scope, depth: u8) Allocator.Error!*const Node {
        if (scope.len >= max_scope) return self.leaf(ty, &scope);
        const bound: Type = if (self.reader.pick(3) == 0) .bool_ else .u64_;
        const value = try self.term(bound, scope, depth);
        var inner = scope;
        inner.types[inner.len] = bound;
        inner.len += 1;
        return self.node(.{ .let = .{ .value = value, .body = try self.term(ty, inner, depth), .slot = scope.len } });
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
    };
}

/// Prints one term, choosing a spelling at every construct.
const Printer = struct {
    gpa: Allocator,
    out: *std.ArrayList(u8),
    choices: *Reader,
    names: *Names,
    symbols: *Symbols,

    fn write(self: *Printer, text: []const u8) Allocator.Error!void {
        try self.out.appendSlice(self.gpa, text);
    }

    fn print(self: *Printer, comptime fmt: []const u8, args: anytype) Allocator.Error!void {
        try self.out.print(self.gpa, fmt, args);
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
            .plus => |pair| try self.two(pair, "+", "plus"),
            .minus => |pair| try self.two(pair, "-", "minus"),
            .times => |t| {
                try self.write("(");
                try self.expr(t.value);
                if (self.choices.pick(2) == 0) try self.print(" * {d})", .{t.k}) else try self.print(").times({d})", .{t.k});
            },
            .is_lt => |pair| try self.two(pair, "<", "is_lt"),
            .is_eq => |pair| try self.two(pair, "==", "is_eq"),
            .is_ne => |pair| if (self.choices.pick(2) == 0) {
                try self.write("(");
                try self.expr(pair[0]);
                try self.write(" != ");
                try self.expr(pair[1]);
                try self.write(")");
            } else {
                try self.write("!(");
                try self.two(pair, "==", "is_eq");
                try self.write(")");
            },
            .and_ => |pair| if (self.choices.pick(2) == 0) {
                try self.write("(");
                try self.expr(pair[0]);
                try self.write(" and ");
                try self.expr(pair[1]);
                try self.write(")");
            } else {
                try self.write("(if ");
                try self.expr(pair[0]);
                try self.write(" ");
                try self.expr(pair[1]);
                try self.write(" else Bool.False)");
            },
            .or_ => |pair| if (self.choices.pick(2) == 0) {
                try self.write("(");
                try self.expr(pair[0]);
                try self.write(" or ");
                try self.expr(pair[1]);
                try self.write(")");
            } else {
                try self.write("(if ");
                try self.expr(pair[0]);
                try self.write(" Bool.True else ");
                try self.expr(pair[1]);
                try self.write(")");
            },
            .not => |inner| if (self.choices.pick(2) == 0) {
                try self.write("!(");
                try self.expr(inner);
                try self.write(")");
            } else {
                try self.write("Bool.not(");
                try self.expr(inner);
                try self.write(")");
            },
            .if_ => |i| if (self.choices.pick(2) == 0) {
                try self.write("(if ");
                try self.expr(i.cond);
                try self.write(" ");
                try self.expr(i.then);
                try self.write(" else ");
                try self.expr(i.other);
                try self.write(")");
            } else {
                try self.write("(if ");
                try self.expr(i.cond);
                try self.write(" { ");
                try self.expr(i.then);
                try self.write(" } else { ");
                try self.expr(i.other);
                try self.write(" })");
            },
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
                try self.print("{{\nvar {s} = ", .{acc});
                try self.expr(s.start);
                // The start may bind this slot in a block of its own.
                self.names.locals[s.slot] = item;
                self.names.twins[s.slot] = null;
                try self.print("\nfor {s} in {s}.{s} {{\n{s} = {s} + ", .{ item, self.names.param, self.names.fields[3], acc, acc });
                try self.expr(s.step);
                try self.print("\n}}\n{s}\n}}", .{acc});
            },
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
            .lit_u64, .lit_bool, .field_u64, .field_bool, .local, .plus, .minus, .times, .is_lt, .is_eq, .is_ne, .and_, .or_, .not, .default, .sum => {},
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
    var arena_impl = std.heap.ArenaAllocator.init(gpa);
    defer arena_impl.deinit();
    const arena = arena_impl.allocator();

    var reader: Reader = .{ .bytes = bytes };
    var builder: Builder = .{ .arena = arena, .reader = &reader };
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
    try out.print(gpa, "{s} : {{ {s} : U64, {s} : U64, {s} : Bool, {s} : List(U64) }}\n\n", .{ input_ty, fields[0], fields[1], fields[2], fields[3] });

    // The two prints read their spelling choices from what follows the
    // term, one byte stream each, so they differ wherever the bytes do.
    const rest = bytes[@min(reader.at, bytes.len)..];
    const half = rest.len / 2;
    var left_choices: Reader = .{ .bytes = rest[0..half] };
    var right_choices: Reader = .{ .bytes = rest[half..] };
    for ([_]struct { name: []const u8, names: *Names, choices: *Reader }{
        .{ .name = left_fn, .names = &left_names, .choices = &left_choices },
        .{ .name = right_fn, .names = &right_names, .choices = &right_choices },
    }) |side| {
        try out.print(gpa, "{s} : {s} -> U64\n{s} = |{s}| ", .{ side.name, input_ty, side.name, side.names.param });
        var printer: Printer = .{ .gpa = gpa, .out = &out, .choices = side.choices, .names = side.names, .symbols = &symbols };
        // `return` last, in some prints.
        if (side.choices.pick(3) == 0) {
            try out.appendSlice(gpa, "{\nreturn ");
            try printer.expr(root);
            try out.appendSlice(gpa, "\n}");
        } else try printer.expr(root);
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
        .input = input,
    };
}

test "a case prints two functions and the constant of their answer" {
    var case = try generate(std.testing.allocator, &.{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 });
    defer case.deinit(std.testing.allocator);
    try std.testing.expect(std.mem.find(u8, case.source, case.left_param) != null);
    try std.testing.expect(std.mem.find(u8, case.source, case.right_param) != null);
    try std.testing.expect(std.mem.find(u8, case.source, case.answer) != null);
}
