//! Step 2's fingerprints (`roc-reify-rule-derivation.md` 3.2): each term's
//! values in `eval.zig`'s `most_defined` mode on one fixed input set, and
//! the grouping of terms by sort and fingerprint.
//!
//! The input set gives every variable of the signature a value in each of 64
//! assignments: ⊥ for each variable once; one special value of its sort
//! shared by the variables of that sort, so equal operands occur; the special
//! values of its sort; then seeded random values. The counterexamples of
//! `inputs.zon` follow them.

const std = @import("std");
const reify = @import("reify");
const term = @import("term.zig");
const sig_mod = @import("sig.zig");

const Allocator = std.mem.Allocator;
const Value = reify.eval.Value;
const Sort = sig_mod.Sort;

/// A fingerprint: a hash of a term's values on the input set. Equal
/// fingerprints only propose a pair; a proof decides it.
pub const Fingerprint = u128;

/// A term's fingerprints on every input, and on the inputs where no
/// variable is ⊥: two terms equal on the second only are equal where their
/// variables are speculatable, which the builder assumes of a variable.
pub const Prints = struct { all: Fingerprint, defined: Fingerprint };

/// The number of generated assignments.
pub const generated = 64;

const int_specials = [_]i64{ 0, 1, -1, std.math.minInt(i64), std.math.maxInt(i64), 2, -2, 3 };

fn special(arena: Allocator, sort: Sort, i: usize) Allocator.Error!Value {
    return switch (sort) {
        .bool => .{ .bool_ = i % 2 == 1 },
        .i64 => .{ .int = int_specials[i % int_specials.len] },
        .union_ab => switch (i % 7) {
            0 => tagB(),
            6 => tagA(arena, .bottom),
            else => |j| tagA(arena, .{ .int = int_specials[j - 1] }),
        },
        .record_xy => switch (i % 7) {
            5 => record(arena, .bottom, .{ .bool_ = true }),
            6 => record(arena, .{ .int = 0 }, .bottom),
            else => |j| record(arena, .{ .int = int_specials[(j * 3) % int_specials.len] }, .{ .bool_ = j % 2 == 0 }),
        },
        // A tuple's values are a record's, and a nominal's its backing type's.
        .tuple_ib => special(arena, .record_xy, i),
        .nominal_i64 => special(arena, .i64, i),
        .f64, .str, .union_abc, .list_i64 => unreachable,
    };
}

fn tagB() Value {
    return .{ .tag = .{ .name = sig_mod.tag_b, .payload = &.{} } };
}

fn tagA(arena: Allocator, v: Value) Allocator.Error!Value {
    return .{ .tag = .{ .name = sig_mod.tag_a, .payload = try arena.dupe(Value, &.{v}) } };
}

fn record(arena: Allocator, x: Value, y: Value) Allocator.Error!Value {
    return .{ .agg = try arena.dupe(Value, &.{ x, y }) };
}

fn random(arena: Allocator, rng: std.Random, sort: Sort) Allocator.Error!Value {
    return switch (sort) {
        .bool => .{ .bool_ = rng.boolean() },
        .i64 => .{ .int = randomInt(rng) },
        .union_ab => if (rng.uintLessThan(u8, 4) == 0) tagB() else tagA(arena, .{ .int = randomInt(rng) }),
        .record_xy, .tuple_ib => record(arena, .{ .int = randomInt(rng) }, .{ .bool_ = rng.boolean() }),
        .nominal_i64 => .{ .int = randomInt(rng) },
        .f64, .str, .union_abc, .list_i64 => unreachable,
    };
}

fn randomInt(rng: std.Random) i64 {
    return if (rng.boolean()) rng.int(i64) else rng.intRangeAtMost(i64, -4, 4);
}

/// The input set over the base variables of `vars`, then `extra`.
pub fn inputs(arena: Allocator, vars: sig_mod.Vars, extra: []const []const Value) Allocator.Error![]const []const Value {
    const n = vars.sorts.items.len;
    const out = try arena.alloc([]const Value, generated + extra.len);
    var prng = std.Random.DefaultPrng.init(0x5eed_0001);
    const rng = prng.random();
    for (out[0..generated], 0..) |*row, i| {
        const vals = try arena.alloc(Value, n);
        for (vals, vars.sorts.items, 0..) |*v, s, var_index| {
            v.* = if (i < n)
                (if (i == var_index) .bottom else try special(arena, s, var_index + 1))
            else if (i < n + 8)
                try special(arena, s, i - n)
            else if (i < 40)
                try special(arena, s, i * (2 * var_index + 3) + var_index)
            else
                try random(arena, rng, s);
        }
        row.* = vals;
    }
    @memcpy(out[generated..], extra);
    return out;
}

fn hashValue(h: *std.hash.Wyhash, v: Value) void {
    h.update(&.{@backingInt(std.meta.activeTag(v))});
    switch (v) {
        .bottom => {},
        .int => |x| h.update(std.mem.asBytes(&x)),
        .float => |x| h.update(std.mem.asBytes(&x)),
        .bool_ => |x| h.update(&.{@intFromBool(x)}),
        .str => |x| h.update(x),
        .agg, .list => |xs| {
            h.update(std.mem.asBytes(&xs.len));
            for (xs) |x| hashValue(h, x);
        },
        .tag => |t| {
            h.update(std.mem.asBytes(&t.name));
            for (t.payload) |x| hashValue(h, x);
        },
    }
}

/// The fingerprints of the term `inst` holds, on `input_set`.
pub fn of(arena: Allocator, inst: *sig_mod.Instance, input_set: []const []const Value) reify.eval.Error!Prints {
    var ev = try reify.eval.Evaluator.init(arena, &inst.store, &inst.types, .most_defined);
    var all: [2]std.hash.Wyhash = .{ .init(0), .init(1) };
    var defined: [2]std.hash.Wyhash = .{ .init(2), .init(3) };
    for (input_set) |args| {
        const v = try ev.run(inst.row, args);
        const some_bottom = for (args) |a| {
            if (a == .bottom) break true;
        } else false;
        for ([2]*[2]std.hash.Wyhash{ &all, &defined }, [2]bool{ true, !some_bottom }) |hs, on| {
            if (on) for (hs) |*h| hashValue(h, v);
        }
    }
    return .{ .all = @as(u128, all[1].final()) << 64 | all[0].final(), .defined = @as(u128, defined[1].final()) << 64 | defined[0].final() };
}

/// Write a value of `sort` as `inputs.zon` records it: `bot`, `True`,
/// `-3`, `A(1)`, `B`, `{x: 0, y: bot}`, `(0, True)`. A nominal's value is
/// its backing value.
pub fn writeValue(w: *std.Io.Writer, sort: Sort, v: Value) std.Io.Writer.Error!void {
    switch (v) {
        .bottom => try w.writeAll("bot"),
        .int => |x| try w.print("{d}", .{x}),
        .bool_ => |x| try w.writeAll(if (x) "True" else "False"),
        .tag => |t| if (t.name == sig_mod.tag_a) {
            try w.writeAll("A(");
            try writeValue(w, .i64, t.payload[0]);
            try w.writeAll(")");
        } else try w.writeAll("B"),
        .agg => |xs| {
            try w.writeAll(if (sort == .tuple_ib) "(" else "{x: ");
            try writeValue(w, .i64, xs[0]);
            try w.writeAll(if (sort == .tuple_ib) ", " else ", y: ");
            try writeValue(w, .bool, xs[1]);
            try w.writeAll(if (sort == .tuple_ib) ")" else "}");
        },
        .float, .str, .list => unreachable,
    }
}

/// Why a value's text did not parse.
pub const ParseError = error{InvalidValue} || Allocator.Error;

/// Parse the text `writeValue` gives back into a value of `sort`.
pub fn parseValue(arena: Allocator, sort: Sort, text: []const u8) ParseError!Value {
    const t = std.mem.trim(u8, text, " ");
    if (std.mem.eql(u8, t, "bot")) return .bottom;
    return switch (sort) {
        .bool => if (std.mem.eql(u8, t, "True")) .{ .bool_ = true } else if (std.mem.eql(u8, t, "False")) .{ .bool_ = false } else error.InvalidValue,
        .i64 => .{ .int = std.fmt.parseInt(i64, t, 10) catch return error.InvalidValue },
        .union_ab => if (std.mem.eql(u8, t, "B"))
            tagB()
        else if (std.mem.startsWith(u8, t, "A(") and std.mem.endsWith(u8, t, ")"))
            tagA(arena, try parseValue(arena, .i64, t[2 .. t.len - 1]))
        else
            error.InvalidValue,
        .record_xy => {
            if (!std.mem.startsWith(u8, t, "{x: ") or !std.mem.endsWith(u8, t, "}")) return error.InvalidValue;
            const body = t[4 .. t.len - 1];
            const comma = std.mem.find(u8, body, ", y: ") orelse return error.InvalidValue;
            return record(arena, try parseValue(arena, .i64, body[0..comma]), try parseValue(arena, .bool, body[comma + 5 ..]));
        },
        .tuple_ib => {
            if (!std.mem.startsWith(u8, t, "(") or !std.mem.endsWith(u8, t, ")")) return error.InvalidValue;
            const body = t[1 .. t.len - 1];
            const comma = std.mem.findScalar(u8, body, ',') orelse return error.InvalidValue;
            return record(arena, try parseValue(arena, .i64, body[0..comma]), try parseValue(arena, .bool, body[comma + 1 ..]));
        },
        .nominal_i64 => parseValue(arena, .i64, t),
        .f64, .str, .union_abc, .list_i64 => error.InvalidValue,
    };
}

const testing = std.testing;

test "every variable is bottom once, and values print and parse back" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var vars = try sig_mod.Vars.base(testing.allocator, sig_mod.find("S1").?);
    defer vars.deinit(testing.allocator);
    const set = try inputs(a, vars, &.{});
    for (0..vars.sorts.items.len) |v| {
        var bottoms: usize = 0;
        for (set) |row| bottoms += @intFromBool(row[v] == .bottom);
        try testing.expect(bottoms >= 1);
    }
    for (set) |row| for (row, vars.sorts.items) |v, s| {
        var out: std.Io.Writer.Allocating = .init(a);
        try writeValue(&out.writer, s, v);
        try testing.expect(v.eql(try parseValue(a, s, out.written())));
    };
}

test "a term and its unfolding by an equation share a fingerprint; a different term does not" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var vars = try sig_mod.Vars.base(testing.allocator, sig_mod.find("S1").?);
    defer vars.deinit(testing.allocator);
    const set = try inputs(a, vars, &.{});
    const none: [reify.rules.count]bool = @splat(false);
    var prints: [3]Prints = undefined;
    for (&prints, [_][]const u8{ "Num.I64.plus(x2, 0)", "x2", "Num.I64.minus(x2, 0)" }) |*p, text| {
        var inst: sig_mod.Instance = undefined;
        try inst.init(testing.allocator, vars, try term.parse(a, text), .i64, true, &none);
        defer inst.deinit();
        p.* = try of(a, &inst, set);
    }
    try testing.expectEqual(prints[0], prints[1]);
    try testing.expectEqual(prints[0], prints[2]);
    var inst: sig_mod.Instance = undefined;
    try inst.init(testing.allocator, vars, try term.parse(a, "Num.I64.minus(x2, 1)"), .i64, true, &none);
    defer inst.deinit();
    try testing.expect((try of(a, &inst, set)).all != prints[0].all);
}

test "a term that crashes only where its variable does agrees with True on the defined inputs only" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var vars = try sig_mod.Vars.base(testing.allocator, sig_mod.find("S1").?);
    defer vars.deinit(testing.allocator);
    const set = try inputs(a, vars, &.{});
    const none: [reify.rules.count]bool = @splat(false);
    var prints: [2]Prints = undefined;
    for (&prints, [_][]const u8{ "Bool.is_eq(x0, x0)", "True" }) |*p, text| {
        var inst: sig_mod.Instance = undefined;
        // Rules off: T3.1 would build the first as `True`.
        try inst.init(testing.allocator, vars, try term.parse(a, text), .i64, false, &none);
        defer inst.deinit();
        p.* = try of(a, &inst, set);
    }
    try testing.expect(prints[0].all != prints[1].all);
    try testing.expectEqual(prints[0].defined, prints[1].defined);
}
