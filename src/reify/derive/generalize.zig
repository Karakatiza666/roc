//! Step 4 of the loop (`roc-reify-rule-derivation.md` 3.4): lift the
//! subterms and literals of a proved pair to pattern variables while the
//! proof still holds, trying the conditions of the fixed condition language
//! when a lift proves only under one.

const std = @import("std");
const term = @import("term.zig");
const sig_mod = @import("sig.zig");
const prove = @import("prove.zig");
const smt = @import("smt.zig");
const order_mod = @import("order.zig");

const Allocator = std.mem.Allocator;
const Term = term.Term;

/// A condition of the fixed language, over a variable of the equation.
pub const Cond = union(enum) {
    /// The integer builtins' owner is any builtin integer type.
    int_owner,
    speculatable: term.Var,
    is_lit: term.Var,
    nonzero_lit: term.Var,

    fn assume(self: Cond) ?smt.Assume {
        return switch (self) {
            .int_owner => null,
            // A literal never crashes, so both proofs assume the variable defined.
            .speculatable, .is_lit => |k| .{ .defined = k },
            .nonzero_lit => |k| .{ .nonzero = k },
        };
    }
};

/// A generalized equation.
pub const Equation = struct {
    lhs: Term,
    rhs: Term,
    conds: []const Cond,

    /// The proof assumptions of the conditions.
    pub fn assumptions(self: Equation, arena: Allocator) Allocator.Error![]const smt.Assume {
        var out: std.ArrayList(smt.Assume) = .empty;
        for (self.conds) |c| if (c.assume()) |a| try out.append(arena, a);
        return out.toOwnedSlice(arena);
    }

    /// The variables its conditions make literals, for the orientation check.
    pub fn lits(self: Equation, arena: Allocator) Allocator.Error!order_mod.Lits {
        var out: std.ArrayList(term.Var) = .empty;
        for (self.conds) |c| switch (c) {
            .is_lit, .nonzero_lit => |k| try out.append(arena, k),
            .int_owner, .speculatable => {},
        };
        return .{ .lit = out.items };
    }

    /// The widths the equation is claimed at.
    pub fn widths(self: Equation) prove.Widths {
        for (self.conds) |c| if (c == .int_owner) return .every_int;
        return .i64_only;
    }
};

fn subterms(arena: Allocator, t: Term, out: *std.ArrayList(Term)) Allocator.Error!void {
    const x = switch (t) {
        .var_ => return,
        .app => |x| x,
    };
    for (out.items) |o| {
        if (o.eql(t)) break;
    } else try out.append(arena, t);
    for (x.args) |a| try subterms(arena, a, out);
}

/// `t` with every occurrence of `s` replaced by `with`.
pub fn replace(arena: Allocator, t: Term, s: Term, with: Term) Allocator.Error!Term {
    if (t.eql(s)) return with;
    const x = switch (t) {
        .var_ => return t,
        .app => |x| x,
    };
    const args = try arena.alloc(Term, x.args.len);
    for (x.args, args) |a, *o| o.* = try replace(arena, a, s, with);
    return .{ .app = .{ .sym = x.sym, .args = args } };
}

fn isLit(t: Term) bool {
    return t == .app and t.app.sym.op == .lit;
}

fn isNonzeroInt(t: Term) bool {
    return isLit(t) and t.app.sym.int != null and t.app.sym.int.? != 0;
}

fn hasIntPrim(t: Term) bool {
    const x = switch (t) {
        .var_ => return false,
        .app => |x| x,
    };
    if (x.sym.op == .prim and x.sym.owner.? == .fixed and x.sym.owner.?.fixed.int() != null) return true;
    // A literal switch is on an integer, whose owner its row binds.
    if (term.litKeys(x) != null) return true;
    for (x.args) |a| if (hasIntPrim(a)) return true;
    return false;
}

// Whether every integer literal of `t` is a value of every integer type:
// the table reads a literal in its own type's signedness, so `-1` is not a
// `U8` literal, and a rule over every owner may only name literals all have.
fn litsFitEveryInt(t: Term) bool {
    const x = switch (t) {
        .var_ => return true,
        .app => |x| x,
    };
    if (x.sym.int) |n| if (n < 0 or n > std.math.maxInt(i8)) return false;
    for (x.args) |a| if (!litsFitEveryInt(a)) return false;
    return true;
}

fn bindOwners(arena: Allocator, t: Term) Allocator.Error!Term {
    const x = switch (t) {
        .var_ => return t,
        .app => |x| x,
    };
    var sym = x.sym;
    if (sym.op == .prim and sym.owner.? == .fixed and sym.owner.?.fixed.int() != null) sym.owner = .{ .bind = 0 };
    const args = try arena.alloc(Term, x.args.len);
    for (x.args, args) |a, *o| o.* = try bindOwners(arena, a);
    return .{ .app = .{ .sym = sym, .args = args } };
}

/// Generalize the equation `lhs = rhs`, proved under `start`. New variables
/// are added to `vars`, which `vars_gpa` allocated.
pub fn run(arena: Allocator, vars_gpa: Allocator, prover: *prove.Prover, vars: *sig_mod.Vars, lhs: Term, rhs: Term, start: []const Cond) prove.Error!Equation {
    var eq: Equation = .{ .lhs = lhs, .rhs = rhs, .conds = start };
    outer: while (true) {
        var subs: std.ArrayList(Term) = .empty;
        try subterms(arena, eq.lhs, &subs);
        // Larger subterms first: one lift of a large subterm generalizes most.
        std.mem.sort(Term, subs.items, {}, struct {
            fn gt(_: void, a: Term, b: Term) bool {
                return size(a) > size(b);
            }
        }.gt);
        for (subs.items) |s| {
            if (s.eql(eq.lhs)) continue;
            const v = try vars.fresh(vars_gpa, sig_mod.sortOf(vars.*, s));
            const l = try replace(arena, eq.lhs, s, .{ .var_ = v });
            // The subterm lifted on both sides, then on the left side only.
            const both = try replace(arena, eq.rhs, s, .{ .var_ = v });
            const rights = [2]?Term{ if (both.eql(eq.rhs)) null else both, eq.rhs };
            var tries: [4]?Cond = .{ null, .{ .speculatable = v }, null, null };
            if (isLit(s)) tries[2] = .{ .is_lit = v };
            if (isNonzeroInt(s)) tries[3] = .{ .nonzero_lit = v };
            // Every way to lift `s` is sent ahead, in parallel; the first that proves, in order, is taken.
            var cands: std.ArrayList(Equation) = .empty;
            var claims: std.ArrayList(prove.Prover.Claim) = .empty;
            for (rights) |maybe_r| {
                const r = maybe_r orelse continue;
                for (tries, 0..) |c, i| {
                    if (i > 0 and c == null) continue;
                    var conds: std.ArrayList(Cond) = .empty;
                    try conds.appendSlice(arena, eq.conds);
                    if (c) |cc| try conds.append(arena, cc);
                    const cand: Equation = .{ .lhs = l, .rhs = r, .conds = try conds.toOwnedSlice(arena) };
                    try cands.append(arena, cand);
                    try claims.append(arena, .{ .l = l, .r = r, .assume = try cand.assumptions(arena), .widths = cand.widths() });
                }
            }
            try prover.prefetch(vars.*, claims.items);
            for (cands.items, claims.items, 0..) |cand, c, i| {
                if (try prover.equation(vars.*, c.l, c.r, c.assume, c.widths) == .proved) {
                    try prover.release(vars.*, claims.items[i + 1 ..]);
                    eq = cand;
                    continue :outer;
                }
            }
        }
        break;
    }
    if ((hasIntPrim(eq.lhs) or hasIntPrim(eq.rhs)) and litsFitEveryInt(eq.lhs) and litsFitEveryInt(eq.rhs)) {
        var conds: std.ArrayList(Cond) = .empty;
        try conds.appendSlice(arena, eq.conds);
        try conds.append(arena, .int_owner);
        const cand: Equation = .{ .lhs = try bindOwners(arena, eq.lhs), .rhs = try bindOwners(arena, eq.rhs), .conds = try conds.toOwnedSlice(arena) };
        if (try prover.equation(vars.*, cand.lhs, cand.rhs, try cand.assumptions(arena), .every_int) == .proved) eq = cand;
    }
    // A condition the proof does not need, or on a variable a lift removed,
    // goes, so the rule is the most general the proofs allow.
    var i: usize = 0;
    while (i < eq.conds.len) {
        const c = eq.conds[i];
        const without = try std.mem.concat(arena, Cond, &.{ eq.conds[0..i], eq.conds[i + 1 ..] });
        const drop = switch (c) {
            .int_owner => false,
            .speculatable, .is_lit, .nonzero_lit => |k| !eq.lhs.occurs(k) or blk: {
                const cand: Equation = .{ .lhs = eq.lhs, .rhs = eq.rhs, .conds = without };
                break :blk try prover.equation(vars.*, eq.lhs, eq.rhs, try cand.assumptions(arena), cand.widths()) == .proved;
            },
        };
        if (drop) eq.conds = without else i += 1;
    }
    return eq;
}

/// The number of nodes of `t`.
pub fn size(t: Term) u32 {
    return switch (t) {
        .var_ => 1,
        .app => |x| blk: {
            var n: u32 = 1;
            for (x.args) |a| n += size(a);
            break :blk n;
        },
    };
}

/// The equation's text with its variables renamed in order of first
/// occurrence and their sorts listed, so two equations equal up to renaming
/// have one key.
pub fn key(arena: Allocator, vars: sig_mod.Vars, eq: Equation) Allocator.Error![]const u8 {
    var order: std.ArrayList(term.Var) = .empty;
    try firstOccurrences(arena, eq.lhs, &order);
    try firstOccurrences(arena, eq.rhs, &order);
    var out: std.Io.Writer.Allocating = .init(arena);
    const w = &out.writer;
    term.writeRenamed(w, eq.lhs, order.items) catch return error.OutOfMemory;
    w.writeAll(" = ") catch return error.OutOfMemory;
    term.writeRenamed(w, eq.rhs, order.items) catch return error.OutOfMemory;
    for (eq.conds) |c| {
        switch (c) {
            .int_owner => w.writeAll(" [o0 is an integer type]") catch return error.OutOfMemory,
            .speculatable, .is_lit, .nonzero_lit => |k| w.print(" [x{d} {s}]", .{ indexOf(order.items, k), @tagName(c) }) catch return error.OutOfMemory,
        }
    }
    w.writeAll(" :") catch return error.OutOfMemory;
    for (order.items, 0..) |v, i| w.print(" x{d}:{s}", .{ i, @tagName(vars.of(v)) }) catch return error.OutOfMemory;
    return out.written();
}

fn indexOf(order: []const term.Var, v: term.Var) usize {
    return std.mem.findScalar(term.Var, order, v).?;
}

fn firstOccurrences(arena: Allocator, t: Term, order: *std.ArrayList(term.Var)) Allocator.Error!void {
    switch (t) {
        .var_ => |v| if (std.mem.findScalar(term.Var, order.items, v) == null) try order.append(arena, v),
        .app => |x| for (x.args) |a| try firstOccurrences(arena, a, order),
    }
}

const testing = std.testing;

test "plus(field#0(r), 0) = field#0(r) generalizes to plus(x, 0) = x over every integer type" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var vars = try sig_mod.Vars.base(testing.allocator, sig_mod.find("S1").?);
    defer vars.deinit(testing.allocator);
    var p = prove.Prover.init(a, testing.allocator, testing.io);
    defer p.deinit();
    if (p.z3_missing != null) return error.SkipZigTest;
    const eq = try run(a, testing.allocator, &p, &vars, try term.parse(a, "Num.I64.plus(field#0(x6), 0)"), try term.parse(a, "field#0(x6)"), &.{});
    try testing.expectEqualStrings("o0.plus(x0, 0) = x0 [o0 is an integer type] : x0:i64", try key(a, vars, eq));
}

test "Bool.is_eq(x, x) = True generalizes only under speculatable" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var vars = try sig_mod.Vars.base(testing.allocator, sig_mod.find("S1").?);
    defer vars.deinit(testing.allocator);
    var p = prove.Prover.init(a, testing.allocator, testing.io);
    defer p.deinit();
    const eq = try run(a, testing.allocator, &p, &vars, try term.parse(a, "Bool.is_eq(True, True)"), try term.parse(a, "True"), &.{});
    try testing.expectEqualStrings("Bool.is_eq(x0, x0) = True [x0 speculatable] : x0:bool", try key(a, vars, eq));
    // From a pair over variables, proved with them speculatable, the same rule.
    const from_vars = try run(a, testing.allocator, &p, &vars, try term.parse(a, "Bool.is_eq(x0, x0)"), try term.parse(a, "True"), &.{.{ .speculatable = 0 }});
    try testing.expectEqualStrings("Bool.is_eq(x0, x0) = True [x0 speculatable] : x0:bool", try key(a, vars, from_vars));
    // A condition the proof does not need is dropped.
    const needless = try run(a, testing.allocator, &p, &vars, try term.parse(a, "Bool.not(Bool.not(x0))"), try term.parse(a, "x0"), &.{.{ .speculatable = 0 }});
    try testing.expectEqualStrings("Bool.not(Bool.not(x0)) = x0 : x0:bool", try key(a, vars, needless));
}

test "an equation naming -1 keeps its owner: -1 is not a literal of an unsigned type" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var vars = try sig_mod.Vars.base(testing.allocator, sig_mod.find("S2").?);
    defer vars.deinit(testing.allocator);
    var p = prove.Prover.init(a, testing.allocator, testing.io);
    defer p.deinit();
    if (p.z3_missing != null) return error.SkipZigTest;
    const eq = try run(a, testing.allocator, &p, &vars, try term.parse(a, "Num.I64.bitwise_and(x2, -1)"), try term.parse(a, "x2"), &.{});
    try testing.expectEqualStrings("Num.I64.bitwise_and(x0, -1) = x0 : x0:i64", try key(a, vars, eq));
}
