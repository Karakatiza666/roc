//! The orientation check of `roc-reify-rule-derivation.md` 2.2.
//!
//! `l ≻ r` compares the components of the measure of normal-form 3.0 in
//! order, each counted on the unfolded term, and nothing else: the driver
//! checks that same measure after every round, so a rule the measure does
//! not lower is not oriented. A component compares by its count only when no
//! variable occurs more often in `r` than in `l`; otherwise the rule fails.
//! The positional components, `is_lte` scrutinees and flipping scrutinees,
//! are counted with the pattern's root in every context that changes the
//! count, and the rule must decrease in each. `unordered_leaves` reads
//! whether an operand is a literal: a variable is one under `is_lit` or as a
//! literal switch's key, and is not one under `not_lit`; the rule must
//! decrease with each other variable at such an operand taken both ways.

const std = @import("std");
const reify = @import("reify");
const term = @import("term.zig");

const Term = term.Term;
const Component = reify.measure.Component;

const term_components = [_]Component{ .loops, .general_loops, .aggregate_slots, .applies, .switches, .negated_connectives, .nodes, .flipped_comparisons, .is_lte_scrutinees, .flipping_scrutinees, .unordered_leaves, .terminators, .joins, .arms_and_operands };

/// Which variables are literals, as a rule's conditions state it.
pub const Lits = struct {
    lit: []const term.Var = &.{},
    not_lit: []const term.Var = &.{},

    fn has(vs: []const term.Var, v: term.Var) bool {
        return std.mem.findScalar(term.Var, vs, v) != null;
    }
};

/// The literal variables of `rule`'s instances, by its conditions.
pub fn ruleLits(arena: std.mem.Allocator, rule: reify.rules.Rule) std.mem.Allocator.Error!Lits {
    var lit: std.ArrayList(term.Var) = .empty;
    var not_lit: std.ArrayList(term.Var) = .empty;
    for (rule.conds) |c| switch (c) {
        .is_lit, .nonzero_lit => |k| try lit.append(arena, k),
        .not_lit => |k| try not_lit.append(arena, k),
        .int_owner, .not_float_owner, .speculatable, .movable, .movable_rest, .speculatable_rest, .polarity_flips, .folds, .same_ty, .lit_bool_switch => {},
    };
    return .{ .lit = lit.items, .not_lit = not_lit.items };
}

/// Whether each variable is a literal, for one way of taking the open ones.
pub const Kinds = struct {
    lits: Lits = .{},
    keys: []const term.Var = &.{},
    open: []const term.Var = &.{},
    /// Bit `i` set: `open[i]` is a literal.
    mask: u64 = 0,

    // Null for a variable whose kind is not known.
    fn isLit(self: Kinds, t: Term) ?bool {
        return switch (t) {
            .app => |x| x.sym.op == .lit,
            .var_ => |v| if (Lits.has(self.lits.lit, v) or Lits.has(self.keys, v))
                true
            else if (Lits.has(self.lits.not_lit, v))
                false
            else if (std.mem.findScalar(term.Var, self.open, v)) |i|
                self.mask & (@as(u64, 1) << @intCast(i)) != 0
            else
                null,
        };
    }
};

// A set of at most 32 variables.
const VarSet = struct {
    buf: [32]term.Var = undefined,
    len: usize = 0,

    fn items(self: *const VarSet) []const term.Var {
        return self.buf[0..self.len];
    }

    fn add(self: *VarSet, v: term.Var) void {
        if (std.mem.findScalar(term.Var, self.items(), v) != null) return;
        self.buf[self.len] = v;
        self.len += 1;
    }
};

/// Where the rewritten term sits.
pub const Context = enum {
    /// Anywhere a scrutinee is not.
    plain,
    /// The scrutinee of a switch.
    scrutinee,
};

/// What decided the comparison.
pub const Decider = union(enum) {
    component: Component,
    /// A variable occurs more often on the right: no instance order holds.
    variable: term.Var,
    /// Every component ties.
    none,
};

/// The result of checking one direction.
pub const Verdict = struct {
    oriented: bool,
    decided_by: Decider,
    context: Context,
};

/// The count of component `c` on `t` placed in context `ctx`.
pub fn count(t: Term, c: Component, ctx: Context, kinds: Kinds) u64 {
    var n: u64 = countIn(t, c, kinds);
    if (ctx == .scrutinee) switch (c) {
        .is_lte_scrutinees => n += lteLeaves(t),
        .flipping_scrutinees => n += @intFromBool(term.polarityFlips(t)),
        .loops, .general_loops, .aggregate_slots, .applies, .switches, .negated_connectives, .forwarding_calls, .nodes, .flipped_comparisons, .unordered_leaves, .terminators, .joins, .arms_and_operands, .graph_nodes => {},
    };
    return n;
}

// A variable stands for at least one node, and the variable check keeps
// the right side from reading it more often, so it counts as one.
fn countIn(t: Term, c: Component, kinds: Kinds) u64 {
    const x = switch (t) {
        .var_ => return @intFromBool(c == .nodes),
        .app => |x| x,
    };
    var n: u64 = switch (c) {
        .nodes => 1,
        .loops => @intFromBool(x.sym.op.isLoop()),
        .general_loops => @intFromBool(x.sym.op == .loop),
        .switches => @intFromBool(x.sym.op == .switch_),
        .flipped_comparisons => @intFromBool(x.sym.op == .prim and (x.sym.method == .is_gt or x.sym.method == .is_gte)),
        .negated_connectives => @intFromBool(x.sym.op == .prim and x.sym.method == .not and x.args[0] == .app and (x.args[0].app.sym.op == .and_ or x.args[0].app.sym.op == .or_ or x.args[0].app.sym.op == .switch_)),
        .is_lte_scrutinees => if (x.sym.op == .switch_ and x.args.len > 0) lteLeaves(x.args[0]) else 0,
        .flipping_scrutinees => @intFromBool(x.sym.op == .switch_ and x.args.len > 0 and term.polarityFlips(x.args[0])),
        .unordered_leaves => @intFromBool(ordersLiteralLast(x) and kinds.isLit(x.args[0]).? and !kinds.isLit(x.args[1]).?),
        // A switch's arms and an `And` or `Or`'s operands after the first are
        // regions; a literal switch's keys are not.
        .arms_and_operands => if (x.sym.op == .switch_ or x.sym.op == .and_ or x.sym.op == .or_) x.args.len -| 1 -| (term.litKeys(x) orelse 0) else 0,
        // First-order terms own no slots, terminators or joins, and call no row.
        .aggregate_slots, .applies, .forwarding_calls, .terminators, .joins, .graph_nodes => 0,
    };
    for (x.args) |a| n += countIn(a, c, kinds);
    return n;
}

// A bound owner is an integer type: the table binds owners only under
// `int_owner`, and generalization only for integer builtins.
fn ordersLiteralLast(x: @FieldType(Term, "app")) bool {
    if (x.sym.op != .prim or x.args.len != 2) return false;
    const owner: reify.prims.Owner = switch (x.sym.owner.?) {
        .fixed => |o| o,
        .bind => .i64,
    };
    return reify.prims.ordersLiteralLast(owner, x.sym.method.?);
}

// The variables at an operand of a call `ordersLiteralLast` names.
fn operandVars(t: Term, out: *VarSet) void {
    const x = switch (t) {
        .var_ => return,
        .app => |x| x,
    };
    if (ordersLiteralLast(x)) for (x.args) |a| if (a == .var_) out.add(a.var_);
    for (x.args) |a| operandVars(a, out);
}

fn keyVars(t: Term, out: *VarSet) void {
    const x = switch (t) {
        .var_ => return,
        .app => |x| x,
    };
    if (term.litKeys(x)) |n| for (x.args[1 .. 1 + n]) |k| if (k == .var_) out.add(k.var_);
    for (x.args) |a| keyVars(a, out);
}

// The `is_lte` leaves of a scrutinee, through its `And` and `Or` operands
// and its `Bool` switches' arms.
fn lteLeaves(t: Term) u64 {
    const x = switch (t) {
        .var_ => return 0,
        .app => |x| x,
    };
    if (x.sym.op == .and_ or x.sym.op == .or_ or x.sym.op == .switch_) {
        var n: u64 = 0;
        for (if (x.sym.op == .switch_) x.args[1..] else x.args) |a| n += lteLeaves(a);
        return n;
    }
    return @intFromBool(x.sym.op == .prim and x.sym.method == .is_lte);
}

/// Whether `lhs ≻ rhs` in context `ctx`, with the variables' kinds `kinds`.
fn orientIn(lhs: Term, rhs: Term, ctx: Context, kinds: Kinds) Verdict {
    var v: term.Var = 0;
    const bound = @max(lhs.varBound(), rhs.varBound());
    while (v < bound) : (v += 1) {
        if (rhs.countVar(v) > lhs.countVar(v)) return .{ .oriented = false, .decided_by = .{ .variable = v }, .context = ctx };
    }
    for (term_components) |c| {
        const l = count(lhs, c, ctx, kinds);
        const r = count(rhs, c, ctx, kinds);
        if (l != r) return .{ .oriented = l > r, .decided_by = .{ .component = c }, .context = ctx };
    }
    return .{ .oriented = false, .decided_by = .none, .context = ctx };
}

/// Whether `lhs ≻ rhs` in every context and for every kind of the
/// variables `lits` leaves open; the verdict names the first case that
/// fails, if one does.
pub fn orient(lhs: Term, rhs: Term, lits: Lits) Verdict {
    var keys: VarSet = .{};
    keyVars(lhs, &keys);
    var all: VarSet = .{};
    operandVars(lhs, &all);
    operandVars(rhs, &all);
    var open: VarSet = .{};
    for (all.items()) |v| if (!Lits.has(lits.lit, v) and !Lits.has(lits.not_lit, v) and !Lits.has(keys.items(), v)) open.add(v);
    std.debug.assert(open.len < 16);
    var plain: Verdict = undefined;
    var mask: u64 = 0;
    while (mask < @as(u64, 1) << @intCast(open.len)) : (mask += 1) {
        const kinds: Kinds = .{ .lits = lits, .keys = keys.items(), .open = open.items(), .mask = mask };
        plain = orientIn(lhs, rhs, .plain, kinds);
        if (!plain.oriented) return plain;
        const scrutinee = orientIn(lhs, rhs, .scrutinee, kinds);
        if (!scrutinee.oriented) return scrutinee;
    }
    return plain;
}

const testing = std.testing;

test "every instance of every rule of the table orients" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    for (reify.rules.rules) |r| {
        if (r.tier == .evaluation) continue;
        const lits = try ruleLits(arena.allocator(), r);
        for (try term.instances(arena.allocator(), r)) |rt| {
            const v = orient(rt.lhs, rt.rhs, lits);
            if (!v.oriented) {
                var w: std.Io.Writer.Allocating = .init(arena.allocator());
                try term.write(&w.writer, rt.lhs);
                try w.writer.writeAll(" -> ");
                try term.write(&w.writer, rt.rhs);
                std.debug.print("row {s} does not orient, by {any}: {s}\n", .{ r.step, v.decided_by, w.written() });
            }
            try testing.expect(v.oriented);
        }
    }
}

fn app(sym: term.Sym, args: []const Term) Term {
    return .{ .app = .{ .sym = sym, .args = args } };
}

test "commutativity orients in neither direction" {
    const plus: term.Sym = .{ .op = .prim, .method = .plus_wrap, .owner = .{ .bind = 0 } };
    const l = app(plus, &.{ .{ .var_ = 0 }, .{ .var_ = 1 } });
    const r = app(plus, &.{ .{ .var_ = 1 }, .{ .var_ = 0 } });
    try testing.expect(!orient(l, r, .{}).oriented);
    try testing.expect(!orient(r, l, .{}).oriented);
}

test "a rule that duplicates a variable fails orientation" {
    const not_sym: term.Sym = .{ .op = .prim, .method = .not, .owner = .{ .fixed = .bool_ } };
    const and_sym: term.Sym = .{ .op = .and_ };
    const l = app(not_sym, &.{app(not_sym, &.{app(not_sym, &.{.{ .var_ = 0 }})})});
    const r = app(and_sym, &.{ .{ .var_ = 0 }, .{ .var_ = 0 } });
    const v = orient(l, r, .{});
    try testing.expect(!v.oriented);
    try testing.expectEqual(Decider{ .variable = 0 }, v.decided_by);
}

test "a rule whose result is an is_lte counts in the scrutinee context" {
    // not(is_lt(a, b)) -> is_lte(b, a) lowers the node count, which comes
    // before is_lte scrutinees, so it orients even under a switch.
    const not_sym: term.Sym = .{ .op = .prim, .method = .not, .owner = .{ .fixed = .bool_ } };
    const lt: term.Sym = .{ .op = .prim, .method = .is_lt, .owner = .{ .bind = 0 } };
    const lte: term.Sym = .{ .op = .prim, .method = .is_lte, .owner = .{ .bind = 0 } };
    const l = app(not_sym, &.{app(lt, &.{ .{ .var_ = 0 }, .{ .var_ = 1 } })});
    const r = app(lte, &.{ .{ .var_ = 1 }, .{ .var_ = 0 } });
    try testing.expectEqual(@as(u64, 1), count(r, .is_lte_scrutinees, .scrutinee, .{}));
    try testing.expectEqual(@as(u64, 0), count(r, .is_lte_scrutinees, .plain, .{}));
    const v = orient(l, r, .{});
    try testing.expect(v.oriented);
    try testing.expectEqual(Decider{ .component = .nodes }, v.decided_by);
}
