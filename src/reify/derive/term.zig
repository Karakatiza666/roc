//! First-order terms over the rule table's patterns
//! (`roc-reify-rule-derivation.md` 4, `term.zig`).
//!
//! A term is a variable or a symbol applied to terms. A rule's left side is
//! its root symbol over its argument patterns; its right side is its result
//! template. Unification finds the overlaps of step 1 and anti-unification
//! generalizes a proved pair in step 4.

const std = @import("std");
const reify = @import("reify");

const Allocator = std.mem.Allocator;
const Op = reify.ir.Op;
const prims = reify.prims;
const table = reify.rules;

/// A term variable. Pattern variables keep their numbers, region variables
/// become `region_base + k`, and owner variables live in symbols.
pub const Var = u16;

/// The first term variable that stands for a region variable: an arm or an
/// operand, read as the value its region delivers.
pub const region_base: Var = 64;

/// A symbol: an op, and for `prim` its method and owner, for a literal its
/// value, for `tag`, `payload` and `field` the tag or field index. A table
/// pattern leaves the index unset: it stands for the one component its root reads.
/// On a `switch_` the index is the key count n of a literal switch, whose
/// arguments are the scrutinee, the n key literals, the n keyed arms and the
/// default arm; a switch without an index is on a `Bool` or a union.
pub const Sym = struct {
    op: Op,
    method: ?prims.Method = null,
    owner: ?table.OwnerPat = null,
    lit: ?bool = null,
    int: ?i64 = null,
    index: ?u32 = null,

    /// Whether two symbols are one symbol.
    pub fn eql(a: Sym, b: Sym) bool {
        if (a.op != b.op or a.method != b.method or a.lit != b.lit or a.int != b.int or a.index != b.index) return false;
        const ao = a.owner orelse return b.owner == null;
        const bo = b.owner orelse return false;
        return ownerEql(ao, bo);
    }
};

fn ownerEql(a: table.OwnerPat, b: table.OwnerPat) bool {
    return switch (a) {
        .fixed => |o| b == .fixed and b.fixed == o,
        .bind => |k| b == .bind and b.bind == k,
    };
}

/// The key count of a literal switch term, or null for any other term.
pub fn litKeys(x: @FieldType(Term, "app")) ?u32 {
    return if (x.sym.op == .switch_) x.sym.index else null;
}

/// Whether a literal switch in `t` has a variable for a key, as a
/// generalized equation does: such a term has no row to build.
pub fn hasVarKey(t: Term) bool {
    const x = switch (t) {
        .var_ => return false,
        .app => |x| x,
    };
    if (litKeys(x)) |n| for (x.args[1 .. 1 + n]) |k| if (k == .var_) return true;
    for (x.args) |a| if (hasVarKey(a)) return true;
    return false;
}

/// A term.
pub const Term = union(enum) {
    var_: Var,
    app: struct { sym: Sym, args: []const Term },

    /// Structural equality.
    pub fn eql(a: Term, b: Term) bool {
        return switch (a) {
            .var_ => |v| b == .var_ and b.var_ == v,
            .app => |x| b == .app and x.sym.eql(b.app.sym) and x.args.len == b.app.args.len and for (x.args, b.app.args) |p, q| {
                if (!p.eql(q)) break false;
            } else true,
        };
    }

    /// Whether variable `v` occurs in the term.
    pub fn occurs(self: Term, v: Var) bool {
        return switch (self) {
            .var_ => |w| w == v,
            .app => |x| for (x.args) |a| {
                if (a.occurs(v)) break true;
            } else false,
        };
    }

    /// How often variable `v` occurs.
    pub fn countVar(self: Term, v: Var) u32 {
        return switch (self) {
            .var_ => |w| @intFromBool(w == v),
            .app => |x| blk: {
                var n: u32 = 0;
                for (x.args) |a| n += a.countVar(v);
                break :blk n;
            },
        };
    }

    /// The largest variable number plus one.
    pub fn varBound(self: Term) Var {
        return switch (self) {
            .var_ => |w| w + 1,
            .app => |x| blk: {
                var n: Var = 0;
                for (x.args) |a| n = @max(n, a.varBound());
                break :blk n;
            },
        };
    }
};

/// The first term variable that stands for an element of a sequence
/// variable: element `i` of sequence variable `k` is `seq_base + seq_width * k + i`.
pub const seq_base: Var = 48;
const seq_width: Var = 4;

/// The longest run the term view gives a sequence variable. A row with
/// sequence variables reads as every instance whose runs are 0 to
/// `seq_bound` operands long; step 1 and the orientation check cover the
/// row up to that bound, as step 2 covers terms up to size k.
pub const seq_bound = 2;

/// One fixed-arity instance of a row, read as a pair of terms.
pub const RuleTerms = struct {
    lhs: Term,
    rhs: Term,
    /// The element terms each sequence variable took in this instance.
    seqs: [4][]const Term = @splat(&.{}),
    /// The formula a pattern variable a polarity condition reads took in
    /// this instance, if the condition reads it.
    shapes: [16]?Term = @splat(null),
};

const Ctx = struct {
    seqs: [4][]const Term = @splat(&.{}),
    /// The formula a pattern variable stands for, in place of a variable.
    shapes: [16]?Term = @splat(null),
    /// A connective with no operands was built: the instance is not a node.
    empty: bool = false,
};

/// The first term variable of the leaves of a polarity shape.
const shape_base: Var = 56;

/// The fixed-arity instances of a table row. Each sequence variable takes
/// 0 to `seq_bound` fresh variables. A pattern variable a polarity
/// condition reads takes every formula of one leaf, or an `And`, `Or` or
/// `Bool` switch of two, whose leaves are a variable, its `Bool.not`, or an `I64` `is_lt` or
/// `is_lte`, that the condition accepts. An instance whose
/// result is an `And` or `Or` of no operands is left out: the row that
/// turns a one-operand `And` or `Or` into its operand comes first in the
/// table, so the builder never reaches it.
pub fn instances(arena: Allocator, rule: table.Rule) Allocator.Error![]const RuleTerms {
    // An evaluation row's result is a computed value, not a term.
    std.debug.assert(rule.tier != .evaluation);
    const seq_count = table.seqVarCount(rule);
    var polar: ?table.Var = null;
    var lit_bool: ?table.Var = null;
    for (rule.conds) |c| switch (c) {
        .polarity_flips => |k| polar = k,
        .lit_bool_switch => |k| lit_bool = k,
        .int_owner, .not_float_owner, .is_lit, .speculatable, .nonzero_lit, .movable, .movable_rest, .speculatable_rest, .same_ty, .not_lit => {},
        .folds => unreachable, // only an evaluation row folds
    };
    const shapes: []const ?Term = if (polar != null) try polarityShapes(arena) else &.{null};
    // A literal switch with `Bool` arms reads as one over one key, the literal 0.
    if (lit_bool) |k| {
        std.debug.assert(polar == null);
        polar = k;
    }
    const lit_shapes: []const ?Term = if (lit_bool != null) &.{try litBoolShape(arena)} else shapes;
    var out: std.ArrayList(RuleTerms) = .empty;
    var lens: [4]u8 = @splat(0);
    while (true) {
        var ctx: Ctx = .{};
        for (0..seq_count) |k| {
            const elems = try arena.alloc(Term, lens[k]);
            for (elems, 0..) |*e, i| e.* = .{ .var_ = seq_base + seq_width * @as(Var, @intCast(k)) + @as(Var, @intCast(i)) };
            ctx.seqs[k] = elems;
        }
        for (lit_shapes) |shape| {
            if (shape) |f| {
                if (lit_bool == null and !polarityFlips(f)) continue;
                ctx.shapes[polar.?] = f;
            }
            ctx.empty = false;
            const rt = try ofRuleIn(arena, rule, &ctx);
            if (!ctx.empty) try out.append(arena, .{ .lhs = rt.lhs, .rhs = rt.rhs, .seqs = ctx.seqs, .shapes = ctx.shapes });
        }
        var k: usize = 0;
        while (k < seq_count) : (k += 1) {
            if (lens[k] < seq_bound) {
                lens[k] += 1;
                break;
            }
            lens[k] = 0;
        }
        if (k == seq_count) break;
    }
    return out.toOwnedSlice(arena);
}

fn polarityShapes(arena: Allocator) Allocator.Error![]const ?Term {
    const i64_owner: table.OwnerPat = .{ .fixed = .i64 };
    var out: std.ArrayList(?Term) = .empty;
    var leaves: [2][4]Term = undefined;
    for (&leaves, 0..) |*row, j| {
        const v: Term = .{ .var_ = shape_base + 2 * @as(Var, @intCast(j)) };
        const w: Term = .{ .var_ = shape_base + 2 * @as(Var, @intCast(j)) + 1 };
        row.* = .{
            v,
            try notOf(arena, v),
            try appOf(arena, .{ .op = .prim, .method = .is_lt, .owner = i64_owner }, &.{ v, w }),
            try appOf(arena, .{ .op = .prim, .method = .is_lte, .owner = i64_owner }, &.{ v, w }),
        };
    }
    for (leaves[0]) |a| try out.append(arena, a);
    for ([_]Op{ .and_, .or_ }) |op| for (leaves[0]) |a| for (leaves[1]) |b| {
        try out.append(arena, try appOf(arena, .{ .op = op }, &.{ a, b }));
    };
    const scrutinee: Term = .{ .var_ = shape_base + 4 };
    for (leaves[0]) |a| for (leaves[1]) |b| {
        try out.append(arena, try appOf(arena, .{ .op = .switch_ }, &.{ scrutinee, a, b }));
    };
    return out.toOwnedSlice(arena);
}

fn litBoolShape(arena: Allocator) Allocator.Error!Term {
    const v = struct {
        fn of(i: Var) Term {
            return .{ .var_ = shape_base + i };
        }
    }.of;
    const zero: Term = .{ .app = .{ .sym = .{ .op = .lit, .int = 0 }, .args = &.{} } };
    return appOf(arena, .{ .op = .switch_, .index = 1 }, &.{ v(0), zero, v(1), v(2) });
}

fn appOf(arena: Allocator, sym: Sym, args: []const Term) Allocator.Error!Term {
    return .{ .app = .{ .sym = sym, .args = try arena.dupe(Term, args) } };
}

/// The negation of `t` with its `Bool.not` pushed to the leaves, as the
/// builder builds `Bool.not(t)`: N13h cancels a `Bool.not`, N13t turns an
/// `And` into an `Or` of negated operands and back, and N13q flips an
/// integer comparison.
pub fn notOf(arena: Allocator, t: Term) Allocator.Error!Term {
    const x = switch (t) {
        .var_ => return appOf(arena, not_sym, &.{t}),
        .app => |x| x,
    };
    switch (x.sym.op) {
        .and_, .or_ => {
            const args = try arena.alloc(Term, x.args.len);
            for (x.args, args) |a, *o| o.* = try notOf(arena, a);
            return .{ .app = .{ .sym = .{ .op = if (x.sym.op == .and_) .or_ else .and_ }, .args = args } };
        },
        .prim => {
            if (x.sym.method == .not) return x.args[0];
            const int_owner = x.sym.owner.? == .fixed and x.sym.owner.?.fixed.int() != null;
            if (int_owner and (x.sym.method == .is_lt or x.sym.method == .is_lte))
                return appOf(arena, .{ .op = .prim, .method = if (x.sym.method == .is_lt) .is_lte else .is_lt, .owner = x.sym.owner }, &.{ x.args[1], x.args[0] });
            return appOf(arena, not_sym, &.{t});
        },
        .switch_ => {
            // The scrutinee and a literal switch's keys stay; each arm is negated.
            const lead = 1 + (litKeys(x) orelse 0);
            const args = try arena.alloc(Term, x.args.len);
            @memcpy(args[0..lead], x.args[0..lead]);
            for (x.args[lead..], args[lead..]) |a, *o| o.* = try notOf(arena, a);
            return .{ .app = .{ .sym = x.sym, .args = args } };
        },
        .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .call, .for_range, .for_list, .loop, .lambda, .apply => return appOf(arena, not_sym, &.{t}),
    }
}

const not_sym: Sym = .{ .op = .prim, .method = .not, .owner = .{ .fixed = .bool_ } };

/// The term form of the builder's polarity condition (`table.Cond.polarity_flips`).
pub fn polarityFlips(t: Term) bool {
    var l: Leaves = .{};
    countLeaves(t, &l);
    if (l.negated != l.plain) return l.negated > l.plain;
    if (l.lte != l.lt) return l.lte > l.lt;
    if (t == .app and (t.app.sym.op == .and_ or t.app.sym.op == .or_)) return t.app.sym.op == .or_;
    return l.first_flips.?;
}

const Leaves = struct { negated: u32 = 0, plain: u32 = 0, lte: u32 = 0, lt: u32 = 0, first_flips: ?bool = null };

// A `Bool` switch term is `switch_(scrutinee, arms...)`; its arms are its leaves' places.
fn countLeaves(t: Term, l: *Leaves) void {
    const x = switch (t) {
        .var_ => return leafOf(l, .plain),
        .app => |x| x,
    };
    if (x.sym.op == .and_ or x.sym.op == .or_) {
        for (x.args) |a| countLeaves(a, l);
        return;
    }
    if (x.sym.op == .switch_) {
        for (x.args[1 + (litKeys(x) orelse 0) ..]) |a| countLeaves(a, l);
        return;
    }
    if (x.sym.op != .prim) return leafOf(l, .plain);
    const int_owner = x.sym.owner.? == .fixed and x.sym.owner.?.fixed.int() != null;
    if (x.sym.method == .not) return leafOf(l, .negated);
    if (int_owner and x.sym.method == .is_lte) return leafOf(l, .lte);
    if (int_owner and x.sym.method == .is_lt) return leafOf(l, .lt);
    leafOf(l, .plain);
}

fn leafOf(l: *Leaves, class: enum { negated, plain, lte, lt }) void {
    if (l.first_flips == null) l.first_flips = class == .negated or class == .lte;
    switch (class) {
        .negated => l.negated += 1,
        .plain => l.plain += 1,
        .lte => l.lte += 1,
        .lt => l.lt += 1,
    }
}

fn ofRuleIn(arena: Allocator, rule: table.Rule, ctx: *Ctx) Allocator.Error!RuleTerms {
    // A switch, `And` or `Or` rule's one pattern describes the whole node.
    if (rule.root == .switch_ or rule.root == .and_ or rule.root == .or_) return .{ .lhs = try ofPat(arena, rule.args[0], ctx), .rhs = try ofTmpl(arena, rule.result, ctx) };
    const root_sym: Sym = if (rule.root_prim) |rp|
        .{ .op = .prim, .method = rp.method, .owner = rp.owner }
    else
        .{ .op = rule.root };
    const args = try ofArgs(arena, rule.args, ctx, root_sym);
    return .{ .lhs = .{ .app = .{ .sym = root_sym, .args = args } }, .rhs = try ofTmpl(arena, rule.result, ctx) };
}

// A prim's arguments, a run spliced in. A chain of fewer than two operands
// is not a node, so its instance is left out.
fn ofArgs(arena: Allocator, pats: []const table.Pat, ctx: *Ctx, sym: Sym) Allocator.Error![]const Term {
    var args: std.ArrayList(Term) = .empty;
    for (pats) |p| switch (p) {
        .rest => |k| try args.appendSlice(arena, ctx.seqs[k]),
        // At `I64`, the type step 1 instantiates owner variables at.
        .identity => try args.append(arena, .{ .app = .{ .sym = .{ .op = .lit, .int = @intCast(prims.identityInt(.i64, sym.method.?).?) }, .args = &.{} } }),
        // The variable stands for the literal wherever the result reads it.
        .absorbing => |k| {
            const lit: Term = .{ .app = .{ .sym = .{ .op = .lit, .int = @intCast(prims.absorbingInt(.i64, sym.method.?).?) }, .args = &.{} } };
            ctx.shapes[k] = lit;
            try args.append(arena, lit);
        },
        .any, .lit_bool, .lit_int, .prim, .op, .component, .bool_switch, .connective, .same_arms, .tag_arm, .lit_switch => try args.append(arena, try ofPat(arena, p, ctx)),
    };
    if (sym.op == .prim and prims.associativeOf(sym.method.?) and args.items.len < 2) ctx.empty = true;
    return args.items;
}

fn ofPat(arena: Allocator, p: table.Pat, ctx: *Ctx) Allocator.Error!Term {
    return switch (p) {
        .any => |k| ctx.shapes[k] orelse .{ .var_ = k },
        .lit_bool => |b| .{ .app = .{ .sym = .{ .op = .lit, .lit = b }, .args = &.{} } },
        .lit_int => |v| .{ .app = .{ .sym = .{ .op = .lit, .int = v }, .args = &.{} } },
        .prim => |pp| blk: {
            const sym: Sym = .{ .op = .prim, .method = pp.method, .owner = pp.owner };
            break :blk .{ .app = .{ .sym = sym, .args = try ofArgs(arena, pp.args, ctx, sym) } };
        },
        // `ofArgs` reads these among a chain's arguments.
        .rest, .identity, .absorbing => unreachable, // ofArgs reads these among a chain's arguments
        .op => |op| blk: {
            const args = try arena.alloc(Term, op.args.len);
            for (op.args, args) |sub, *a| a.* = try ofPat(arena, sub, ctx);
            break :blk .{ .app = .{ .sym = .{ .op = op.op }, .args = args } };
        },
        // The construction with only the component the root reads: its other
        // components may not exist, so a count over the term never exceeds
        // the count over the node the pattern matches.
        .component => |c| blk: {
            const args = try arena.alloc(Term, 1);
            args[0] = .{ .var_ = c.bind };
            break :blk .{ .app = .{ .sym = .{ .op = c.op }, .args = args } };
        },
        .bool_switch => |bs| blk: {
            const args = try arena.alloc(Term, 3);
            args[0] = try ofPat(arena, bs.scrutinee.*, ctx);
            for (bs.arms, args[1..]) |arm, *a| a.* = try ofArm(arena, arm, ctx);
            break :blk .{ .app = .{ .sym = .{ .op = .switch_ }, .args = args } };
        },
        // Two arms, as over a `Bool`: every scrutinee sort has at least two members.
        .same_arms => |sa| blk: {
            const args = try arena.alloc(Term, 3);
            args[0] = try ofPat(arena, sa.scrutinee.*, ctx);
            args[1] = .{ .var_ = region_base + sa.region };
            args[2] = args[1];
            break :blk .{ .app = .{ .sym = .{ .op = .switch_ }, .args = args } };
        },
        // Over the one-member union of step 1's pattern terms, the one arm the tag selects.
        .tag_arm => |k| blk: {
            const args = try arena.alloc(Term, 2);
            const payload = try arena.alloc(Term, 1);
            payload[0] = .{ .var_ = 0 };
            args[0] = .{ .app = .{ .sym = .{ .op = .tag }, .args = payload } };
            args[1] = .{ .var_ = region_base + k };
            break :blk .{ .app = .{ .sym = .{ .op = .switch_ }, .args = args } };
        },
        .lit_switch => |ls| blk: {
            const args = try arena.alloc(Term, 4);
            args[0] = try ofPat(arena, ls.scrutinee.*, ctx);
            args[1] = try ofPat(arena, ls.key.*, ctx);
            for (ls.arms, args[2..]) |arm, *a| a.* = try ofArm(arena, arm, ctx);
            break :blk .{ .app = .{ .sym = .{ .op = .switch_, .index = 1 }, .args = args } };
        },
        .connective => |c| blk: {
            var args: std.ArrayList(Term) = .empty;
            for (c.operands) |o| switch (o) {
                .arm => |a| try args.append(arena, try ofArm(arena, a, ctx)),
                .rest => |k| try args.appendSlice(arena, ctx.seqs[k]),
            };
            if (args.items.len == 0) ctx.empty = true;
            break :blk .{ .app = .{ .sym = .{ .op = c.op }, .args = args.items } };
        },
    };
}

// An arm reads as the value it delivers.
fn ofArm(arena: Allocator, arm: table.Arm, ctx: *Ctx) Allocator.Error!Term {
    return switch (arm) {
        .lit => |b| .{ .app = .{ .sym = .{ .op = .lit, .lit = b }, .args = &.{} } },
        .region => |k| .{ .var_ = region_base + k },
        .value => |p| ofPat(arena, p.*, ctx),
    };
}

fn ofTmpl(arena: Allocator, t: table.Tmpl, ctx: *Ctx) Allocator.Error!Term {
    return switch (t) {
        .var_ => |k| ctx.shapes[k] orelse .{ .var_ = k },
        .prim => |pp| blk: {
            var args: std.ArrayList(Term) = .empty;
            for (pp.args) |sub| switch (sub) {
                .rest => |k| try args.appendSlice(arena, ctx.seqs[k]),
                .var_, .prim, .bool_switch, .and_, .or_, .region_value, .lit_bool, .lit_int, .folded, .negation, .lit_switch => try args.append(arena, try ofTmpl(arena, sub, ctx)),
            };
            if (args.items.len == 0) ctx.empty = true;
            // A one-operand chain is its operand, as the builder builds it.
            if (args.items.len == 1 and prims.associativeOf(pp.method)) break :blk args.items[0];
            break :blk .{ .app = .{ .sym = .{ .op = .prim, .method = pp.method, .owner = pp.owner }, .args = args.items } };
        },
        .rest => unreachable, // rest is expanded among a chain's arguments above
        .bool_switch => |bs| blk: {
            const args = try arena.alloc(Term, 3);
            args[0] = try ofTmpl(arena, bs.scrutinee.*, ctx);
            for (bs.arms, args[1..]) |arm, *a| a.* = switch (arm) {
                .region => |k| .{ .var_ = region_base + k },
                .value => |v| try ofTmpl(arena, v.*, ctx),
            };
            break :blk .{ .app = .{ .sym = .{ .op = .switch_ }, .args = args } };
        },
        .and_, .or_ => |ops| blk: {
            var args: std.ArrayList(Term) = .empty;
            for (ops) |o| switch (o) {
                .value => |v| try args.append(arena, try ofTmpl(arena, v.*, ctx)),
                .region => |k| try args.append(arena, .{ .var_ = region_base + k }),
                .rest => |k| try args.appendSlice(arena, ctx.seqs[k]),
                .negated_rest => |k| for (ctx.seqs[k]) |e| try args.append(arena, try notOf(arena, e)),
            };
            if (args.items.len == 0) ctx.empty = true;
            // A one-operand `And` or `Or` is its operand, as the builder builds it.
            if (args.items.len == 1) break :blk args.items[0];
            break :blk .{ .app = .{ .sym = .{ .op = if (t == .and_) .and_ else .or_ }, .args = args.items } };
        },
        .region_value => |k| .{ .var_ = region_base + k },
        .lit_bool => |b| .{ .app = .{ .sym = .{ .op = .lit, .lit = b }, .args = &.{} } },
        // The term reads the literal's type from its context, as it does a variable's.
        .lit_int => |l| .{ .app = .{ .sym = .{ .op = .lit, .int = l.value }, .args = &.{} } },
        .negation => |v| try notOf(arena, try ofTmpl(arena, v.*, ctx)),
        .lit_switch => |ls| blk: {
            const args = try arena.alloc(Term, 4);
            args[0] = try ofTmpl(arena, ls.scrutinee.*, ctx);
            args[1] = try ofTmpl(arena, ls.key.*, ctx);
            for (ls.arms, args[2..]) |arm, *a| a.* = switch (arm) {
                .region => |k| .{ .var_ = region_base + k },
                .value => |v| try ofTmpl(arena, v.*, ctx),
            };
            break :blk .{ .app = .{ .sym = .{ .op = .switch_, .index = 1 }, .args = args } };
        },
        .folded => unreachable, // folded templates occur only in results of evaluation rows, not in term patterns
    };
}

/// The number of owner variables a substitution can bind.
pub const owner_bound = 8;

/// A substitution: variable `v` maps to `map[v]` when set, and owner
/// variable `k` to `owners[k]`.
pub const Subst = struct {
    map: []?Term,
    owners: [owner_bound]?table.OwnerPat = @splat(null),

    /// The owner an owner pattern stands for under this substitution.
    pub fn owner(self: Subst, o: table.OwnerPat) table.OwnerPat {
        var cur = o;
        while (true) switch (cur) {
            .fixed => return cur,
            .bind => |k| cur = self.owners[k] orelse return cur,
        };
    }

    /// The symbol with its owner resolved.
    pub fn sym(self: Subst, s: Sym) Sym {
        var out = s;
        if (s.owner) |o| out.owner = self.owner(o);
        return out;
    }

    /// The term with every bound variable replaced, repeatedly.
    pub fn apply(self: Subst, arena: Allocator, t: Term) Allocator.Error!Term {
        return switch (t) {
            .var_ => |v| if (v < self.map.len and self.map[v] != null) self.apply(arena, self.map[v].?) else t,
            .app => |x| blk: {
                const args = try arena.alloc(Term, x.args.len);
                for (x.args, args) |a, *o| o.* = try self.apply(arena, a);
                break :blk .{ .app = .{ .sym = self.sym(x.sym), .args = args } };
            },
        };
    }
};

/// The most general unifier of `a` and `b`, or null. Variables range below `bound`.
pub fn unify(arena: Allocator, a: Term, b: Term, bound: Var) Allocator.Error!?Subst {
    const map = try arena.alloc(?Term, bound);
    @memset(map, null);
    var s: Subst = .{ .map = map };
    if (!try unifyInto(arena, &s, a, b)) return null;
    return s;
}

fn unifySym(s: *Subst, a: Sym, b: Sym) bool {
    if (a.op != b.op or a.method != b.method or a.lit != b.lit or a.int != b.int or a.index != b.index) return false;
    const ao = a.owner orelse return b.owner == null;
    const bo = b.owner orelse return false;
    const x = s.owner(ao);
    const y = s.owner(bo);
    if (ownerEql(x, y)) return true;
    switch (x) {
        .bind => |k| {
            s.owners[k] = y;
            return true;
        },
        .fixed => switch (y) {
            .bind => |k| {
                s.owners[k] = x;
                return true;
            },
            .fixed => return false,
        },
    }
}

fn unifyInto(arena: Allocator, s: *Subst, a0: Term, b0: Term) Allocator.Error!bool {
    const a = try s.apply(arena, a0);
    const b = try s.apply(arena, b0);
    switch (a) {
        .var_ => |v| {
            if (b == .var_ and b.var_ == v) return true;
            if (b.occurs(v)) return false;
            s.map[v] = b;
            return true;
        },
        .app => |x| switch (b) {
            .var_ => return unifyInto(arena, s, b, a),
            .app => |y| {
                if (!unifySym(s, x.sym, y.sym) or x.args.len != y.args.len) return false;
                for (x.args, y.args) |p, q| {
                    if (!try unifyInto(arena, s, p, q)) return false;
                }
                return true;
            },
        },
    }
}

/// The term with every variable renumbered by `offset` and every owner
/// variable by `owner_offset`, to keep two rules' variables apart.
pub fn shift(arena: Allocator, t: Term, offset: Var, owner_offset: u8) Allocator.Error!Term {
    return switch (t) {
        .var_ => |v| .{ .var_ = v + offset },
        .app => |x| blk: {
            const args = try arena.alloc(Term, x.args.len);
            for (x.args, args) |a, *o| o.* = try shift(arena, a, offset, owner_offset);
            var sym = x.sym;
            if (sym.owner) |o| switch (o) {
                .bind => |k| sym.owner = .{ .bind = k + owner_offset },
                .fixed => {},
            };
            break :blk .{ .app = .{ .sym = sym, .args = args } };
        },
    };
}

/// A copy of `t` in `arena`.
pub fn dupe(arena: Allocator, t: Term) Allocator.Error!Term {
    const x = switch (t) {
        .var_ => return t,
        .app => |x| x,
    };
    const args = try arena.alloc(Term, x.args.len);
    for (args, x.args) |*o, a| o.* = try dupe(arena, a);
    return .{ .app = .{ .sym = x.sym, .args = args } };
}

/// The subterm at `path`, a list of argument positions from the root.
pub fn at(t: Term, path: []const u8) Term {
    var cur = t;
    for (path) |i| cur = cur.app.args[i];
    return cur;
}

/// The term with the subterm at `path` replaced by `with`.
pub fn replaceAt(arena: Allocator, t: Term, path: []const u8, with: Term) Allocator.Error!Term {
    if (path.len == 0) return with;
    const x = t.app;
    const args = try arena.dupe(Term, x.args);
    args[path[0]] = try replaceAt(arena, x.args[path[0]], path[1..], with);
    return .{ .app = .{ .sym = x.sym, .args = args } };
}

/// Write a term, `x0`, `Bool.not(x0)`, `field(record(x0))`.
pub fn write(w: *std.Io.Writer, t: Term) std.Io.Writer.Error!void {
    return writeRenamed(w, t, null);
}

/// Write a term with variable `order[i]` named `xi`, or with its own
/// numbers when `order` is null.
pub fn writeRenamed(w: *std.Io.Writer, t: Term, order: ?[]const Var) std.Io.Writer.Error!void {
    switch (t) {
        .var_ => |v| try w.print("x{d}", .{if (order) |o| std.mem.findScalar(Var, o, v).? else v}),
        .app => |x| {
            if (x.sym.lit) |b| return w.writeAll(if (b) "True" else "False");
            if (x.sym.int) |n| return w.print("{d}", .{n});
            if (x.sym.method) |m| {
                const owner = x.sym.owner.?;
                switch (owner) {
                    .fixed => |o| try w.print("{s}.{s}", .{ o.text(), @tagName(m) }),
                    .bind => |k| try w.print("o{d}.{s}", .{ k, @tagName(m) }),
                }
            } else try w.writeAll(@tagName(x.sym.op));
            if (x.sym.index) |i| try w.print("#{d}", .{i});
            try w.writeAll("(");
            for (x.args, 0..) |a, i| {
                if (i > 0) try w.writeAll(", ");
                try writeRenamed(w, a, order);
            }
            try w.writeAll(")");
        },
    }
}

/// The term a built value unfolds to: an arm or operand reads as the value
/// its region delivers, and a row parameter `k` as variable `k`.
///
/// A `Tag` or `Payload` reads back with the position of its tag in its union,
/// which is how a term names a tag (`Sym`).
pub fn readBack(arena: Allocator, store: *const reify.ir.Store, types: *const reify.types.Types, ref: reify.ir.Ref) Allocator.Error!Term {
    switch (ref.kind) {
        .row_param => return .{ .var_ = @intCast(ref.output) },
        .region_param => return .{ .var_ = std.math.maxInt(Var) },
        .node => {},
    }
    const nd = store.node(ref.nodeId());
    const args = store.refSlice(nd.args);
    const regions = store.regionSlice(nd.regions);
    // A literal switch's keys follow its scrutinee (`Sym`).
    const keys = if (nd.op == .switch_) store.wordSlice(nd.aux) else &.{};
    const out = try arena.alloc(Term, args.len + keys.len + regions.len);
    for (args, out[0..args.len]) |a, *o| o.* = try readBack(arena, store, types, a);
    for (keys, out[args.len..][0..keys.len]) |k, *o| {
        const bits = store.lit(reify.ir.LitId.of(k)).value.int;
        o.* = .{ .app = .{ .sym = .{ .op = .lit, .int = @truncate(@as(i128, @bitCast(bits))) }, .args = &.{} } };
    }
    for (regions, out[args.len + keys.len ..]) |r, *o| {
        const end = store.region(r).end;
        o.* = if (end.kind == .value and end.refs.len == 1) try readBack(arena, store, types, store.refSlice(end.refs)[0]) else .{ .var_ = std.math.maxInt(Var) };
    }
    var sym: Sym = .{ .op = nd.op };
    switch (nd.op) {
        .prim => {
            const p = prims.get(reify.ir.PrimId.of(nd.payload));
            sym.method = p.method;
            sym.owner = .{ .fixed = p.owner };
        },
        .lit => switch (store.lit(reify.ir.LitId.of(nd.payload)).value) {
            .bool_ => |v| sym.lit = v,
            .int => |bits| sym.int = @truncate(@as(i128, @bitCast(bits))),
            .float, .str, .dec, .bytes => {},
        },
        .field, .index => sym.index = nd.payload,
        .tag => sym.index = types.memberIndex(store.tySlice(nd.tys)[0], reify.types.NameId.of(nd.payload)).?,
        .payload => sym.index = types.memberIndex(store.refTy(store.region(nd.region).row, args[0]), reify.types.NameId.of(nd.payload)).?,
        .switch_ => if (keys.len > 0) {
            sym.index = @intCast(keys.len);
        },
        .crash, .derived, .record, .tuple, .list, .wrap, .closure, .elem, .opt_field, .unwrap, .call, .and_, .or_, .for_range, .for_list, .loop, .lambda, .apply => {},
    }
    return .{ .app = .{ .sym = sym, .args = out } };
}

/// Why a term's text did not parse.
pub const ParseError = error{InvalidTerm} || Allocator.Error;

/// Parse the text `write` gives back into a term.
pub fn parse(arena: Allocator, text: []const u8) ParseError!Term {
    var p: Parser = .{ .arena = arena, .text = text };
    const t = try p.term();
    if (p.pos != text.len) return error.InvalidTerm;
    return t;
}

const Parser = struct {
    arena: Allocator,
    text: []const u8,
    pos: usize = 0,

    fn skipSpace(self: *Parser) void {
        while (self.pos < self.text.len and self.text[self.pos] == ' ') self.pos += 1;
    }

    fn term(self: *Parser) ParseError!Term {
        self.skipSpace();
        const start = self.pos;
        while (self.pos < self.text.len) : (self.pos += 1) {
            const c = self.text[self.pos];
            if (!(std.ascii.isAlphanumeric(c) or c == '_' or c == '.' or c == '#' or c == '-')) break;
        }
        const word = self.text[start..self.pos];
        if (word.len == 0) return error.InvalidTerm;
        if (word[0] == 'x' and word.len > 1 and std.ascii.isDigit(word[1])) {
            return .{ .var_ = std.fmt.parseInt(Var, word[1..], 10) catch return error.InvalidTerm };
        }
        if (std.mem.eql(u8, word, "True") or std.mem.eql(u8, word, "False")) {
            return .{ .app = .{ .sym = .{ .op = .lit, .lit = word[0] == 'T' }, .args = &.{} } };
        }
        if (std.ascii.isDigit(word[0]) or word[0] == '-') {
            return .{ .app = .{ .sym = .{ .op = .lit, .int = std.fmt.parseInt(i64, word, 10) catch return error.InvalidTerm }, .args = &.{} } };
        }
        const sym = try symOf(word);
        if (self.pos >= self.text.len or self.text[self.pos] != '(') return error.InvalidTerm;
        self.pos += 1;
        var args: std.ArrayList(Term) = .empty;
        self.skipSpace();
        if (self.pos < self.text.len and self.text[self.pos] == ')') {
            self.pos += 1;
        } else while (true) {
            try args.append(self.arena, try self.term());
            self.skipSpace();
            if (self.pos >= self.text.len) return error.InvalidTerm;
            const c = self.text[self.pos];
            self.pos += 1;
            if (c == ')') break;
            if (c != ',') return error.InvalidTerm;
        }
        return .{ .app = .{ .sym = sym, .args = try args.toOwnedSlice(self.arena) } };
    }

    fn symOf(word: []const u8) ParseError!Sym {
        if (std.mem.findScalarLast(u8, word, '.')) |dot| {
            const method = std.meta.stringToEnum(prims.Method, word[dot + 1 ..]) orelse return error.InvalidTerm;
            const owner_text = word[0..dot];
            if (owner_text.len > 1 and owner_text[0] == 'o' and std.ascii.isDigit(owner_text[1])) {
                return .{ .op = .prim, .method = method, .owner = .{ .bind = std.fmt.parseInt(u8, owner_text[1..], 10) catch return error.InvalidTerm } };
            }
            for (std.enums.values(prims.Owner)) |o| {
                if (std.mem.eql(u8, o.text(), owner_text)) return .{ .op = .prim, .method = method, .owner = .{ .fixed = o } };
            }
            return error.InvalidTerm;
        }
        const hash = std.mem.findScalar(u8, word, '#');
        const op = std.meta.stringToEnum(Op, word[0 .. hash orelse word.len]) orelse return error.InvalidTerm;
        var sym: Sym = .{ .op = op };
        if (hash) |h| sym.index = std.fmt.parseInt(u32, word[h + 1 ..], 10) catch return error.InvalidTerm;
        return sym;
    }
};

/// The least general generalization of `a` and `b` (Plotkin, Reynolds): equal
/// symbols stay, and each distinct pair of differing subterms becomes one
/// fresh variable, numbered from `first`.
pub fn antiUnify(arena: Allocator, a: Term, b: Term, first: Var) Allocator.Error!Term {
    var pairs: std.ArrayList([2]Term) = .empty;
    return lgg(arena, &pairs, a, b, first);
}

fn lgg(arena: Allocator, pairs: *std.ArrayList([2]Term), a: Term, b: Term, first: Var) Allocator.Error!Term {
    if (a == .app and b == .app and a.app.sym.eql(b.app.sym) and a.app.args.len == b.app.args.len) {
        const args = try arena.alloc(Term, a.app.args.len);
        for (a.app.args, b.app.args, args) |p, q, *o| o.* = try lgg(arena, pairs, p, q, first);
        return .{ .app = .{ .sym = a.app.sym, .args = args } };
    }
    if (a.eql(b)) return a;
    for (pairs.items, 0..) |pair, i| {
        if (pair[0].eql(a) and pair[1].eql(b)) return .{ .var_ = first + @as(Var, @intCast(i)) };
    }
    try pairs.append(arena, .{ a, b });
    return .{ .var_ = first + @as(Var, @intCast(pairs.items.len - 1)) };
}

const testing = std.testing;

fn app(sym: Sym, args: []const Term) Term {
    return .{ .app = .{ .sym = sym, .args = args } };
}

test "unify finds the overlap of N13h with itself" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    // not(x1) against the whole of not(not(x0)): x1 = not(x0).
    const lhs = app(not_sym, &.{app(not_sym, &.{.{ .var_ = 0 }})});
    const sub = app(not_sym, &.{.{ .var_ = 1 }});
    const s = (try unify(a, lhs, sub, 2)).?;
    try testing.expect((try s.apply(a, sub)).eql(try s.apply(a, lhs)));
    try testing.expect((try s.apply(a, .{ .var_ = 1 })).eql(lhs.app.args[0]));
    // x0 against not(x0) fails the occurs check.
    try testing.expect(try unify(a, .{ .var_ = 0 }, app(not_sym, &.{.{ .var_ = 0 }}), 1) == null);
}

test "anti-unification keeps shared structure and names each difference once" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const t = app(.{ .op = .lit, .lit = true }, &.{});
    const f = app(.{ .op = .lit, .lit = false }, &.{});
    const and_sym: Sym = .{ .op = .and_ };
    const g = try antiUnify(a, app(and_sym, &.{ t, t }), app(and_sym, &.{ f, f }), 0);
    try testing.expect(g.eql(app(and_sym, &.{ .{ .var_ = 0 }, .{ .var_ = 0 } })));
}

test "a written term parses back to itself" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    for ([_][]const u8{ "switch_(and_(x0, Bool.not(x66)), x130, 7)", "o0.is_lte(x1, -2)", "tag#1()", "field#0(record(x2, True))", "Num.I64.plus(x2, 0)" }) |text| {
        const t = try parse(a, text);
        var out: std.Io.Writer.Allocating = .init(a);
        try write(&out.writer, t);
        try testing.expectEqualStrings(text, out.written());
    }
    try testing.expectError(error.InvalidTerm, parse(a, "Frob.not(x0)"));
}

test "every instance of every table row is a pair of terms whose right side uses only left variables" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    for (table.rules) |r| {
        if (r.tier == .evaluation) continue;
        const all = try instances(arena.allocator(), r);
        try testing.expect(all.len > 0);
        for (all) |rt| {
            var v: Var = 0;
            while (v < rt.rhs.varBound()) : (v += 1) {
                if (rt.rhs.occurs(v)) try testing.expect(rt.lhs.occurs(v));
            }
        }
    }
}

test "a row over a sequence reads as its instances up to the bound" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    for (table.rules) |r| {
        if (!std.mem.eql(u8, r.step, "N13t") or r.args[0] != .connective or r.args[0].connective.op != .and_) continue;
        // Runs of 0 to 2 operands: none of length 0 is a node.
        const all = try instances(a, r);
        try testing.expectEqual(@as(usize, 2), all.len);
        var text: std.Io.Writer.Allocating = .init(a);
        try write(&text.writer, all[1].lhs);
        try text.writer.writeAll(" -> ");
        try write(&text.writer, all[1].rhs);
        try testing.expectEqualStrings("Bool.not(and_(x48, x49)) -> or_(Bool.not(x48), Bool.not(x49))", text.written());
    }
}

test "the polarity row reads as the formulas whose negation is the better scrutinee" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    for (table.rules) |r| {
        if (!std.mem.eql(u8, r.step, "N13s")) continue;
        var text: std.Io.Writer.Allocating = .init(a);
        for (try instances(a, r)) |rt| {
            try write(&text.writer, rt.lhs);
            try text.writer.writeAll(" -> ");
            try write(&text.writer, rt.rhs);
            try text.writer.writeAll("\n");
        }
        const got = text.written();
        try testing.expect(std.mem.find(u8, got, "switch_(Bool.not(x56), x64, x65) -> switch_(x56, x65, x64)\n") != null);
        try testing.expect(std.mem.find(u8, got, "switch_(or_(Bool.not(x56), x58), x64, x65) -> switch_(and_(x56, Bool.not(x58)), x65, x64)\n") != null);
        try testing.expect(std.mem.find(u8, got, "switch_(Num.I64.is_lte(x56, x57), x64, x65) -> switch_(Num.I64.is_lt(x57, x56), x65, x64)\n") != null);
        // The better polarity itself is not an instance.
        try testing.expect(std.mem.find(u8, got, "switch_(and_(x56, Bool.not(x58)), x64, x65)") == null);
    }
}
