//! Step 5 of the loop (`roc-reify-rule-derivation.md` 3.5): classify a
//! generalized equation, and write the table row of a first-order rule.

const std = @import("std");
const prims = @import("reify").prims;
const term = @import("term.zig");
const sig_mod = @import("sig.zig");
const order = @import("order.zig");
const prove = @import("prove.zig");
const generalize = @import("generalize.zig");

const Allocator = std.mem.Allocator;
const Term = term.Term;
const Equation = generalize.Equation;

/// The class of a group.
pub const Class = union(enum) {
    /// A first-order rule: oriented, passing the speculation check. `row` is
    /// its table row, or null with `unstated` naming what the pattern
    /// language cannot state.
    f_rule: struct { row: ?[]const u8, unstated: ?[]const u8 },
    /// Proved, but not orientable, or failing the speculation check; the criterion.
    unoriented: []const u8,
    /// Joined by a hand-written algorithm, named here.
    context: []const u8,
    /// Excluded by a criterion of 3.6, named here.
    out_of_scope: []const u8,
    /// The speculation check could not decide; the reason.
    unproved: []const u8,
};

/// A classified equation, oriented when it orients.
pub const Verdict = struct {
    eq: Equation,
    class: Class,
};

fn isCommutative(sym: term.Sym) bool {
    if (sym.op == .and_ or sym.op == .or_) return true;
    if (sym.op != .prim) return false;
    return switch (sym.method.?) {
        .is_eq, .plus, .times, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor => true,
        .is_lt, .is_lte, .is_gt, .is_gte, .not, .minus, .div_trunc, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect => false,
    };
}

// Whether `a` and `b` differ only in the operand order of commutative nodes.
fn commuted(a: Term, b: Term) bool {
    if (a.eql(b)) return true;
    const x = switch (a) {
        .var_ => return false,
        .app => |x| x,
    };
    const y = switch (b) {
        .var_ => return false,
        .app => |y| y,
    };
    if (!x.sym.eql(y.sym) or x.args.len != y.args.len) return false;
    const straight = for (x.args, y.args) |p, q| {
        if (!commuted(p, q)) break false;
    } else true;
    if (straight) return true;
    return isCommutative(x.sym) and x.args.len == 2 and commuted(x.args[0], y.args[1]) and commuted(x.args[1], y.args[0]);
}

// Whether `t` has a variable that `conds` does not fix to a literal.
fn hasOpenVar(t: Term, conds: []const generalize.Cond) bool {
    return switch (t) {
        .var_ => |v| for (conds) |c| switch (c) {
            .is_lit, .nonzero_lit => |k| if (k == v) break false,
            .int_owner, .speculatable => {},
        } else true,
        .app => |x| for (x.args) |a| {
            if (hasOpenVar(a, conds)) break true;
        } else false,
    };
}

fn occursIn(needle: Term, t: Term) bool {
    if (needle.eql(t)) return true;
    return switch (t) {
        .var_ => false,
        .app => |x| for (x.args) |a| {
            if (occursIn(needle, a)) break true;
        } else false,
    };
}

// The algorithm that decides a test a dominating test already decided: a
// switch whose scrutinee recurs in an arm (N13d), or an `And`/`Or` whose
// first operand recurs in the second (N13p).
fn dominated(t: Term) ?[]const u8 {
    const x = switch (t) {
        .var_ => return null,
        .app => |x| x,
    };
    switch (x.sym.op) {
        .switch_ => for (x.args[1..]) |arm| if (occursIn(x.args[0], arm)) return "N13d",
        .and_, .or_ => if (occursIn(x.args[0], x.args[1])) return "N13p",
        .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .for_range, .for_list, .loop, .lambda, .apply => {},
    }
    for (x.args) |a| if (dominated(a)) |alg| return alg;
    return null;
}

/// Classify `eq`, which step 3 proved.
pub fn run(arena: Allocator, prover: *prove.Prover, vars: sig_mod.Vars, eq: Equation) prove.Error!Verdict {
    if (commuted(eq.lhs, eq.rhs)) return .{ .eq = eq, .class = .{ .out_of_scope = "operand order of a commutative op (normal-form 7.2)" } };
    // Over literals only, the equation is constant folding.
    if (!hasOpenVar(eq.lhs, eq.conds) and !hasOpenVar(eq.rhs, eq.conds)) return .{ .eq = eq, .class = .{ .context = "N13j" } };
    if (dominated(eq.lhs) orelse dominated(eq.rhs)) |alg| return .{ .eq = eq, .class = .{ .context = alg } };
    var oriented = eq;
    const lits = try eq.lits(arena);
    if (!order.orient(eq.lhs, eq.rhs, lits).oriented) {
        if (!order.orient(eq.rhs, eq.lhs, lits).oriented) return .{ .eq = eq, .class = .{ .unoriented = "fails orientation in both directions" } };
        oriented = .{ .lhs = eq.rhs, .rhs = eq.lhs, .conds = eq.conds };
    }
    switch (try prover.speculation(vars, oriented.lhs, oriented.rhs, try oriented.assumptions(arena), oriented.widths())) {
        .proved => {},
        .refuted => return .{ .eq = oriented, .class = .{ .unoriented = "fails the speculation check in its preferred direction" } },
        .unknown => |why| return .{ .eq = oriented, .class = .{ .unproved = why } },
    }
    var rw: RowWriter = .{ .arena = arena, .sorts = vars, .eq = oriented };
    const row = rw.write() catch |err| switch (err) {
        error.Unstated => return .{ .eq = oriented, .class = .{ .f_rule = .{ .row = null, .unstated = rw.unstated } } },
        else => |e| return e,
    };
    return .{ .eq = oriented, .class = .{ .f_rule = .{ .row = row, .unstated = null } } };
}

// Whether every operand of `m` has its owner's type.
fn operandsAreOwner(m: prims.Method) bool {
    return switch (m) {
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .is_empty, .collect => true,
        .len, .get, .append, .map, .keep_if, .fold => false,
    };
}

// Whether `m`'s result has its owner's type.
fn resultIsOwner(m: prims.Method) bool {
    return switch (m) {
        .not, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .append, .map, .keep_if => true,
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .len, .get, .is_empty, .fold, .collect => false,
    };
}

/// Writes the table row of an oriented equation, in `rules/table.zig`'s syntax.
const RowWriter = struct {
    arena: Allocator,
    sorts: sig_mod.Vars,
    eq: Equation,
    unstated: []const u8 = "",
    /// Per term variable: its pattern variable, region variable, or neither yet.
    vars: std.ArrayList(struct { v: term.Var, kind: enum { pattern, region }, k: u8 }) = .empty,
    pattern_count: u8 = 0,
    region_count: u8 = 0,
    /// The variables the left side reads as a value, not only as an arm: an
    /// arm that is one of them matches its value, not its region. The right
    /// side reads a region variable as a value through `region_value`.
    value_vars: std.ArrayList(term.Var) = .empty,

    const Error = error{Unstated} || Allocator.Error || std.Io.Writer.Error;

    fn fail(self: *RowWriter, why: []const u8) Error {
        self.unstated = why;
        return error.Unstated;
    }

    fn print(self: *RowWriter, comptime fmt: []const u8, args: anytype) Error![]const u8 {
        return std.fmt.allocPrint(self.arena, fmt, args);
    }

    // A slice literal as `zig fmt` writes it, so an admitted row needs no reformatting.
    fn list(self: *RowWriter, items: []const []const u8) Error![]const u8 {
        return switch (items.len) {
            0 => "&.{}",
            1 => self.print("&.{{{s}}}", .{items[0]}),
            else => self.print("&.{{ {s} }}", .{try std.mem.join(self.arena, ", ", items)}),
        };
    }

    fn bind(self: *RowWriter, v: term.Var, region: bool) Error!u8 {
        for (self.vars.items) |e| if (e.v == v) {
            if ((e.kind == .region) != region) return self.fail("a variable read both as a value and as an arm");
            return e.k;
        };
        const k = if (region) self.region_count else self.pattern_count;
        if (region) self.region_count += 1 else self.pattern_count += 1;
        try self.vars.append(self.arena, .{ .v = v, .kind = if (region) .region else .pattern, .k = k });
        return k;
    }

    fn lookup(self: *RowWriter, v: term.Var) ?@TypeOf(self.vars.items[0]) {
        for (self.vars.items) |e| if (e.v == v) return e;
        return null;
    }

    fn owner(self: *RowWriter, sym: term.Sym) Error![]const u8 {
        return switch (sym.owner.?) {
            .fixed => |o| self.print(".{{ .fixed = .{s} }}", .{@tagName(o)}),
            .bind => |k| self.print(".{{ .bind = {d} }}", .{k}),
        };
    }

    fn pat(self: *RowWriter, t: Term) Error![]const u8 {
        const x = switch (t) {
            .var_ => |v| return self.print(".{{ .any = {d} }}", .{try self.bind(v, false)}),
            .app => |x| x,
        };
        switch (x.sym.op) {
            .lit => if (x.sym.lit) |b| return self.print(".{{ .lit_bool = {} }}", .{b}) else return self.print(".{{ .lit_int = {d} }}", .{x.sym.int.?}),
            .prim => {
                var args: std.ArrayList([]const u8) = .empty;
                for (x.args) |a| try args.append(self.arena, try self.pat(a));
                return self.print(".{{ .prim = .{{ .method = .{s}, .owner = {s}, .args = {s} }} }}", .{ @tagName(x.sym.method.?), try self.owner(x.sym), try self.list(args.items) });
            },
            .switch_ => if (term.litKeys(x)) |n| {
                if (n != 1) return self.fail("a literal switch with more than one key");
                return self.print(".{{ .lit_switch = .{{ .scrutinee = &{s}, .owner = {s}, .key = &{s}, .arms = .{{ {s}, {s} }} }} }}", .{ try self.pat(x.args[0]), self.intOwner(), try self.key(x.args[1]), try self.arm(x.args[2]), try self.arm(x.args[3]) });
            } else return self.print(".{{ .bool_switch = .{{ .scrutinee = &{s}, .arms = .{{ {s}, {s} }} }} }}", .{ try self.boolScrutinee(x.args[0]), try self.arm(x.args[1]), try self.arm(x.args[2]) }),
            .and_, .or_ => {
                var elems: std.ArrayList([]const u8) = .empty;
                for (x.args, 0..) |a, i| try elems.append(self.arena, try self.print(".{{ .arm = {s} }}", .{if (i == 0) try self.firstArm(a) else try self.arm(a)}));
                return self.print(".{{ .connective = .{{ .op = .{s}, .operands = {s} }} }}", .{ @tagName(x.sym.op), try self.list(elems.items) });
            },
            // `Wrap` and `Unwrap` have no payload, so the table's op pattern states them.
            .wrap, .unwrap => return self.print(".{{ .op = .{{ .op = .{s}, .args = &.{{{s}}} }} }}", .{ @tagName(x.sym.op), try self.pat(x.args[0]) }),
            .tag, .payload, .record, .field, .tuple, .index => return self.fail("a pattern over a record, tuple or tag union"),
            .crash, .derived, .list, .closure, .elem, .opt_field, .call, .for_range, .for_list, .loop, .lambda, .apply => unreachable, // signature terms are built only from the enumerated symbols (derive/enumerate.zig)
        }
    }

    // The owner of a literal switch's integer scrutinee: the one owner
    // variable of a rule over every integer type, else `I64`.
    fn intOwner(self: *RowWriter) []const u8 {
        for (self.eq.conds) |c| if (c == .int_owner) return ".{ .bind = 0 }";
        return ".{ .fixed = .i64 }";
    }

    // A key: a variable, which the switch's form makes a literal. A row over
    // one named key is not stated; generalization lifts the key.
    fn key(self: *RowWriter, t: Term) Error![]const u8 {
        if (t != .var_) return self.fail("a literal switch whose key is not a variable");
        return self.pat(t);
    }

    // The table's switch patterns are over `Bool` scrutinees.
    fn boolScrutinee(self: *RowWriter, t: Term) Error![]const u8 {
        if (sig_mod.sortOf(self.sorts, t) != .bool) return self.fail("a switch on a tag union");
        return self.pat(t);
    }

    fn arm(self: *RowWriter, t: Term) Error![]const u8 {
        const x = switch (t) {
            .var_ => |v| {
                if (std.mem.findScalar(term.Var, self.value_vars.items, v) != null) return self.print(".{{ .value = &{s} }}", .{try self.pat(t)});
                return self.print(".{{ .region = {d} }}", .{try self.bind(v, true)});
            },
            .app => |x| x,
        };
        if (x.sym.op == .lit) if (x.sym.lit) |b| return self.print(".{{ .lit = {} }}", .{b});
        return self.print(".{{ .value = &{s} }}", .{try self.pat(t)});
    }

    // The first operand of an `And` or `Or` is a value, not a region.
    fn firstArm(self: *RowWriter, t: Term) Error![]const u8 {
        if (t == .app and t.app.sym.op == .lit) if (t.app.sym.lit) |b| return self.print(".{{ .lit = {} }}", .{b});
        return self.print(".{{ .value = &{s} }}", .{try self.pat(t)});
    }

    // `lit_owner` is the owner whose integer type a literal at `t` has, or
    // null where no integer literal can stand.
    fn tmpl(self: *RowWriter, t: Term, lit_owner: ?[]const u8) Error![]const u8 {
        const x = switch (t) {
            .var_ => |v| {
                const e = self.lookup(v) orelse return self.fail("a result variable the left side does not bind");
                return switch (e.kind) {
                    .pattern => self.print(".{{ .var_ = {d} }}", .{e.k}),
                    .region => self.print(".{{ .region_value = {d} }}", .{e.k}),
                };
            },
            .app => |x| x,
        };
        switch (x.sym.op) {
            .lit => {
                if (x.sym.lit) |b| return self.print(".{{ .lit_bool = {} }}", .{b});
                const o = lit_owner orelse return self.fail("an integer literal whose type no owner gives");
                return self.print(".{{ .lit_int = .{{ .value = {d}, .owner = {s} }} }}", .{ x.sym.int.?, o });
            },
            .prim => {
                var args: std.ArrayList([]const u8) = .empty;
                for (x.args) |a| try args.append(self.arena, try self.tmpl(a, if (operandsAreOwner(x.sym.method.?)) try self.owner(x.sym) else null));
                return self.print(".{{ .prim = .{{ .method = .{s}, .owner = {s}, .args = {s} }} }}", .{ @tagName(x.sym.method.?), try self.owner(x.sym), try self.list(args.items) });
            },
            .switch_ => if (term.litKeys(x)) |n| {
                if (n != 1) return self.fail("a literal switch with more than one key");
                if (x.args[1] != .var_) return self.fail("a literal switch whose key is not a variable");
                return self.print(".{{ .lit_switch = .{{ .scrutinee = &{s}, .key = &{s}, .arms = .{{ {s}, {s} }} }} }}", .{ try self.tmpl(x.args[0], null), try self.tmpl(x.args[1], null), try self.placed(x.args[2], lit_owner), try self.placed(x.args[3], lit_owner) });
            } else return self.print(".{{ .bool_switch = .{{ .scrutinee = &{s}, .arms = .{{ {s}, {s} }} }} }}", .{ try self.tmpl(x.args[0], null), try self.placed(x.args[1], lit_owner), try self.placed(x.args[2], lit_owner) }),
            .and_, .or_ => {
                var elems: std.ArrayList([]const u8) = .empty;
                for (x.args, 0..) |a, i| try elems.append(self.arena, if (i == 0) try self.print(".{{ .value = &{s} }}", .{try self.tmpl(a, null)}) else try self.placed(a, null));
                return self.print(".{{ .{s} = {s} }}", .{ @tagName(x.sym.op), try self.list(elems.items) });
            },
            .tag, .payload, .record, .field, .tuple, .index, .wrap, .unwrap => return self.fail("a result over a record, tuple, tag union or nominal"),
            .crash, .derived, .list, .closure, .elem, .opt_field, .call, .for_range, .for_list, .loop, .lambda, .apply => unreachable, // signature terms are built only from the enumerated symbols (derive/enumerate.zig)
        }
    }

    // A result arm or later operand: a bound region placed as it is, or a
    // new region computing the value.
    fn placed(self: *RowWriter, t: Term, lit_owner: ?[]const u8) Error![]const u8 {
        if (t == .var_) if (self.lookup(t.var_)) |e| if (e.kind == .region) return self.print(".{{ .region = {d} }}", .{e.k});
        return self.print(".{{ .value = &{s} }}", .{try self.tmpl(t, lit_owner)});
    }

    // Collect the variables `t` reads in a value position: anywhere but an
    // arm of a switch or an operand after an `And` or `Or`'s first.
    fn collectValueVars(self: *RowWriter, t: Term, as_arm: bool) Error!void {
        const x = switch (t) {
            .var_ => |v| {
                if (!as_arm and std.mem.findScalar(term.Var, self.value_vars.items, v) == null) try self.value_vars.append(self.arena, v);
                return;
            },
            .app => |x| x,
        };
        for (x.args, 0..) |a, i| {
            const arm_position = switch (x.sym.op) {
                // A literal switch's keys are values.
                .switch_ => i > (term.litKeys(x) orelse 0),
                .and_, .or_ => i > 0,
                .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .for_range, .for_list, .loop, .lambda, .apply => false,
            };
            try self.collectValueVars(a, arm_position);
        }
    }

    // The pattern of a projection of a construction whose result is the
    // component it reads: `field#i(record(..., v, ...)) -> v`, the same
    // for `index` of a `tuple`, and `payload#t(tag#t(v)) -> v`. The other components are distinct
    // variables the result drops.
    fn component(self: *RowWriter, root: @FieldType(Term, "app")) Error![]const u8 {
        const c = switch (root.args[0]) {
            .var_ => return self.fail("a projection of a variable"),
            .app => |c| c,
        };
        const want: @import("reify").ir.Op = switch (root.sym.op) {
            .field => .record,
            .index => .tuple,
            .payload => .tag,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => unreachable, // the root was matched as field, index or payload by the caller
        };
        if (c.sym.op != want) return self.fail("a projection of another construction");
        if (root.sym.op == .payload and c.sym.index != root.sym.index) return self.fail("a payload of another member");
        const position: usize = if (root.sym.op == .payload) 0 else root.sym.index.?;
        for (c.args, 0..) |a, i| {
            if (a != .var_) return self.fail("a construction over a non-variable");
            for (c.args[0..i]) |b| if (b.eql(a)) return self.fail("a construction repeating a variable");
        }
        if (position >= c.args.len or !self.eq.rhs.eql(c.args[position])) return self.fail("a projection whose result is not its component");
        return self.print(".{{ .component = .{{ .op = .{s}, .bind = {d} }} }}", .{ @tagName(want), try self.bind(c.args[position].var_, false) });
    }

    // The pattern of a switch whose result is one of its arms: on a `Tag`
    // construction, the arm the tag selects (N13c); on any scrutinee, the arm
    // every arm equals (N13g). Null for any other switch.
    fn wholeSwitch(self: *RowWriter, root: @FieldType(Term, "app")) Error!?[]const u8 {
        const result = switch (self.eq.rhs) {
            .var_ => |v| v,
            .app => return null,
        };
        // A literal switch whose result is an arm is N13c or N13g, which
        // decide it by its keys, not by a row.
        if (term.litKeys(root) != null) return null;
        const arms = root.args[1..];
        for (arms) |a| if (a != .var_) return null;
        const s0 = root.args[0];
        if (s0 == .app and s0.app.sym.op == .tag) {
            const i = s0.app.sym.index.?;
            if (i < arms.len and arms[i].var_ == result and !s0.occurs(result)) return try self.print(".{{ .tag_arm = {d} }}", .{try self.bind(result, true)});
        }
        for (arms) |a| if (a.var_ != result) return null;
        if (s0.occurs(result)) return null;
        const scrutinee = try self.pat(s0);
        return try self.print(".{{ .same_arms = .{{ .scrutinee = &{s}, .region = {d} }} }}", .{ scrutinee, try self.bind(result, true) });
    }

    /// The row's text, `step` left for the admitting command to fill in.
    fn write(self: *RowWriter) Error![]const u8 {
        try self.collectValueVars(self.eq.lhs, false);
        const lhs = switch (self.eq.lhs) {
            .var_ => return self.fail("a left side that is a variable"),
            .app => |x| x,
        };
        var out: std.Io.Writer.Allocating = .init(self.arena);
        const w = &out.writer;
        try w.writeAll("    .{\n        .step = \"{step}\",\n        .tier = .first_order,\n");
        switch (lhs.sym.op) {
            .prim => {
                var args: std.ArrayList([]const u8) = .empty;
                for (lhs.args) |a| try args.append(self.arena, try self.pat(a));
                try w.print("        .root = .prim,\n        .root_prim = .{{ .method = .{s}, .owner = {s} }},\n        .args = {s},\n", .{ @tagName(lhs.sym.method.?), try self.owner(lhs.sym), try self.list(args.items) });
            },
            .switch_ => if (try self.wholeSwitch(lhs)) |p|
                try w.print("        .root = .switch_,\n        .args = &.{{{s}}},\n", .{p})
            else
                try w.print("        .root = .switch_,\n        .args = &.{{{s}}},\n", .{try self.pat(self.eq.lhs)}),
            .and_, .or_ => try w.print("        .root = .{s},\n        .args = &.{{{s}}},\n", .{ @tagName(lhs.sym.op), try self.pat(self.eq.lhs) }),
            .field, .index, .payload => try w.print("        .root = .{s},\n        .args = &.{{{s}}},\n", .{ @tagName(lhs.sym.op), try self.component(lhs) }),
            .wrap, .unwrap => try w.print("        .root = .{s},\n        .args = &.{{{s}}},\n", .{ @tagName(lhs.sym.op), try self.pat(lhs.args[0]) }),
            .lit, .tag, .record, .tuple => return self.fail("a left side rooted at a literal, record, tuple or tag union"),
            .crash, .derived, .list, .closure, .elem, .opt_field, .call, .for_range, .for_list, .loop, .lambda, .apply => unreachable, // signature terms are built only from the enumerated symbols (derive/enumerate.zig)
        }
        const result_owner: ?[]const u8 = if (lhs.sym.op == .prim and resultIsOwner(lhs.sym.method.?)) try self.owner(lhs.sym) else null;
        const result = try self.tmpl(self.eq.rhs, result_owner);
        var conds: std.ArrayList([]const u8) = .empty;
        for (self.eq.conds) |c| switch (c) {
            .int_owner => try conds.append(self.arena, ".{ .int_owner = 0 }"),
            .speculatable, .is_lit, .nonzero_lit => |v| {
                const e = self.lookup(v) orelse return self.fail("a condition on a variable the left side does not bind");
                if (e.kind != .pattern) return self.fail("a condition on an arm");
                try conds.append(self.arena, try self.print(".{{ .{s} = {d} }}", .{ @tagName(c), e.k }));
            },
        };
        // The signature has one nominal, so its sort proves what a row over
        // every nominal must state: a `Wrap` root's result is of its type.
        if (lhs.sym.op == .wrap and self.eq.rhs == .var_) try conds.append(self.arena, try self.print(".{{ .same_ty = {d} }}", .{self.lookup(self.eq.rhs.var_).?.k}));
        if (conds.items.len > 0) try w.print("        .conds = {s},\n", .{try self.list(conds.items)});
        try w.print("        .result = {s},\n    }},\n", .{result});
        return out.written();
    }
};

const testing = std.testing;

test "Bool.is_eq(x, True) = x is a first-order rule with a row; commutativity is out of scope" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var vars = try sig_mod.Vars.base(testing.allocator, sig_mod.find("S1").?);
    defer vars.deinit(testing.allocator);
    var p = prove.Prover.init(a, testing.allocator, testing.io);
    defer p.deinit();
    const v = try run(a, &p, vars, .{ .lhs = try term.parse(a, "Bool.is_eq(x0, True)"), .rhs = try term.parse(a, "x0"), .conds = &.{} });
    const row = v.class.f_rule.row.?;
    try testing.expect(std.mem.find(u8, row, ".root_prim = .{ .method = .is_eq, .owner = .{ .fixed = .bool_ } }") != null);
    try testing.expect(std.mem.find(u8, row, ".args = &.{ .{ .any = 0 }, .{ .lit_bool = true } }") != null);
    try testing.expect(std.mem.find(u8, row, ".result = .{ .var_ = 0 }") != null);
    const c = try run(a, &p, vars, .{ .lhs = try term.parse(a, "and_(x0, x1)"), .rhs = try term.parse(a, "and_(x1, x0)"), .conds = &.{} });
    try testing.expect(c.class == .out_of_scope);
}

test "an integer literal is a pattern, and a result of its enclosing owner's type" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var vars = try sig_mod.Vars.base(testing.allocator, sig_mod.find("S1").?);
    defer vars.deinit(testing.allocator);
    var p = prove.Prover.init(a, testing.allocator, testing.io);
    defer p.deinit();
    if (p.z3_missing != null) return error.SkipZigTest;
    const plus = try run(a, &p, vars, .{ .lhs = try term.parse(a, "o0.plus(x2, 0)"), .rhs = try term.parse(a, "x2"), .conds = &.{.int_owner} });
    try testing.expect(std.mem.find(u8, plus.class.f_rule.row.?, ".args = &.{ .{ .any = 0 }, .{ .lit_int = 0 } }") != null);
    // One condition is written as `zig fmt` writes a one-element slice.
    try testing.expect(std.mem.find(u8, plus.class.f_rule.row.?, ".conds = &.{.{ .int_owner = 0 }},") != null);
    const minus = try run(a, &p, vars, .{ .lhs = try term.parse(a, "o0.minus(x2, x2)"), .rhs = try term.parse(a, "0"), .conds = &.{ .{ .speculatable = 2 }, .int_owner } });
    try testing.expect(std.mem.find(u8, minus.class.f_rule.row.?, ".result = .{ .lit_int = .{ .value = 0, .owner = .{ .bind = 0 } } }") != null);
}

test "a switch or projection whose result is one of its parts has a row; another switch on a union has none; an equation over literals is constant folding" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var vars = try sig_mod.Vars.base(testing.allocator, sig_mod.find("S1").?);
    defer vars.deinit(testing.allocator);
    var p = prove.Prover.init(a, testing.allocator, testing.io);
    defer p.deinit();
    if (p.z3_missing != null) return error.SkipZigTest;
    const Case = struct { lhs: []const u8, rhs: []const u8, args: []const u8, result: []const u8 };
    for ([_]Case{
        .{ .lhs = "switch_(x4, x2, x2)", .rhs = "x2", .args = ".{ .same_arms = .{ .scrutinee = &.{ .any = 0 }, .region = 0 } }", .result = ".{ .region_value = 0 }" },
        .{ .lhs = "switch_(tag#1(), x2, x3)", .rhs = "x3", .args = ".{ .tag_arm = 0 }", .result = ".{ .region_value = 0 }" },
        .{ .lhs = "field#1(record(x2, x0))", .rhs = "x0", .args = ".{ .component = .{ .op = .record, .bind = 0 } }", .result = ".{ .var_ = 0 }" },
        .{ .lhs = "payload#0(tag#0(x2))", .rhs = "x2", .args = ".{ .component = .{ .op = .tag, .bind = 0 } }", .result = ".{ .var_ = 0 }" },
        .{ .lhs = "index#1(tuple(x2, x0))", .rhs = "x0", .args = ".{ .component = .{ .op = .tuple, .bind = 0 } }", .result = ".{ .var_ = 0 }" },
        .{ .lhs = "unwrap(wrap(x2))", .rhs = "x2", .args = ".{ .op = .{ .op = .wrap, .args = &.{.{ .any = 0 }} } }", .result = ".{ .var_ = 0 }" },
        .{ .lhs = "wrap(unwrap(x10))", .rhs = "x10", .args = ".{ .op = .{ .op = .unwrap, .args = &.{.{ .any = 0 }} } }", .result = ".conds = &.{.{ .same_ty = 0 }}" },
    }) |c| {
        const v = try run(a, &p, vars, .{ .lhs = try term.parse(a, c.lhs), .rhs = try term.parse(a, c.rhs), .conds = &.{} });
        const row = v.class.f_rule.row.?;
        try testing.expect(std.mem.find(u8, row, c.args) != null);
        try testing.expect(std.mem.find(u8, row, c.result) != null);
    }
    const sw = try run(a, &p, vars, .{ .lhs = try term.parse(a, "switch_(x4, True, True)"), .rhs = try term.parse(a, "True"), .conds = &.{} });
    try testing.expectEqualStrings("a switch on a tag union", sw.class.f_rule.unstated.?);
    const folded = try run(a, &p, vars, .{ .lhs = try term.parse(a, "Bool.not(o0.is_eq(0, x2))"), .rhs = try term.parse(a, "True"), .conds = &.{ .{ .nonzero_lit = 2 }, .int_owner } });
    try testing.expectEqualStrings("N13j", folded.class.context);
}
