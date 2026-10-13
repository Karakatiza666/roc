//! Step 1 of the loop: critical pairs of the rule table
//! (`roc-reify-rule-derivation.md` 3.1).
//!
//! For each ordered pair of first-order rows, a row with itself included,
//! and each non-variable position of the first left side, the second left
//! side is unified there, with both rows' variables and owner variables kept
//! apart. The unified term is the peak; rewriting it once by each rule gives
//! two reducts. Both are built through the builder with every rule on, which
//! normalizes them, and the builder's hash-consing makes two equal normal
//! forms one node. Two different nodes are an unjoined pair.
//!
//! A pair is checked on an instance both rows' conditions accept: the peak is
//! built in the builder's rules-off mode, and the builder says whether each
//! row rewrites it at its position. A variable a row needs to be a literal
//! takes each literal the rows name, and one they do not; an instance either
//! row refuses is no overlap. A repeated term with regions is built once and
//! shared, as a body that binds it once has it.

const std = @import("std");
const reify = @import("reify");
const term = @import("term.zig");

const Allocator = std.mem.Allocator;
const Term = term.Term;
const table = reify.rules;
const prims = reify.prims;
const ir = reify.ir;
const Ref = ir.Ref;
const TyId = ir.TyId;

/// One critical pair.
pub const Pair = struct {
    /// The row rewriting at the peak's root.
    outer: usize,
    /// The row rewriting at `path`.
    inner: usize,
    /// Which fixed-arity instance of each row (`term.instances`).
    outer_instance: usize = 0,
    inner_instance: usize = 0,
    path: []const u8,
    peak: Term,
    /// The peak rewritten by `outer`.
    left: Term,
    /// The peak rewritten by `inner` at `path`.
    right: Term,
    status: Status,
    /// The normal forms of `left` and `right`.
    normal: [2]Term,
};

/// What normalizing the two reducts gave.
pub const Status = enum { joined, unjoined };

/// Every critical pair of the first-order rows, with `knocked_out` rows disabled
/// both as sources of pairs and in the normalizer.
pub fn all(arena: Allocator, gpa: Allocator, knocked_out: []const bool) Allocator.Error![]Pair {
    var out: std.ArrayList(Pair) = .empty;
    const lits = try namedLits(arena);
    for (table.rules, 0..) |outer, oi| {
        if (outer.tier != .first_order or knocked_out[oi]) continue;
        for (try term.instances(arena, outer), 0..) |lo, ok| {
            var paths: std.ArrayList([]const u8) = .empty;
            try positions(arena, lo.lhs, &.{}, &paths);
            for (table.rules, 0..) |inner, ii| {
                if (inner.tier != .first_order or knocked_out[ii]) continue;
                for (try term.instances(arena, inner), 0..) |li, ik| {
                    const offset = @max(lo.lhs.varBound(), 1);
                    const owner_offset = table.ownerVarCount(outer);
                    const inner_lhs = try term.shift(arena, li.lhs, offset, owner_offset);
                    const inner_rhs = try term.shift(arena, li.rhs, offset, owner_offset);
                    for (paths.items) |path| {
                        if (oi == ii and ok == ik and path.len == 0) continue;
                        const bound = offset + @max(li.lhs.varBound(), 1);
                        const s = (try term.unify(arena, term.at(lo.lhs, path), inner_lhs, bound)) orelse continue;
                        const cond = try checkConds(arena, s, outer, lo, 0, 0) and try checkConds(arena, s, inner, li, offset, owner_offset);
                        if (!cond) continue;
                        var lit_vars: std.ArrayList(term.Var) = .empty;
                        try literalVars(arena, s, outer, 0, &lit_vars);
                        try literalVars(arena, s, inner, offset, &lit_vars);
                        try keyVars(arena, try s.apply(arena, lo.lhs), &lit_vars);
                        // One instance per assignment of named literals to the variables.
                        const choice = try arena.alloc(usize, lit_vars.items.len);
                        @memset(choice, 0);
                        while (true) {
                            const si = try withLits(arena, s, lit_vars.items, choice, lits);
                            const peak = try si.apply(arena, lo.lhs);
                            const left = try si.apply(arena, lo.rhs);
                            const right = try si.apply(arena, try term.replaceAt(arena, lo.lhs, path, inner_rhs));
                            const probe: Probe = .{ .outer = oi, .inner = ii, .path = path };
                            if (try joins(arena, gpa, si, peak, left, right, knocked_out, probe)) |j| {
                                try out.append(arena, .{ .outer = oi, .inner = ii, .outer_instance = ok, .inner_instance = ik, .path = path, .peak = peak, .left = left, .right = right, .status = if (j.same) .joined else .unjoined, .normal = j.normal });
                            }
                            if (!nextChoice(choice, lits.len)) break;
                        }
                    }
                }
            }
        }
    }
    return out.toOwnedSlice(arena);
}

fn positions(arena: Allocator, t: Term, prefix: []const u8, out: *std.ArrayList([]const u8)) Allocator.Error!void {
    switch (t) {
        .var_ => {},
        .app => |x| {
            try out.append(arena, prefix);
            for (x.args, 0..) |a, i| {
                const p = try arena.alloc(u8, prefix.len + 1);
                @memcpy(p[0..prefix.len], prefix);
                p[prefix.len] = @intCast(i);
                try positions(arena, a, p, out);
            }
        },
    }
}

// An unbound owner stands for any owner the conditions allow; `I64` is the
// one the pair is built at, and a fixed owner must satisfy the condition itself.
fn resolvedOwner(s: term.Subst, k: u8) prims.Owner {
    return switch (s.owner(.{ .bind = k })) {
        .fixed => |o| o,
        .bind => .i64,
    };
}

// A polarity condition reads the peak's formula, whose leaves unification
// can have turned into `Bool.not` nodes or connectives.
fn checkConds(arena: Allocator, s: term.Subst, rule: table.Rule, rt: term.RuleTerms, var_offset: term.Var, owner_offset: u8) Allocator.Error!bool {
    for (rule.conds) |c| switch (c) {
        .int_owner => |k| if (resolvedOwner(s, k + owner_offset).int() == null) return false,
        .not_float_owner => |k| if (resolvedOwner(s, k + owner_offset).float() != null) return false,
        .polarity_flips => |k| if (rt.shapes[k]) |f| {
            if (!term.polarityFlips(try s.apply(arena, try term.shift(arena, f, var_offset, owner_offset)))) return false;
        },
        .is_lit, .speculatable, .nonzero_lit, .movable, .movable_rest, .speculatable_rest, .same_ty, .lit_bool_switch, .not_lit => {},
        // Only an evaluation row folds, and `all` pairs first-order rows.
        .folds => unreachable,
    };
    return true;
}

// The variables, after `s`, that a condition of `rule` needs to be literals
// and that unification left variables.
fn literalVars(arena: Allocator, s: term.Subst, rule: table.Rule, var_offset: term.Var, out: *std.ArrayList(term.Var)) Allocator.Error!void {
    for (rule.conds) |c| switch (c) {
        .is_lit, .nonzero_lit => |k| switch (try s.apply(arena, .{ .var_ = k + var_offset })) {
            .var_ => |v| if (std.mem.findScalar(term.Var, out.items, v) == null) try out.append(arena, v),
            .app => {},
        },
        .int_owner, .not_float_owner, .speculatable, .speculatable_rest, .same_ty, .movable, .movable_rest, .polarity_flips, .lit_bool_switch, .not_lit => {},
        .folds => unreachable,
    };
}

// Adds the variables that stand for a key of a literal switch in `t`: a key
// is a literal by the switch's form.
fn keyVars(arena: Allocator, t: Term, out: *std.ArrayList(term.Var)) Allocator.Error!void {
    switch (t) {
        .var_ => {},
        .app => |x| {
            if (term.litKeys(x)) |n| for (x.args[1 .. 1 + n]) |k| switch (k) {
                .var_ => |v| if (std.mem.findScalar(term.Var, out.items, v) == null) try out.append(arena, v),
                .app => {},
            };
            for (x.args) |a| try keyVars(arena, a, out);
        },
    }
}

// The literals a literal variable takes: `False`, `True`, every integer
// literal of a row's instances, and one integer above them all, which stands
// for every literal the rows do not name.
fn namedLits(arena: Allocator) Allocator.Error![]const Term {
    var ints: std.ArrayList(i64) = .empty;
    for (table.rules) |r| {
        if (r.tier != .first_order) continue;
        for (try term.instances(arena, r)) |inst| {
            try collectInts(arena, inst.lhs, &ints);
            try collectInts(arena, inst.rhs, &ints);
        }
    }
    std.mem.sort(i64, ints.items, {}, std.sort.asc(i64));
    var out: std.ArrayList(Term) = .empty;
    for ([_]bool{ false, true }) |v| try out.append(arena, .{ .app = .{ .sym = .{ .op = .lit, .lit = v }, .args = &.{} } });
    for (ints.items) |n| try out.append(arena, .{ .app = .{ .sym = .{ .op = .lit, .int = n }, .args = &.{} } });
    const above = if (ints.items.len == 0) 0 else ints.items[ints.items.len - 1] + 1;
    try out.append(arena, .{ .app = .{ .sym = .{ .op = .lit, .int = above }, .args = &.{} } });
    return out.toOwnedSlice(arena);
}

fn collectInts(arena: Allocator, t: Term, out: *std.ArrayList(i64)) Allocator.Error!void {
    switch (t) {
        .var_ => {},
        .app => |x| {
            if (x.sym.op == .lit) if (x.sym.int) |n| {
                if (std.mem.findScalar(i64, out.items, n) == null) try out.append(arena, n);
            };
            for (x.args) |a| try collectInts(arena, a, out);
        },
    }
}

// `s` with `vars[i]` bound to `lits[choice[i]]`.
fn withLits(arena: Allocator, s: term.Subst, vars: []const term.Var, choice: []const usize, lits: []const Term) Allocator.Error!term.Subst {
    if (vars.len == 0) return s;
    var bound: term.Var = @intCast(s.map.len);
    for (vars) |v| bound = @max(bound, v + 1);
    var out = s;
    out.map = try arena.alloc(?Term, bound);
    @memset(out.map, null);
    @memcpy(out.map[0..s.map.len], s.map);
    for (vars, choice) |v, c| out.map[v] = lits[c];
    return out;
}

// The next assignment in counting order, or false after the last.
fn nextChoice(choice: []usize, n: usize) bool {
    for (choice) |*c| {
        c.* += 1;
        if (c.* < n) return true;
        c.* = 0;
    }
    return false;
}

const Join = struct { same: bool, normal: [2]Term };

fn termSize(t: Term) usize {
    return switch (t) {
        .var_ => 1,
        .app => |x| blk: {
            var n: usize = 1;
            for (x.args) |a| n += termSize(a);
            break :blk n;
        },
    };
}

/// The two rows of a pair and where the inner one rewrites the peak.
const Probe = struct { outer: usize, inner: usize, path: []const u8 };

// Null when the instance is ill typed or a row does not rewrite its peak.
fn joins(arena: Allocator, gpa: Allocator, s: term.Subst, peak: Term, left: Term, right: Term, knocked_out: []const bool, probe: Probe) Allocator.Error!?Join {
    var store = ir.Store.init(gpa);
    defer store.deinit();
    var types = reify.types.Types.init(gpa);
    defer types.deinit();
    var b = reify.builder.Builder.init(gpa, &store, &types);
    defer b.deinit();
    for (knocked_out, 0..) |k, i| b.hooks.knocked_out[i] = k;

    var m: Materializer = .{ .gpa = gpa, .types = &types, .b = &b, .s = s };
    defer m.var_tys.deinit(gpa);
    defer m.path.deinit(gpa);
    defer m.shared.deinit(gpa);
    const peak_ty = try m.infer(peak, null);
    if (m.ill_typed) return null;
    const params = try gpa.alloc(TyId, m.var_tys.items.len);
    defer gpa.free(params);
    for (m.var_tys.items, params) |t, *p| p.* = t orelse try types.intTy(.i64);
    const bool_ty = try types.boolTy();
    _ = try b.beginRow(params, bool_ty);
    b.hooks.rules_off = true;
    m.target = probe.path;
    const p = try m.buildShared(peak, peak_ty);
    m.target = null;
    b.hooks.rules_off = false;
    if (!try b.rewrites(probe.outer, p) or !try b.rewrites(probe.inner, m.found.?)) {
        try b.endRow(.{ .value = &.{p} });
        return null;
    }
    const l = try m.buildShared(left, peak_ty);
    const r = try m.buildShared(right, peak_ty);
    try b.endRow(.{ .value = &.{l} });
    var cmp: reify.equal.Comparison = .{ .gpa = gpa, .store = &store };
    defer cmp.deinit();
    return .{ .same = try cmp.values(l, r), .normal = .{ try term.readBack(arena, &store, &types, l), try term.readBack(arena, &store, &types, r) } };
}

/// The normal form of a term over the table's patterns, as step 1 builds it.
pub fn normalize(arena: Allocator, gpa: Allocator, t: Term, knocked_out: []const bool) Allocator.Error!Term {
    return (try normalizeTyped(arena, gpa, t, knocked_out)) orelse unreachable;
}

/// The normal form of `t` as `normalize` builds it, or null when `t` has no
/// type: a variable or a node its context gives two types.
pub fn normalizeTyped(arena: Allocator, gpa: Allocator, t: Term, knocked_out: []const bool) Allocator.Error!?Term {
    var store = ir.Store.init(gpa);
    defer store.deinit();
    var types = reify.types.Types.init(gpa);
    defer types.deinit();
    var b = reify.builder.Builder.init(gpa, &store, &types);
    defer b.deinit();
    @memcpy(&b.hooks.knocked_out, knocked_out);
    const map = try arena.alloc(?Term, 0);
    var m: Materializer = .{ .gpa = gpa, .types = &types, .b = &b, .s = .{ .map = map } };
    defer m.var_tys.deinit(gpa);
    defer m.path.deinit(gpa);
    defer m.shared.deinit(gpa);
    const t_ty = try m.infer(t, null);
    if (m.ill_typed) return null;
    const params = try gpa.alloc(TyId, m.var_tys.items.len);
    defer gpa.free(params);
    for (m.var_tys.items, params) |ty, *p| p.* = ty orelse try types.intTy(.i64);
    _ = try b.beginRow(params, try types.boolTy());
    const v = try m.buildShared(t, t_ty);
    try b.endRow(.{ .value = &.{v} });
    return try term.readBack(arena, &store, &types, v);
}

/// The kind of type a variable takes where terms are built together.
pub const VarKind = enum { bool_, int, other };

/// The kind of each variable of `terms`, built as one pair of equal type the
/// way `joins` builds its two reducts; null for a variable they do not read,
/// and null in all when they are ill typed.
pub fn varKinds(arena: Allocator, gpa: Allocator, terms: [2]Term) Allocator.Error!?[]const ?VarKind {
    var store = ir.Store.init(gpa);
    defer store.deinit();
    var types = reify.types.Types.init(gpa);
    defer types.deinit();
    var b = reify.builder.Builder.init(gpa, &store, &types);
    defer b.deinit();
    var m: Materializer = .{ .gpa = gpa, .types = &types, .b = &b, .s = .{ .map = &.{} } };
    defer m.var_tys.deinit(gpa);
    defer m.path.deinit(gpa);
    _ = try m.infer(terms[1], try m.infer(terms[0], null));
    if (m.ill_typed) return null;
    const out = try arena.alloc(?VarKind, m.var_tys.items.len);
    for (m.var_tys.items, out) |t, *k| k.* = if (t) |ty| switch (types.get(ty)) {
        .bool_ => .bool_,
        .int => |i| if (i == .i64) .int else .other,
        .float, .dec, .str, .record, .tuple, .tag_union, .list, .nominal, .opaque_, .recursive, .func => .other,
    } else null;
    return out;
}

/// Builds a term as nodes: variables become row parameters, and each
/// construction a component pattern stands for gets a one-component type.
const Materializer = struct {
    gpa: Allocator,
    types: *reify.types.Types,
    b: *reify.builder.Builder,
    s: term.Subst,
    var_tys: std.ArrayList(?TyId) = .empty,
    /// Whether `infer` met a term its context gives another type.
    ill_typed: bool = false,
    /// The position whose node `build` records in `found`, if any.
    target: ?[]const u8 = null,
    found: ?Ref = null,
    /// The position `build` is at.
    path: std.ArrayList(u8) = .empty,
    /// The terms with regions that occur more than once in the term being
    /// built, each built once in the row body and read wherever it occurs, as
    /// in a body that binds the value once. Two builds would be two nodes,
    /// one per region, which no pattern variable matches twice.
    shared: std.ArrayList(struct { t: Term, r: Ref }) = .empty,

    fn owner(self: *Materializer, o: table.OwnerPat) prims.Owner {
        return switch (self.s.owner(o)) {
            .fixed => |f| f,
            .bind => .i64,
        };
    }

    fn ownerTy(self: *Materializer, o: prims.Owner) Allocator.Error!TyId {
        if (o.int()) |i| return self.types.intTy(i);
        if (o.float()) |f| return self.types.floatTy(f);
        return switch (o) {
            .bool_ => self.types.boolTy(),
            .str => self.types.strTy(),
            .list => self.types.listTy(try self.types.intTy(.i64)),
            .u8, .i8, .u16, .i16, .u32, .i32, .u64, .i64, .u128, .i128, .f32, .f64 => unreachable,
        };
    }

    // The type of `t` where `expected` is the type its context wants, if
    // known. A variable keeps the type its first occurrence gives it.
    fn infer(self: *Materializer, t: Term, expected: ?TyId) Allocator.Error!TyId {
        const ty = try self.inferNode(t, expected);
        if (expected) |e| if (ty != e) {
            self.ill_typed = true;
        };
        return ty;
    }

    fn inferNode(self: *Materializer, t: Term, expected: ?TyId) Allocator.Error!TyId {
        const i64_ty = try self.types.intTy(.i64);
        switch (t) {
            .var_ => |v| {
                while (self.var_tys.items.len <= v) try self.var_tys.append(self.gpa, null);
                if (self.var_tys.items[v]) |ty| return ty;
                const ty = expected orelse i64_ty;
                self.var_tys.items[v] = ty;
                return ty;
            },
            .app => |x| {
                const want = expected orelse i64_ty;
                switch (x.sym.op) {
                    .lit => {
                        if (x.sym.int == null) return self.types.boolTy();
                        switch (self.types.get(want)) {
                            .int, .float => {},
                            .bool_, .dec, .str, .record, .tuple, .tag_union, .list, .nominal, .opaque_, .recursive, .func => self.ill_typed = true,
                        }
                        return want;
                    },
                    .switch_ => {
                        // A literal switch's keys are literals of its scrutinee's type.
                        const n = term.litKeys(x) orelse 0;
                        const sty = try self.infer(x.args[0], if (n > 0) null else try self.scrutineeTy(x));
                        for (x.args[1 .. 1 + n]) |key| {
                            if (key != .app or key.app.sym.int == null) self.ill_typed = true;
                            _ = try self.infer(key, sty);
                        }
                        const arms = x.args[1 + n ..];
                        // An arm that is a variable not yet typed takes its type from the others.
                        const out = expected orelse for (arms) |arm| {
                            if (arm == .var_ and (arm.var_ >= self.var_tys.items.len or self.var_tys.items[arm.var_] == null)) continue;
                            break try self.infer(arm, null);
                        } else try self.infer(arms[0], null);
                        for (arms) |arm| _ = try self.infer(arm, out);
                        return out;
                    },
                    .and_, .or_ => {
                        const bool_ty = try self.types.boolTy();
                        for (x.args) |a| _ = try self.infer(a, bool_ty);
                        return bool_ty;
                    },
                    .prim => {
                        const o = self.owner(x.sym.owner.?);
                        const operand = try self.ownerTy(o);
                        for (x.args) |a| _ = try self.infer(a, operand);
                        return switch (x.sym.method.?) {
                            .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not => self.types.boolTy(),
                            .len => self.types.intTy(.u64),
                            .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .get => operand,
                        };
                    },
                    .field, .index, .payload => {
                        _ = try self.infer(x.args[0], try self.aggregateOf(x.sym.op, want));
                        return want;
                    },
                    .record, .tuple, .tag => {
                        const projection: ir.Op = switch (x.sym.op) {
                            .record => .field,
                            .tuple => .index,
                            .tag => .payload,
                            .lit, .crash, .derived, .list, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => unreachable,
                        };
                        const e = expected orelse return self.aggregateOf(projection, try self.infer(x.args[0], null));
                        const component = self.componentOf(e, x.sym.op) orelse {
                            self.ill_typed = true;
                            return e;
                        };
                        _ = try self.infer(x.args[0], component);
                        return e;
                    },
                    .unwrap => {
                        _ = try self.infer(x.args[0], try self.types.nominalTy("N", want));
                        return want;
                    },
                    .wrap => {
                        const e = expected orelse return self.types.nominalTy("N", try self.infer(x.args[0], null));
                        const backing = switch (self.types.get(e)) {
                            .nominal => |n| n.backing,
                            .bool_, .str, .int, .float, .record, .tuple, .tag_union, .list, .dec, .opaque_, .recursive, .func => {
                                self.ill_typed = true;
                                return e;
                            },
                        };
                        _ = try self.infer(x.args[0], backing);
                        return e;
                    },
                    .crash, .derived, .list, .closure, .elem, .opt_field, .call, .for_range, .for_list, .loop, .lambda, .apply => unreachable,
                }
            },
        }
    }

    // A switch on a `Tag` construction is on its union, and any other on a `Bool`.
    fn scrutineeTy(self: *Materializer, x: @FieldType(Term, "app")) Allocator.Error!?TyId {
        if (x.args[0] == .app and x.args[0].app.sym.op == .tag) return null;
        return try self.types.boolTy();
    }

    // The one-component aggregate whose component is `component`.
    fn aggregateOf(self: *Materializer, op: ir.Op, component: TyId) Allocator.Error!TyId {
        return switch (op) {
            .field => self.types.recordTy(&.{.{ .name = "f", .ty = component }}),
            .index => self.types.tupleTy(&.{component}),
            .payload => self.types.tagUnionTy(&.{.{ .name = "T", .payload = &.{component} }}),
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => unreachable,
        };
    }

    // The component of `aggregate`, or null when `op` does not build it.
    fn componentOf(self: *Materializer, aggregate: TyId, op: ir.Op) ?TyId {
        return switch (self.types.get(aggregate)) {
            .record => |span| if (op == .record) self.types.tySlice(self.types.memberSlice(span)[0].tys)[0] else null,
            .tuple => |span| if (op == .tuple) self.types.tySlice(span)[0] else null,
            .tag_union => |span| if (op == .tag) self.types.tySlice(self.types.memberSlice(span)[0].tys)[0] else null,
            .bool_, .str, .int, .float, .list, .nominal, .dec, .opaque_, .recursive, .func => null,
        };
    }

    // `t` built with its repeated terms with regions shared, smaller first.
    fn buildShared(self: *Materializer, t: Term, want: ?TyId) Allocator.Error!Ref {
        self.shared.clearRetainingCapacity();
        var seen: std.ArrayList(Term) = .empty;
        defer seen.deinit(self.gpa);
        var repeated: std.ArrayList(Term) = .empty;
        defer repeated.deinit(self.gpa);
        try self.repeatedRegionTerms(t, &seen, &repeated);
        std.mem.sort(Term, repeated.items, {}, struct {
            fn lt(_: void, a: Term, b: Term) bool {
                return termSize(a) < termSize(b);
            }
        }.lt);
        const target = self.target;
        self.target = null;
        for (repeated.items) |x| {
            const ill = self.ill_typed;
            const ty = try self.infer(x, null);
            self.ill_typed = ill;
            const r = try self.build(x, ty);
            try self.shared.append(self.gpa, .{ .t = x, .r = r });
        }
        self.target = target;
        defer self.shared.clearRetainingCapacity();
        return self.build(t, want);
    }

    fn repeatedRegionTerms(self: *Materializer, t: Term, seen: *std.ArrayList(Term), out: *std.ArrayList(Term)) Allocator.Error!void {
        const x = switch (t) {
            .var_ => return,
            .app => |x| x,
        };
        switch (x.sym.op) {
            .and_, .or_, .switch_ => {
                for (seen.items) |u| if (u.eql(t)) {
                    for (out.items) |o| if (o.eql(t)) return;
                    return out.append(self.gpa, t);
                };
                try seen.append(self.gpa, t);
            },
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .for_range, .for_list, .loop, .lambda, .apply => {},
        }
        for (x.args) |a| try self.repeatedRegionTerms(a, seen, out);
    }

    // `want` is the type the context gives `t`, as in `infer`.
    fn build(self: *Materializer, t: Term, want: ?TyId) Allocator.Error!Ref {
        const r = try self.buildAt(t, want);
        if (self.target) |target| if (std.mem.eql(u8, self.path.items, target)) {
            self.found = r;
        };
        return r;
    }

    // Argument `i` of the term `build` is at.
    fn buildArg(self: *Materializer, i: usize, t: Term, want: ?TyId) Allocator.Error!Ref {
        try self.path.append(self.gpa, @intCast(i));
        defer _ = self.path.pop();
        return self.build(t, want);
    }

    fn buildAt(self: *Materializer, t: Term, want: ?TyId) Allocator.Error!Ref {
        for (self.shared.items) |e| if (e.t.eql(t)) return e.r;
        switch (t) {
            .var_ => |v| return Ref.rowParam(@intCast(v)),
            .app => |x| {
                // Arms and operands are regions, so they are built inside them.
                switch (x.sym.op) {
                    .switch_ => {
                        const n = term.litKeys(x) orelse 0;
                        const scrutinee = try self.buildArg(0, x.args[0], if (n > 0) null else try self.scrutineeTy(x));
                        const keys = try self.gpa.alloc(u32, n);
                        defer self.gpa.free(keys);
                        for (keys, x.args[1 .. 1 + n]) |*k, key| k.* = (try self.b.internLit(self.refTy(scrutinee), .{ .int = @bitCast(@as(i128, key.app.sym.int.?)) })).index();
                        const arms = try self.gpa.alloc(ir.RegionId, x.args.len - 1 - n);
                        defer self.gpa.free(arms);
                        var ty: TyId = undefined;
                        for (arms, x.args[1 + n ..], 0..) |*arm, a, i| {
                            arm.* = try self.b.openArmAt(scrutinee, keys, @intCast(i));
                            const v = try self.buildArg(1 + n + i, a, want);
                            ty = self.refTy(v);
                            try self.b.close(.{ .value = &.{v} });
                        }
                        return self.b.switchOn(scrutinee, arms, &.{}, &.{ty}, keys);
                    },
                    .and_, .or_ => {
                        const bool_ty = try self.types.boolTy();
                        const first = try self.buildArg(0, x.args[0], bool_ty);
                        const operands = try self.gpa.alloc(ir.RegionId, x.args.len - 1);
                        defer self.gpa.free(operands);
                        for (x.args[1..], operands, 1..) |a, *r, i| {
                            r.* = try self.b.openOperand(&.{first}, x.sym.op);
                            const v = try self.buildArg(i, a, bool_ty);
                            try self.b.close(.{ .value = &.{v} });
                        }
                        return if (x.sym.op == .and_) self.b.andOf(first, operands) else self.b.orOf(first, operands);
                    },
                    .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .for_range, .for_list, .loop, .lambda, .apply => {},
                }
                const operand_ty: ?TyId = if (x.sym.op == .prim) try self.ownerTy(self.owner(x.sym.owner.?)) else null;
                const a = try self.gpa.alloc(Ref, x.args.len);
                defer self.gpa.free(a);
                for (x.args, a, 0..) |arg, *r, i| r.* = try self.buildArg(i, arg, operand_ty);
                const b = self.b;
                return switch (x.sym.op) {
                    .lit => if (x.sym.int) |n| b.litInt(want orelse try self.types.intTy(.i64), n) else b.litBool(x.sym.lit.?),
                    .prim => b.call(self.owner(x.sym.owner.?), x.sym.method.?, a),
                    .field => b.field(a[0], 0),
                    .index => b.index(a[0], 0),
                    .payload => b.payload(a[0], try self.types.name("T"), 0),
                    .record => b.record(try self.types.recordTy(&.{.{ .name = "f", .ty = self.refTy(a[0]) }}), a),
                    .tuple => b.tuple(try self.types.tupleTy(&.{self.refTy(a[0])}), a),
                    .tag => b.tag(try self.types.tagUnionTy(&.{.{ .name = "T", .payload = &.{self.refTy(a[0])} }}), try self.types.name("T"), a),
                    .wrap => b.wrap(try self.types.nominalTy("N", self.refTy(a[0])), a[0]),
                    .unwrap => b.unwrap(a[0]),
                    .switch_, .and_, .or_ => unreachable,
                    .crash, .derived, .list, .closure, .elem, .opt_field, .call, .for_range, .for_list, .loop, .lambda, .apply => unreachable,
                };
            },
        }
    }

    fn refTy(self: *Materializer, r: Ref) TyId {
        return self.b.store.refTy(self.b.row, r);
    }
};

/// Write the pairs as a report section. Returns the number of unjoined pairs.
pub fn write(w: *std.Io.Writer, pairs: []const Pair) std.Io.Writer.Error!usize {
    var unjoined: usize = 0;
    try w.writeAll("## Step 1: critical pairs\n\n| Outer | Inner | Position | Peak | Left | Right | Status |\n|---|---|---|---|---|---|---|\n");
    for (pairs) |p| {
        if (p.status == .unjoined) unjoined += 1;
        try w.print("| {d} {s} | {d} {s} | ", .{ p.outer, table.rules[p.outer].step, p.inner, table.rules[p.inner].step });
        if (p.path.len == 0) try w.writeAll("root");
        for (p.path, 0..) |i, k| {
            if (k > 0) try w.writeAll(".");
            try w.print("{d}", .{i});
        }
        try w.writeAll(" | `");
        try term.write(w, p.peak);
        try w.writeAll("` | `");
        try term.write(w, p.left);
        try w.writeAll("` | `");
        try term.write(w, p.right);
        try w.print("` | {s} |\n", .{@tagName(p.status)});
        if (p.status == .unjoined) {
            const n = p.normal;
            try w.writeAll("| | | normal forms | | `");
            try term.write(w, n[0]);
            try w.writeAll("` | `");
            try term.write(w, n[1]);
            try w.writeAll("` | |\n");
        }
    }
    try w.print("\n{d} pairs, {d} unjoined.\n\n", .{ pairs.len, unjoined });
    return unjoined;
}

const testing = std.testing;

fn rowIndex(step: []const u8, method: prims.Method) usize {
    for (table.rules, 0..) |r, i| {
        if (!std.mem.eql(u8, r.step, step)) continue;
        if (r.args.len == 1 and r.args[0] == .prim and r.args[0].prim.method == method) return i;
    }
    unreachable;
}

test "knocking out the is_lte half of N13q leaves the pair with N13h unjoined" {
    // not(not(is_lt(a, b))): N13h gives is_lt(a, b); N13q inside gives
    // not(is_lte(b, a)), which only the knocked-out row brings back.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var knocked: [table.count]bool = @splat(false);
    knocked[rowIndex("N13q", .is_lte)] = true;
    const pairs = try all(arena.allocator(), testing.allocator, &knocked);
    const n13h = rowIndex("N13h", .not);
    const n13q = rowIndex("N13q", .is_lt);
    var found = false;
    for (pairs) |p| {
        if (p.outer == n13h and p.inner == n13q) {
            try testing.expectEqual(Status.unjoined, p.status);
            found = true;
        }
    }
    try testing.expect(found);
}

// A mirror of N13o or N7d is the row whose `And` or `Or` negates its first
// operand; for N7d, the `And` or `Or` a merge of two switches switches on.
fn isMirror(r: table.Rule) bool {
    if (std.mem.eql(u8, r.step, "N13o")) return negatesFirst(r.result);
    if (std.mem.eql(u8, r.step, "N7d") and r.result == .bool_switch) return negatesFirst(r.result.bool_switch.scrutinee.*);
    return false;
}

fn negatesFirst(t: table.Tmpl) bool {
    return switch (t) {
        .and_, .or_ => |ops| ops[0] == .value and ops[0].value.* == .prim,
        .var_, .prim, .bool_switch, .region_value, .lit_bool, .lit_int, .negation, .folded, .rest, .lit_switch => false,
    };
}

// N13s flips every scrutinee the switch half of N13q flips, so it goes too.
fn isSwitchHalf(r: table.Rule) bool {
    return (std.mem.eql(u8, r.step, "N13q") and r.root == .switch_) or std.mem.eql(u8, r.step, "N13s");
}

fn stepOf(i: usize) []const u8 {
    return table.rules[i].step;
}

// Whether the pair of rows `u`, `v`, in either order, has a pair that the
// knockouts leave unjoined and the full table joins.
fn knockoutUnjoins(full: []const Pair, knocked: []const Pair, u: []const u8, v: []const u8) bool {
    for (knocked) |k| {
        if (k.status != .unjoined) continue;
        const a = stepOf(k.outer);
        const b = stepOf(k.inner);
        const is = (std.mem.eql(u8, a, u) and std.mem.eql(u8, b, v)) or (std.mem.eql(u8, a, v) and std.mem.eql(u8, b, u));
        if (!is) continue;
        for (full) |f| {
            if (f.outer == k.outer and f.inner == k.inner and f.outer_instance == k.outer_instance and f.inner_instance == k.inner_instance and std.mem.eql(u8, f.path, k.path) and f.status == .joined) return true;
        }
    }
    return false;
}

test "criterion 2: knocking out the mirrors, or the switch half of N13q with N13s, brings back the four hand-found pairs" {
    // `roc-reify-rule-derivation.md` 6.1 criterion 2. The mirrors join N7d
    // and N13o with N13i and N7d with N13q; the switch half of N13q joins
    // N13q with N13i. N1l takes part in that pair only below a variable of
    // N13i's pattern, so it is an instance of it, not a pair of its own.
    // N13s knocks out with the switch half, which it generalizes.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const none: [table.count]bool = @splat(false);
    const full = try all(arena.allocator(), testing.allocator, &none);
    var mirrors: [table.count]bool = @splat(false);
    var switch_half: [table.count]bool = @splat(false);
    for (table.rules, 0..) |r, i| {
        mirrors[i] = isMirror(r);
        switch_half[i] = isSwitchHalf(r);
    }
    const without_mirrors = try all(arena.allocator(), testing.allocator, &mirrors);
    const without_switch_half = try all(arena.allocator(), testing.allocator, &switch_half);
    try testing.expect(knockoutUnjoins(full, without_mirrors, "N7d", "N13i"));
    try testing.expect(knockoutUnjoins(full, without_mirrors, "N7d", "N13q"));
    try testing.expect(knockoutUnjoins(full, without_mirrors, "N13o", "N13i"));
    try testing.expect(knockoutUnjoins(full, without_switch_half, "N13q", "N13i"));
}

test "a switch on a tag and a switch with equal arms build and normalize to their arm" {
    // N13c's instance is a one-arm switch on a one-member union's tag, which
    // no `Bool` switch reading can build.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const none: [table.count]bool = @splat(false);
    for (table.rules) |r| {
        if (r.root != .switch_ or (r.args[0] != .tag_arm and r.args[0] != .same_arms)) continue;
        for (try term.instances(a, r)) |inst| {
            try testing.expect((try normalize(a, testing.allocator, inst.lhs, &none)).eql(try normalize(a, testing.allocator, inst.rhs, &none)));
            var knocked = none;
            for (table.rules, 0..) |o, i| knocked[i] = o.root == .switch_ and (o.args[0] == .tag_arm or o.args[0] == .same_arms);
            try testing.expect(!(try normalize(a, testing.allocator, inst.lhs, &knocked)).eql(try normalize(a, testing.allocator, inst.rhs, &knocked)));
        }
    }
}

test "every first-order row rewrites the rules-off build of each instance, at some named literal" {
    // The probe `joins` asks of a pair's peak, asked of each row's own left
    // side: a row the builder refuses on its own instance makes no pair.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const none: [table.count]bool = @splat(false);
    const lits = try namedLits(a);
    for (table.rules, 0..) |r, i| {
        if (r.tier != .first_order) continue;
        for (try term.instances(a, r)) |inst| {
            const map = try a.alloc(?Term, 0);
            const s0: term.Subst = .{ .map = map };
            var lv: std.ArrayList(term.Var) = .empty;
            try literalVars(a, s0, r, 0, &lv);
            try keyVars(a, inst.lhs, &lv);
            const choice = try a.alloc(usize, lv.items.len);
            @memset(choice, 0);
            var any = false;
            while (true) {
                const si = try withLits(a, s0, lv.items, choice, lits);
                const peak = try si.apply(a, inst.lhs);
                if (try joins(a, testing.allocator, si, peak, peak, peak, &none, .{ .outer = i, .inner = i, .path = &.{} })) |_| any = true;
                if (!nextChoice(choice, lits.len)) break;
            }
            try testing.expect(any);
        }
    }
}
