//! The signatures of step 2 and the typed view of their terms
//! (`roc-reify-rule-derivation.md` 3.2 and 5).
//!
//! A signature fixes sorts, ops and literals. Its variables are two per sort,
//! numbered in the signature's sort order; generalization adds more. A term
//! over a signature is a `term.Term` whose integer builtins name `I64` and
//! whose variables have the sorts a `Vars` records. `Instance` builds such a
//! term through the builder, at the integer width a proof asks for.

const std = @import("std");
const reify = @import("reify");
const term = @import("term.zig");

const Allocator = std.mem.Allocator;
const Term = term.Term;
const ir = reify.ir;
const prims = reify.prims;
const Ref = ir.Ref;
const TyId = ir.TyId;
const IntTy = reify.types.IntTy;

/// The tag `A` of `union_ab`. Every store of this tool interns `A` and `B`
/// before any other name, so a `Value` the tool makes names them the same way
/// in every store, and a tag's position in `union_ab` is its name's index.
pub const tag_a = reify.types.NameId.of(0);
/// The tag `B` of `union_ab`, interned second (see `tag_a`).
pub const tag_b = reify.types.NameId.of(1);

/// A new type table that holds the tool's tag names first (`tag_a`, `tag_b`).
pub fn newTypes(gpa: Allocator) Allocator.Error!reify.types.Types {
    var types = reify.types.Types.init(gpa);
    errdefer types.deinit();
    const a = try types.name("A");
    const b = try types.name("B");
    std.debug.assert(a == tag_a and b == tag_b);
    return types;
}

/// A sort of a signature.
pub const Sort = enum {
    bool,
    i64,
    /// `[A(I64), B]`.
    union_ab,
    /// `{ x : I64, y : Bool }`.
    record_xy,
    f64,
    str,
    union_abc,
    list_i64,
    /// `(I64, Bool)`.
    tuple_ib,
    /// The nominal `N` over `I64`.
    nominal_i64,

    /// Whether this tool builds terms of the sort yet.
    pub fn built(self: Sort) bool {
        return switch (self) {
            .bool, .i64, .union_ab, .record_xy, .tuple_ib, .nominal_i64 => true,
            .f64, .str, .union_abc, .list_i64 => false,
        };
    }
};

/// An op of a signature.
pub const OpKind = enum {
    not,
    and_,
    or_,
    is_eq,
    is_lt,
    is_lte,
    is_gt,
    is_gte,
    plus,
    minus,
    times,
    div_trunc,
    plus_wrap,
    times_wrap,
    bitwise_and,
    bitwise_or,
    bitwise_xor,
    concat,
    switch_bool,
    switch_union,
    switch_lit,
    tag,
    payload,
    record,
    field,
    len,
    get,
    tuple,
    index,
    wrap,
    unwrap,

    /// Whether this tool builds terms with the op yet.
    pub fn built(self: OpKind) bool {
        return switch (self) {
            .not, .and_, .or_, .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .switch_bool, .switch_union, .switch_lit, .tag, .payload, .record, .field, .tuple, .index, .wrap, .unwrap => true,
            .concat, .len, .get => false,
        };
    }
};

/// A literal of a signature.
pub const Lit = union(enum) { bool: bool, int: i64 };

/// One signature of `signatures.zon`.
pub const Signature = struct {
    name: []const u8,
    milestone: []const u8,
    k: u32,
    sorts: []const Sort,
    ops: []const OpKind,
    lits: []const Lit,
    /// Builtins whose laws the normal form claims only within one chain of
    /// the builtin (normal-form 3.15): an argument of one is a variable, a
    /// literal or the same builtin, and only the same builtin or an op that
    /// is not a builtin reads one. Laws between two of them, or with a
    /// comparison, are not in the table's scope, so the terms stating them
    /// are not built.
    chains: []const OpKind = &.{},
    /// Literals that only a chain builtin reads: they stand for the chains'
    /// identities and absorbers (all ones), and elsewhere state laws of
    /// checked arithmetic the normal form does not claim.
    chain_lits: []const Lit = &.{},

    /// Whether integer literal `v` is one only a chain builtin reads.
    pub fn isChainLit(self: Signature, v: i64) bool {
        for (self.chain_lits) |l| switch (l) {
            .int => |w| if (w == v) return true,
            .bool => {},
        };
        return false;
    }

    /// Whether `m` is one of the signature's chain builtins.
    pub fn isChain(self: Signature, m: prims.Method) bool {
        for (self.chains) |o| if (std.mem.eql(u8, @tagName(o), @tagName(m))) return true;
        return false;
    }

    /// Whether the signature has `op`.
    pub fn has(self: Signature, op: OpKind) bool {
        return std.mem.findScalar(OpKind, self.ops, op) != null;
    }

    /// Whether every term of `other` is a term of this signature over the
    /// same variables: its sorts come first here, in its order, and its ops
    /// are among these. A ledger entry of `other` then holds here as written.
    pub fn includes(self: Signature, other: Signature) bool {
        if (!std.mem.startsWith(Sort, self.sorts, other.sorts)) return false;
        for (other.ops) |o| if (!self.has(o)) return false;
        return true;
    }

    /// The first sort or op of the signature this tool does not build, by name.
    pub fn unbuilt(self: Signature) ?[]const u8 {
        for (self.sorts) |s| if (!s.built()) return @tagName(s);
        for (self.ops) |o| if (!o.built()) return @tagName(o);
        return null;
    }
};

/// Every signature.
pub const signatures: []const Signature = @import("signatures.zon");

/// The signature named `name`.
pub fn find(name: []const u8) ?Signature {
    for (signatures) |s| if (std.mem.eql(u8, s.name, name)) return s;
    return null;
}

/// The variables of a run and their sorts.
pub const Vars = struct {
    sorts: std.ArrayList(Sort) = .empty,

    /// Two variables per sort of `sig`, in its sort order.
    pub fn base(gpa: Allocator, sig: Signature) Allocator.Error!Vars {
        var v: Vars = .{};
        for (sig.sorts) |s| try v.sorts.appendSlice(gpa, &.{ s, s });
        return v;
    }

    pub fn deinit(self: *Vars, gpa: Allocator) void {
        self.sorts.deinit(gpa);
    }

    /// A new variable of `sort`.
    pub fn fresh(self: *Vars, gpa: Allocator, sort: Sort) Allocator.Error!term.Var {
        try self.sorts.append(gpa, sort);
        return @intCast(self.sorts.items.len - 1);
    }

    /// The sort of variable `v`.
    pub fn of(self: Vars, v: term.Var) Sort {
        return self.sorts.items[v];
    }
};

/// The sort of `t`.
pub fn sortOf(vars: Vars, t: Term) Sort {
    return switch (t) {
        .var_ => |v| vars.of(v),
        .app => |x| switch (x.sym.op) {
            .lit => if (x.sym.lit != null) .bool else .i64,
            .prim => switch (x.sym.method.?) {
                .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not => .bool,
                .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor => .i64,
                .concat => .str,
                .len => .i64,
                .get => unreachable, // `get` is not an enumerated signature symbol
            },
            .and_, .or_ => .bool,
            .switch_ => sortOf(vars, x.args[1 + (term.litKeys(x) orelse 0)]),
            .tag => .union_ab,
            .payload => .i64,
            .record => .record_xy,
            .field, .index => if (x.sym.index.? == 0) .i64 else .bool,
            .tuple => .tuple_ib,
            .wrap => .nominal_i64,
            .unwrap => .i64,
            .crash, .derived, .list, .closure, .elem, .opt_field, .call, .for_range, .for_list, .loop, .lambda, .apply => unreachable, // signature terms are built only from the enumerated symbols (derive/enumerate.zig)
        },
    };
}

/// The type of `sort` with integers of `width`.
pub fn tyOf(types: *reify.types.Types, sort: Sort, width: IntTy) Allocator.Error!TyId {
    const int = try types.intTy(width);
    const bool_ty = try types.boolTy();
    return switch (sort) {
        .bool => bool_ty,
        .i64 => int,
        .union_ab => types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{int} }, .{ .name = "B", .payload = &.{} } }),
        .record_xy => types.recordTy(&.{ .{ .name = "x", .ty = int }, .{ .name = "y", .ty = bool_ty } }),
        .tuple_ib => types.tupleTy(&.{ int, bool_ty }),
        .nominal_i64 => types.nominalTy("N", int),
        .f64, .str, .union_abc, .list_i64 => unreachable, // signatures use only the sorts above
    };
}

/// One term built as a row of its own store. The row's parameters are every
/// variable of `vars`, so one assignment of values serves every term.
pub const Instance = struct {
    store: ir.Store,
    types: reify.types.Types,
    b: reify.builder.Builder,
    row: ir.RowId,
    value: Ref,

    /// Build `t` at integer `width`, with every rule but the `knocked_out`
    /// ones on, or with all of them off. `self` must not move afterwards.
    pub fn init(self: *Instance, gpa: Allocator, vars: Vars, t: Term, width: IntTy, rules: bool, knocked_out: []const bool) Allocator.Error!void {
        self.store = ir.Store.init(gpa);
        self.types = try newTypes(gpa);
        self.b = reify.builder.Builder.init(gpa, &self.store, &self.types);
        self.b.hooks.rules_off = !rules;
        @memcpy(&self.b.hooks.knocked_out, knocked_out);
        const params = try gpa.alloc(TyId, vars.sorts.items.len);
        defer gpa.free(params);
        for (vars.sorts.items, params) |s, *p| p.* = try tyOf(&self.types, s, width);
        const out_ty = try tyOf(&self.types, sortOf(vars, t), width);
        self.row = try self.b.beginRow(params, out_ty);
        self.value = try self.build(vars, t, width);
        try self.b.endRow(.{ .value = &.{self.value} });
    }

    pub fn deinit(self: *Instance) void {
        self.b.deinit();
        self.types.deinit();
        self.store.deinit();
    }

    /// How many rules fired while building, and algorithm steps taken.
    pub fn fired(self: *const Instance) u32 {
        var n: u32 = self.b.hooks.algorithm_steps;
        for (self.b.hooks.fired) |f| n += f;
        return n;
    }

    fn owner(sym: term.Sym, width: IntTy) prims.Owner {
        return switch (sym.owner.?) {
            .fixed => |o| if (o.int() != null) prims.intOwner(width) else o,
            .bind => prims.intOwner(width),
        };
    }

    fn build(self: *Instance, vars: Vars, t: Term, width: IntTy) Allocator.Error!Ref {
        const x = switch (t) {
            .var_ => |v| return Ref.rowParam(@intCast(v)),
            .app => |x| x,
        };
        const b = &self.b;
        switch (x.sym.op) {
            .switch_ => {
                const scrutinee = try self.build(vars, x.args[0], width);
                // A literal switch's keys are integer literals, as `checkSort` requires.
                const n = term.litKeys(x) orelse 0;
                var keys: [8]u32 = undefined;
                for (keys[0..n], x.args[1 .. 1 + n]) |*k, key| k.* = (try b.internLit(try self.types.intTy(width), .{ .int = @bitCast(@as(i128, key.app.sym.int.?)) })).index();
                var arms: [9]ir.RegionId = undefined;
                for (arms[0 .. x.args.len - 1 - n], x.args[1 + n ..], 0..) |*arm, a, i| {
                    arm.* = try b.openArmAt(scrutinee, keys[0..n], @intCast(i));
                    try b.close(.{ .value = &.{try self.build(vars, a, width)} });
                }
                return b.switchOn(scrutinee, arms[0 .. x.args.len - 1 - n], &.{}, &.{try tyOf(&self.types, sortOf(vars, t), width)}, keys[0..n]);
            },
            .and_, .or_ => {
                const first = try self.build(vars, x.args[0], width);
                var operands: [8]ir.RegionId = undefined;
                for (x.args[1..], operands[0 .. x.args.len - 1]) |a, *r| {
                    r.* = try b.openOperand(&.{first}, x.sym.op);
                    try b.close(.{ .value = &.{try self.build(vars, a, width)} });
                }
                const regions = operands[0 .. x.args.len - 1];
                return if (x.sym.op == .and_) b.andOf(first, regions) else b.orOf(first, regions);
            },
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .for_range, .for_list, .loop, .lambda, .apply => {},
        }
        const a = try self.b.gpa.alloc(Ref, x.args.len);
        defer self.b.gpa.free(a);
        for (x.args, a) |arg, *r| r.* = try self.build(vars, arg, width);
        return switch (x.sym.op) {
            .lit => if (x.sym.lit) |v| b.litBool(v) else b.litInt(try self.types.intTy(width), x.sym.int.?),
            .prim => b.call(owner(x.sym, width), x.sym.method.?, a),
            .tag => b.tag(try tyOf(&self.types, .union_ab, width), reify.types.NameId.of(x.sym.index.?), a),
            .payload => b.payload(a[0], reify.types.NameId.of(x.sym.index.?), 0),
            .record => b.record(try tyOf(&self.types, .record_xy, width), a),
            .field => b.field(a[0], x.sym.index.?),
            .tuple => b.tuple(try tyOf(&self.types, .tuple_ib, width), a),
            .index => b.index(a[0], x.sym.index.?),
            .wrap => b.wrap(try tyOf(&self.types, .nominal_i64, width), a[0]),
            .unwrap => b.unwrap(a[0]),
            .switch_, .and_, .or_ => unreachable, // signature terms are built only from the enumerated symbols (derive/enumerate.zig)
            .crash, .derived, .list, .closure, .elem, .opt_field, .call, .for_range, .for_list, .loop, .lambda, .apply => unreachable, // signature terms are built only from the enumerated symbols (derive/enumerate.zig)
        };
    }
};

/// The normal form of `t`: built with every rule but the `knocked_out`
/// ones on, and read back.
pub fn normalize(arena: Allocator, gpa: Allocator, vars: Vars, t: Term, knocked_out: []const bool) Allocator.Error!Term {
    var inst: Instance = undefined;
    try inst.init(gpa, vars, t, .i64, true, knocked_out);
    defer inst.deinit();
    return term.readBack(arena, &inst.store, &inst.types, inst.value);
}

/// The normal form of `t` as `normalize` builds it, or null when `t` is not
/// well sorted over `vars`.
pub fn normalizeSorted(arena: Allocator, gpa: Allocator, vars: Vars, t: Term, knocked_out: []const bool) Allocator.Error!?Term {
    if (checkSort(vars, t) == null) return null;
    return try normalize(arena, gpa, vars, t, knocked_out);
}

/// The sort of `t` when every argument has the sort its op takes, as
/// `enumerate` builds terms; null otherwise.
pub fn checkSort(vars: Vars, t: Term) ?Sort {
    const x = switch (t) {
        .var_ => |v| return vars.of(v),
        .app => |x| x,
    };
    // `Instance.build` takes up to nine `And` and `Or` operands.
    var buf: [9]Sort = undefined;
    for (x.args, 0..) |a, i| buf[i] = checkSort(vars, a) orelse return null;
    const args = buf[0..x.args.len];
    const takes: []const Sort, const result: Sort = switch (x.sym.op) {
        .lit => .{ &.{}, if (x.sym.lit != null) .bool else .i64 },
        .prim => {
            const operand: Sort = switch (x.sym.owner.?) {
                .fixed => |o| if (o == .bool_) .bool else .i64,
                .bind => .i64,
            };
            const result: Sort = switch (x.sym.method.?) {
                .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not => .bool,
                .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor => operand,
                .concat, .len, .get => return null,
            };
            for (args) |a| if (a != operand) return null;
            return result;
        },
        .and_, .or_ => blk: {
            for (args) |a| if (a != .bool) return null;
            break :blk .{ args, .bool };
        },
        .switch_ => {
            const n = term.litKeys(x) orelse {
                if (args[0] != .bool and args[0] != .union_ab) return null;
                return if (args[1] == args[2]) args[1] else null;
            };
            // A literal switch on an integer: its keys are ascending integer
            // literals, as the builder keeps them, and it has one arm more.
            if (args[0] != .i64 or x.args.len != 2 * n + 2) return null;
            for (x.args[1 .. 1 + n], 0..) |k, i| {
                if (k != .app or k.app.sym.op != .lit or k.app.sym.int == null) return null;
                if (i > 0 and x.args[i].app.sym.int.? >= k.app.sym.int.?) return null;
            }
            for (args[1 + n ..]) |a| if (a != args[1 + n]) return null;
            return args[1 + n];
        },
        .tag => .{ if (x.sym.index.? == 0) &.{.i64} else &.{}, .union_ab },
        .payload => .{ &.{.union_ab}, .i64 },
        .record => .{ &.{ .i64, .bool }, .record_xy },
        .field => .{ &.{.record_xy}, if (x.sym.index.? == 0) .i64 else .bool },
        .tuple => .{ &.{ .i64, .bool }, .tuple_ib },
        .index => .{ &.{.tuple_ib}, if (x.sym.index.? == 0) .i64 else .bool },
        .wrap => .{ &.{.i64}, .nominal_i64 },
        .unwrap => .{ &.{.nominal_i64}, .i64 },
        .crash, .derived, .list, .closure, .elem, .opt_field, .call, .for_range, .for_list, .loop, .lambda, .apply => return null,
    };
    return if (std.mem.eql(Sort, takes, args)) result else null;
}

const testing = std.testing;

test "S1 and the stages of S2 are built, and S3 names what it lacks" {
    try testing.expectEqual(@as(?[]const u8, null), find("S1").?.unbuilt());
    try testing.expectEqual(@as(?[]const u8, null), find("S2").?.unbuilt());
    try testing.expectEqualStrings("f64", find("S3").?.unbuilt().?);
}

test "S2 includes S1, so S1's ledger entries hold in an S2 run, and S1 does not include S2" {
    try testing.expect(find("S2").?.includes(find("S1").?));
    try testing.expect(find("S3").?.includes(find("S2").?));
    try testing.expect(!find("S1").?.includes(find("S2").?));
}

test "an S1 term builds, and a redex fires a rule" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var vars = try Vars.base(testing.allocator, find("S1").?);
    defer vars.deinit(testing.allocator);
    const t = try term.parse(arena.allocator(), "field#0(record(Num.I64.plus(x2, 1), x0))");
    var inst: Instance = undefined;
    const none: [reify.rules.count]bool = @splat(false);
    try inst.init(testing.allocator, vars, t, .i64, true, &none);
    defer inst.deinit();
    try testing.expectEqual(@as(u32, 1), inst.fired());
    try testing.expectEqual(Sort.i64, sortOf(vars, t));
}
