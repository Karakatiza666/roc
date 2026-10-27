//! The builtin table (I3).
//!
//! Each `PrimId` is one builtin of one owner: its method, arity, whether it is
//! speculatable, and, for N15, whether it is associative, its identity and its absorber.
//! A builtin not on the speculatable list is not speculatable, which is exact
//! under C2 (plan 1.9). The table covers the builtins the rules and the
//! derivation signatures read; the walk interns the rest by export name at M1.

const std = @import("std");
const ir = @import("ir.zig");
const types = @import("types.zig");
const float_bits = @import("builtins").float_bits;

const PrimId = ir.PrimId;

/// The builtin module a primitive belongs to.
pub const Owner = enum(u8) {
    bool_,
    str,
    list,
    /// `Iter`, whose `collect` layer L reads (N16e).
    iter,
    u8,
    i8,
    u16,
    i16,
    u32,
    i32,
    u64,
    i64,
    u128,
    i128,
    f32,
    f64,

    /// The integer type this owner is, if it is one.
    pub fn int(self: Owner) ?types.IntTy {
        return switch (self) {
            .u8 => .u8,
            .i8 => .i8,
            .u16 => .u16,
            .i16 => .i16,
            .u32 => .u32,
            .i32 => .i32,
            .u64 => .u64,
            .i64 => .i64,
            .u128 => .u128,
            .i128 => .i128,
            .bool_, .str, .list, .iter, .f32, .f64 => null,
        };
    }

    /// The owner of integer type `t`.
    pub fn ofInt(t: types.IntTy) Owner {
        return switch (t) {
            .u8 => .u8,
            .i8 => .i8,
            .u16 => .u16,
            .i16 => .i16,
            .u32 => .u32,
            .i32 => .i32,
            .u64 => .u64,
            .i64 => .i64,
            .u128 => .u128,
            .i128 => .i128,
        };
    }

    /// The float type this owner is, if it is one.
    pub fn float(self: Owner) ?types.FloatTy {
        return switch (self) {
            .f32 => .f32,
            .f64 => .f64,
            .bool_, .str, .list, .iter, .u8, .i8, .u16, .i16, .u32, .i32, .u64, .i64, .u128, .i128 => null,
        };
    }

    /// Whether this owner is a number type.
    pub fn isNum(self: Owner) bool {
        return self.int() != null or self.float() != null;
    }

    /// The qualified module name, as `Builtin.roc` exports it.
    pub fn text(self: Owner) []const u8 {
        return switch (self) {
            .bool_ => "Bool",
            .str => "Str",
            .list => "List",
            .iter => "Iter",
            .u8 => "Num.U8",
            .i8 => "Num.I8",
            .u16 => "Num.U16",
            .i16 => "Num.I16",
            .u32 => "Num.U32",
            .i32 => "Num.I32",
            .u64 => "Num.U64",
            .i64 => "Num.I64",
            .u128 => "Num.U128",
            .i128 => "Num.I128",
            .f32 => "Num.F32",
            .f64 => "Num.F64",
        };
    }
};

/// A builtin's method name. The declaration order is part of the op
/// precedence the orientation check breaks ties with.
pub const Method = enum(u8) {
    is_eq,
    is_lt,
    is_lte,
    is_gt,
    is_gte,
    not,
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
    len,
    get,
    /// The builtins layer L reads (normal-form 3.16).
    is_empty,
    append,
    map,
    keep_if,
    fold,
    collect,
};

/// One builtin's entry.
pub const Prim = struct {
    owner: Owner,
    method: Method,
    /// The operand count; an associative builtin takes this many or more,
    /// as a chain N15a flattened (normal-form 3.15).
    arity: u8,
    speculatable: bool,
    associative: bool,

    /// Whether a `Prim` of this builtin may have `n` operands.
    pub fn takes(self: Prim, n: usize) bool {
        return if (self.associative) n >= self.arity else n == self.arity;
    }
};

fn methodApplies(owner: Owner, method: Method) bool {
    return switch (method) {
        .is_eq => owner != .iter,
        .is_lt, .is_lte, .is_gt, .is_gte, .plus, .minus, .times => owner.isNum(),
        .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor => owner.int() != null,
        .not => owner == .bool_,
        .concat => owner == .str or owner == .list,
        .len, .get, .is_empty, .append, .map, .keep_if, .fold => owner == .list,
        .collect => owner == .iter,
    };
}

fn arityOf(method: Method) u8 {
    return switch (method) {
        .not, .len, .is_empty, .collect => 1,
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .get, .append, .map, .keep_if => 2,
        .fold => 3,
    };
}

// Integer `plus`, `minus` and `times` crash on overflow and `div_trunc` on a
// zero divisor, so they are not speculatable; float arithmetic cannot crash.
// `List.is_empty` is `List.len(list) == 0` (`Builtin.roc`), so it cannot
// crash. A builtin that calls a function it is given can crash where the
// function does, and `append`, `collect` stay off the list, as any builtin
// can, since leaving one off is sound (normal-form 1.1).
fn speculatableOf(owner: Owner, method: Method) bool {
    return switch (method) {
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty => true,
        .plus, .minus, .times => owner.float() != null,
        .div_trunc, .append, .map, .keep_if, .fold, .collect => false,
    };
}

/// Whether a two-operand call of `method` at `owner` puts a literal operand
/// last (N15c): integer `plus` and `times`, and `is_eq` over an integer type
/// or `Str`.
pub fn ordersLiteralLast(owner: Owner, method: Method) bool {
    return switch (method) {
        .plus, .times => owner.int() != null,
        .is_eq => owner.int() != null or owner == .str,
        .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .is_lt, .is_lte, .is_gt, .is_gte, .not, .minus, .div_trunc, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect => false,
    };
}

/// Whether `method` is associative, so a chain of it flattens (N15a).
pub fn associativeOf(method: Method) bool {
    return switch (method) {
        .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat => true,
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus, .minus, .times, .div_trunc, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect => false,
    };
}

const owner_count = @typeInfo(Owner).@"enum".field_names.len;
const method_count = @typeInfo(Method).@"enum".field_names.len;

const table_len = blk: {
    @setEvalBranchQuota(10_000);
    var n: usize = 0;
    for (0..owner_count) |o| {
        for (0..method_count) |m| {
            if (methodApplies(@fromBackingInt(@intCast(o)), @fromBackingInt(@intCast(m)))) n += 1;
        }
    }
    break :blk n;
};

/// Every builtin, in owner then method order. `PrimId` indexes this array.
pub const table: [table_len]Prim = blk: {
    @setEvalBranchQuota(10_000);
    var out: [table_len]Prim = undefined;
    var n: usize = 0;
    for (0..owner_count) |o| {
        for (0..method_count) |m| {
            const owner: Owner = @fromBackingInt(@intCast(o));
            const method: Method = @fromBackingInt(@intCast(m));
            if (!methodApplies(owner, method)) continue;
            out[n] = .{
                .owner = owner,
                .method = method,
                .arity = arityOf(method),
                .speculatable = speculatableOf(owner, method),
                .associative = associativeOf(method),
            };
            n += 1;
        }
    }
    break :blk out;
};

/// A fingerprint of the builtin table for `Code.version` (I11): every
/// entry by name, with its arity, whether it is speculatable, whether it is
/// associative and whether N15c puts a literal operand last.
pub fn fingerprint() u64 {
    var h = std.hash.Wyhash.init(0);
    for (table) |p| {
        h.update(@tagName(p.owner));
        h.update(".");
        h.update(@tagName(p.method));
        h.update(&.{ p.arity, @intFromBool(p.speculatable), @intFromBool(p.associative), @intFromBool(ordersLiteralLast(p.owner, p.method)) });
    }
    return h.final();
}

const lookup_table: [owner_count][method_count]?PrimId = blk: {
    @setEvalBranchQuota(10_000);
    var out: [owner_count][method_count]?PrimId = @splat(@splat(null));
    for (table, 0..) |p, i| out[@backingInt(p.owner)][@backingInt(p.method)] = PrimId.of(i);
    break :blk out;
};

/// The builtin `owner.method`, if it exists.
pub fn find(owner: Owner, method: Method) ?PrimId {
    return lookup_table[@backingInt(owner)][@backingInt(method)];
}

/// The entry of `id`, which the table holds.
pub fn get(id: PrimId) Prim {
    return table[id.index()];
}

/// The entry of `id`, or null for a builtin the table does not hold, or a
/// function of another package, which the store names (`ir.Store.primName`).
pub fn lookup(id: PrimId) ?Prim {
    return if (id.index() < table.len) table[id.index()] else null;
}

/// The name `Builtin.roc` gives `method`.
pub fn methodName(method: Method) []const u8 {
    return switch (method) {
        .div_trunc => "div_trunc_by",
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus, .minus, .times, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect => @tagName(method),
    };
}

/// The table's builtin that `Builtin.roc` names `owner.method`, if the table
/// holds it. `owner` is the qualified module name without `Builtin.`.
pub fn findNamed(owner: []const u8, method: []const u8) ?PrimId {
    const o = for (std.enums.values(Owner)) |candidate| {
        if (std.mem.eql(u8, candidate.text(), owner)) break candidate;
    } else return null;
    const m = for (std.enums.values(Method)) |candidate| {
        if (std.mem.eql(u8, methodName(candidate), method)) break candidate;
    } else return null;
    return find(o, m);
}

/// The module every builtin's qualified name starts with.
const builtin_prefix = "Builtin.";

/// A named `Prim` key: the owner a qualified name spells, and its method.
pub const Named = struct { owner: []const u8, method: []const u8 };

/// The owner and method a builtin's export name spells: `Builtin.Num.I64.plus`
/// is `Num.I64` and `plus`, the pair `findNamed` and a named `Prim` key take.
pub fn namedOfExport(export_name: []const u8) ?Named {
    const path = ownerOfTypeName(export_name);
    const dot = std.mem.findScalarLast(u8, path, '.') orelse return null;
    return .{ .owner = path[0..dot], .method = path[dot + 1 ..] };
}

/// The owner a type's qualified name gives its methods: a builtin's name
/// without `Builtin.`, the way every builtin `Prim` is owned.
pub fn ownerOfTypeName(type_name: []const u8) []const u8 {
    return if (std.mem.startsWith(u8, type_name, builtin_prefix)) type_name[builtin_prefix.len..] else type_name;
}

/// A builtin's value over literal operands (N13j, N13k). A `str` is owned by
/// the caller of the fold that made it.
pub const Folded = union(enum) { bool_: bool, int: i256, float: u64, str: []u8 };

/// The identity of associative integer builtin `method` at `int`, the
/// operand N15a drops from a chain; null for a builtin without one. The
/// all-ones identity of `bitwise_and` is -1 read signed.
pub fn identityInt(int: types.IntTy, method: Method) ?i256 {
    return switch (method) {
        .plus_wrap, .bitwise_or, .bitwise_xor => 0,
        .times_wrap => 1,
        .bitwise_and => if (int.signed()) -1 else int.max(),
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus, .minus, .times, .div_trunc, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect => null,
    };
}

/// The literal that absorbs associative integer builtin `method` at `int`:
/// a chain with it as an operand is it, whatever the other operands are.
/// Null for a builtin without one. The all-ones absorber of `bitwise_or`
/// is -1 read signed.
pub fn absorbingInt(int: types.IntTy, method: Method) ?i256 {
    return switch (method) {
        .times_wrap, .bitwise_and => 0,
        .bitwise_or => if (int.signed()) -1 else int.max(),
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus, .minus, .times, .div_trunc, .plus_wrap, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect => null,
    };
}

/// `foldInt` over every operand of a `Prim`: an associative chain folds
/// from the left, and any other builtin has its arity's operands.
pub fn foldIntAll(int: types.IntTy, method: Method, vals: []const i256) ?Folded {
    var acc = foldInt(int, method, vals[0], if (vals.len > 1) vals[1] else 0) orelse return null;
    for (vals[@min(vals.len, 2)..]) |v| acc = foldInt(int, method, acc.int, v) orelse return null;
    return acc;
}

/// The value of integer builtin `method` at `int` over `a` and `b` (`b` is
/// unread for a unary method), or null where the builtin fails: checked
/// arithmetic out of range, or a zero divisor.
pub fn foldInt(int: types.IntTy, method: Method, a: i256, b: i256) ?Folded {
    const in = struct {
        fn range(t: types.IntTy, v: i256) ?Folded {
            return if (v >= t.min() and v <= t.max()) .{ .int = v } else null;
        }
    };
    return switch (method) {
        .is_eq => .{ .bool_ = a == b },
        .is_lt => .{ .bool_ = a < b },
        .is_lte => .{ .bool_ = a <= b },
        .is_gt => .{ .bool_ = a > b },
        .is_gte => .{ .bool_ = a >= b },
        .plus => in.range(int, a + b),
        .minus => in.range(int, a - b),
        .times => in.range(int, a * b),
        .div_trunc => if (b == 0) null else in.range(int, @divTrunc(a, b)),
        .plus_wrap => .{ .int = wrapTo(int, a + b) },
        .times_wrap => .{ .int = wrapTo(int, a * b) },
        .bitwise_and => .{ .int = wrapTo(int, a & b) },
        .bitwise_or => .{ .int = wrapTo(int, a | b) },
        .bitwise_xor => .{ .int = wrapTo(int, a ^ b) },
        .not, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect => unreachable, // integer prims admit no other methods (methodApplies)
    };
}

/// The value of float builtin `method` at `float` over the bits of its
/// operands. The operations are the IEEE-754 ones of the type, in strict
/// float mode, and a `NaN` result is Roc's canonical `NaN`, the bits Roc gives
/// a `NaN` it observes (`float_bits`). No host math library is called, so the
/// bits are the same on every host (plan 1.9). Null where the table has no
/// float builtin by that method.
pub fn foldFloat(float: types.FloatTy, method: Method, a_bits: u64, b_bits: u64) ?Folded {
    return switch (float) {
        .f64 => floatFold(f64, method, @bitCast(a_bits), @bitCast(b_bits)),
        .f32 => floatFold(f32, method, @bitCast(@as(u32, @truncate(a_bits))), @bitCast(@as(u32, @truncate(b_bits)))),
    };
}

fn floatFold(comptime F: type, method: Method, a: F, b: F) ?Folded {
    const Bits = @Int(.unsigned, @bitSizeOf(F));
    const arith = struct {
        fn bits(v: F) Folded {
            const raw: Bits = @bitCast(v);
            return .{ .float = if (F == f32) float_bits.normalizeF32NanBits(raw) else float_bits.normalizeF64NanBits(raw) };
        }
    };
    return switch (method) {
        .is_eq => .{ .bool_ = a == b },
        .is_lt => .{ .bool_ = a < b },
        .is_lte => .{ .bool_ = a <= b },
        .is_gt => .{ .bool_ = a > b },
        .is_gte => .{ .bool_ = a >= b },
        .plus => arith.bits(a + b),
        .minus => arith.bits(a - b),
        .times => arith.bits(a * b),
        .not, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect => null,
    };
}

/// `v` reduced into the range of `int` by two's-complement wrapping.
pub fn wrapTo(int: types.IntTy, v: i256) i256 {
    const modulus = @as(i256, 1) << int.bits();
    var r = @mod(v, modulus);
    if (int.signed() and r > int.max()) r -= modulus;
    return r;
}

/// The owner a builtin integer type's builtins belong to.
pub fn intOwner(int: types.IntTy) Owner {
    return switch (int) {
        .u8 => .u8,
        .i8 => .i8,
        .u16 => .u16,
        .i16 => .i16,
        .u32 => .u32,
        .i32 => .i32,
        .u64 => .u64,
        .i64 => .i64,
        .u128 => .u128,
        .i128 => .i128,
    };
}

/// The owner of a float type's builtins.
pub fn floatOwner(float: types.FloatTy) Owner {
    return switch (float) {
        .f32 => .f32,
        .f64 => .f64,
    };
}

test "every builtin is found under its owner and method" {
    for (table, 0..) |p, i| {
        try std.testing.expectEqual(PrimId.of(@intCast(i)), find(p.owner, p.method).?);
    }
    try std.testing.expect(find(.bool_, .plus) == null);
    const plus = get(find(.i64, .plus).?);
    try std.testing.expect(!plus.speculatable);
    try std.testing.expect(get(find(.f64, .plus).?).speculatable);
    try std.testing.expect(get(find(.i64, .is_lt).?).speculatable);
}

test "a builtin is found by the names Builtin.roc gives it, and one the table lacks is not" {
    try std.testing.expectEqual(find(.i64, .div_trunc).?, findNamed("Num.I64", "div_trunc_by").?);
    try std.testing.expectEqual(find(.str, .concat).?, findNamed("Str", "concat").?);
    try std.testing.expect(findNamed("Num.I64", "div_trunc") == null);
    try std.testing.expect(findNamed("Num.F32", "sin") == null);
    try std.testing.expect(lookup(PrimId.of(table.len)) == null);
}
