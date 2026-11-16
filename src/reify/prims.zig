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
    /// `Iter`, whose `collect` layer L reads (N16e), and whose `with_index`
    /// and `fold` N17h reads.
    iter,
    /// `Try`, whose `ok_or` N13c decides on a known tag.
    try_,
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
    /// `Num.Numeral`, the literal the compiler hands to a `from_numeral`
    /// conversion, whose accessors a conversion reads it through.
    numeral,

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
            .bool_, .str, .list, .iter, .try_, .f32, .f64, .numeral => null,
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
            .bool_, .str, .list, .iter, .try_, .u8, .i8, .u16, .i16, .u32, .i32, .u64, .i64, .u128, .i128, .numeral => null,
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
            .try_ => "Try",
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
            .numeral => "Num.Numeral",
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
    /// The builtins whose results N17 reads off a known list (normal-form 3.17).
    first,
    last,
    prepend,
    single,
    with_capacity,
    set,
    drop_first,
    take_first,
    repeat,
    map2,
    map_with_index,
    fold_rev,
    sum,
    any,
    all,
    fold_with_index,
    /// The builtins over an iterator whose items N17h reads off a known
    /// list: `Iter.with_index` and `List.from_iter` (`Iter.fold` is `fold`).
    with_index,
    from_iter,
    /// The builtin of `Try` N13c decides on a known tag.
    ok_or,
    /// An integer type's conversion of a `Num.Numeral` (`numeral_methods`).
    from_numeral,
    /// The accessors of `Num.Numeral`.
    is_negative,
    digits_before_pt,
    digits_after_pt,
    digits_after_pt_count,
};

/// The builtins over a `Num.Numeral`: an integer type's `from_numeral` and
/// the accessors. No rule folds them; the evaluator computes them
/// (`fromNumeral`).
pub fn isNumeralMethod(method: Method) bool {
    return switch (method) {
        .from_numeral, .is_negative, .digits_before_pt, .digits_after_pt, .digits_after_pt_count => true,
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect, .first, .last, .prepend, .single, .with_capacity, .set, .drop_first, .take_first, .repeat, .map2, .map_with_index, .fold_rev, .sum, .any, .all, .fold_with_index, .with_index, .from_iter, .ok_or => false,
    };
}

/// One builtin's entry.
pub const Prim = struct {
    owner: Owner,
    method: Method,
    /// The operand count; an associative builtin takes this many or more,
    /// as a chain N15a flattened (normal-form 3.15).
    arity: u8,
    speculatable: bool,
    associative: bool,

    /// Whether a `Prim` of this builtin may have `n` operands. A checked
    /// integer `plus` takes more than two as a chain whose operands'
    /// intervals prove that no grouping overflows (N13u, N15a).
    pub fn takes(self: Prim, n: usize) bool {
        if (self.method == .plus and self.owner.int() != null) return n >= self.arity;
        return if (self.associative) n >= self.arity else n == self.arity;
    }
};

fn methodApplies(owner: Owner, method: Method) bool {
    return switch (method) {
        .is_eq => owner != .iter and owner != .numeral,
        .is_lt, .is_lte, .is_gt, .is_gte, .plus, .minus, .times => owner.isNum(),
        .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor => owner.int() != null,
        .not => owner == .bool_,
        .concat => owner == .str or owner == .list,
        .len, .get, .is_empty, .append, .map, .keep_if => owner == .list,
        .fold => owner == .list or owner == .iter,
        .with_index => owner == .iter,
        .from_iter => owner == .list,
        .first, .last, .prepend, .single, .with_capacity, .set, .drop_first, .take_first, .repeat, .map2, .map_with_index, .fold_rev, .sum, .any, .all, .fold_with_index => owner == .list,
        .collect => owner == .iter,
        .ok_or => owner == .try_,
        .from_numeral => owner.int() != null,
        .is_negative, .digits_before_pt, .digits_after_pt, .digits_after_pt_count => owner == .numeral,
    };
}

fn arityOf(method: Method) u8 {
    return switch (method) {
        .not, .len, .is_empty, .collect, .first, .last, .single, .with_capacity, .sum, .with_index, .from_iter, .from_numeral, .is_negative, .digits_before_pt, .digits_after_pt, .digits_after_pt_count => 1,
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .get, .append, .map, .keep_if, .prepend, .drop_first, .take_first, .repeat, .map_with_index, .any, .all, .ok_or => 2,
        .fold, .set, .map2, .fold_rev, .fold_with_index => 3,
    };
}

// Integer `plus`, `minus` and `times` crash on overflow and `div_trunc` on a
// zero divisor, so they are not speculatable; float arithmetic cannot crash.
// `List.is_empty` is `List.len(list) == 0` (`Builtin.roc`), so it cannot
// crash. A builtin that calls a function it is given can crash where the
// function does, and `append`, `collect` stay off the list, as any builtin
// can, since leaving one off is sound (normal-form 1.1). The builtins N17
// reads stay off it as they were before the table held them.
fn speculatableOf(owner: Owner, method: Method) bool {
    return switch (method) {
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty => true,
        .plus, .minus, .times => owner.float() != null,
        .div_trunc, .append, .map, .keep_if, .fold, .collect => false,
        .first, .last, .prepend, .single, .with_capacity, .set, .drop_first, .take_first, .repeat, .map2, .map_with_index, .fold_rev, .sum, .any, .all, .fold_with_index, .with_index, .from_iter, .ok_or => false,
        // The numeral builtins cannot crash, and stay off the list as N17's do.
        .from_numeral, .is_negative, .digits_before_pt, .digits_after_pt, .digits_after_pt_count => false,
    };
}

/// Whether a two-operand call of `method` at `owner` puts a literal operand
/// last (N15c): integer `plus` and `times`, and `is_eq` over an integer type
/// or `Str`.
pub fn ordersLiteralLast(owner: Owner, method: Method) bool {
    return switch (method) {
        .plus, .times => owner.int() != null,
        .is_eq => owner.int() != null or owner == .str,
        .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .is_lt, .is_lte, .is_gt, .is_gte, .not, .minus, .div_trunc, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect, .first, .last, .prepend, .single, .with_capacity, .set, .drop_first, .take_first, .repeat, .map2, .map_with_index, .fold_rev, .sum, .any, .all, .fold_with_index, .with_index, .from_iter, .ok_or, .from_numeral, .is_negative, .digits_before_pt, .digits_after_pt, .digits_after_pt_count => false,
    };
}

/// Whether `method` is associative, so a chain of it flattens (N15a).
pub fn associativeOf(method: Method) bool {
    return switch (method) {
        .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat => true,
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus, .minus, .times, .div_trunc, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect, .first, .last, .prepend, .single, .with_capacity, .set, .drop_first, .take_first, .repeat, .map2, .map_with_index, .fold_rev, .sum, .any, .all, .fold_with_index, .with_index, .from_iter, .ok_or, .from_numeral, .is_negative, .digits_before_pt, .digits_after_pt, .digits_after_pt_count => false,
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
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus, .minus, .times, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect, .first, .last, .prepend, .single, .with_capacity, .set, .drop_first, .take_first, .repeat, .map2, .map_with_index, .fold_rev, .sum, .any, .all, .fold_with_index, .with_index, .from_iter, .ok_or, .from_numeral, .is_negative, .digits_before_pt, .digits_after_pt, .digits_after_pt_count => @tagName(method),
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
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus, .minus, .times, .div_trunc, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect, .first, .last, .prepend, .single, .with_capacity, .set, .drop_first, .take_first, .repeat, .map2, .map_with_index, .fold_rev, .sum, .any, .all, .fold_with_index, .with_index, .from_iter, .ok_or, .from_numeral, .is_negative, .digits_before_pt, .digits_after_pt, .digits_after_pt_count => null,
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
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus, .minus, .times, .div_trunc, .plus_wrap, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect, .first, .last, .prepend, .single, .with_capacity, .set, .drop_first, .take_first, .repeat, .map2, .map_with_index, .fold_rev, .sum, .any, .all, .fold_with_index, .with_index, .from_iter, .ok_or, .from_numeral, .is_negative, .digits_before_pt, .digits_after_pt, .digits_after_pt_count => null,
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
        // Two `U128` values multiply past `i256`; a product that far out
        // leaves every type, and a wrapped one keeps its low bits.
        .times => if (@mulWithOverflow(a, b)[1] == 1) null else in.range(int, a * b),
        .div_trunc => if (b == 0) null else in.range(int, @divTrunc(a, b)),
        .plus_wrap => .{ .int = wrapTo(int, a + b) },
        .times_wrap => .{ .int = wrapTo(int, a *% b) },
        .bitwise_and => .{ .int = wrapTo(int, a & b) },
        .bitwise_or => .{ .int = wrapTo(int, a | b) },
        .bitwise_xor => .{ .int = wrapTo(int, a ^ b) },
        .not, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect, .first, .last, .prepend, .single, .with_capacity, .set, .drop_first, .take_first, .repeat, .map2, .map_with_index, .fold_rev, .sum, .any, .all, .fold_with_index, .with_index, .from_iter, .ok_or, .is_negative, .digits_before_pt, .digits_after_pt, .digits_after_pt_count => unreachable, // integer prims admit no other methods (methodApplies)
        .from_numeral => unreachable, // an integer's from_numeral reads a Numeral, which no caller folds or evaluates here (isNumeralMethod)
    };
}

/// The value an integer type's `from_numeral` gives the `Num.Numeral` of
/// sign `negative`, base-256 digits `before` and `after` the point, and
/// `after_count` decimal digits after it, or null for its
/// `Err(InvalidNumeral(_))`. `Builtin.roc` writes the numeral as decimal
/// text (`numeral_to_str`) and parses it with the type's `from_str`. That
/// text has a point wherever `after_count` is not 0, and an integer's
/// `from_str` rejects a point, so every such numeral is an `Err`, `1.0`
/// too. The digits after the point are read only for that text, so they do
/// not matter. Otherwise the text is the sign and the value of `before`
/// (no digits is 0), and the parse gives that value where the type holds
/// it; `-0` is 0 at every type.
pub fn fromNumeral(int: types.IntTy, negative: bool, before: []const u8, after_count: u64) ?i256 {
    if (after_count != 0) return null;
    // Past every type's range the value is an `Err`, whatever its digits.
    const past: i256 = @as(i256, 1) << 129;
    var magnitude: i256 = 0;
    for (before) |digit| {
        magnitude = magnitude * 256 + digit;
        if (magnitude > past) return null;
    }
    const value = if (negative) -magnitude else magnitude;
    return if (value >= int.min() and value <= int.max()) value else null;
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
        .not, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect, .first, .last, .prepend, .single, .with_capacity, .set, .drop_first, .take_first, .repeat, .map2, .map_with_index, .fold_rev, .sum, .any, .all, .fold_with_index, .with_index, .from_iter, .ok_or, .from_numeral, .is_negative, .digits_before_pt, .digits_after_pt, .digits_after_pt_count => null,
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

test "an integer's from_numeral gives the value Builtin.roc's parse of the numeral's text gives" {
    const expectEqual = std.testing.expectEqual;
    // `7`, `0`, `-0` and no digits at all, which is `0`.
    try expectEqual(@as(?i256, 7), fromNumeral(.u64, false, &.{7}, 0));
    try expectEqual(@as(?i256, 0), fromNumeral(.u64, false, &.{}, 0));
    try expectEqual(@as(?i256, 0), fromNumeral(.u64, true, &.{}, 0));
    try expectEqual(@as(?i256, 0), fromNumeral(.u8, true, &.{0}, 0));
    // A negative number at an unsigned type, and at a signed one.
    try expectEqual(@as(?i256, null), fromNumeral(.u64, true, &.{3}, 0));
    try expectEqual(@as(?i256, -3), fromNumeral(.i64, true, &.{3}, 0));
    // The bounds of a type, and one past each.
    try expectEqual(@as(?i256, -128), fromNumeral(.i8, true, &.{128}, 0));
    try expectEqual(@as(?i256, null), fromNumeral(.i8, true, &.{129}, 0));
    try expectEqual(@as(?i256, null), fromNumeral(.i8, false, &.{128}, 0));
    try expectEqual(@as(?i256, 255), fromNumeral(.u8, false, &.{255}, 0));
    try expectEqual(@as(?i256, null), fromNumeral(.u8, false, &.{ 1, 0 }, 0));
    try expectEqual(@as(?i256, 256), fromNumeral(.u16, false, &.{ 1, 0 }, 0));
    try expectEqual(@as(?i256, std.math.maxInt(u64)), fromNumeral(.u64, false, &(@as([8]u8, @splat(255))), 0));
    try expectEqual(@as(?i256, null), fromNumeral(.u64, false, &([_]u8{1} ++ @as([8]u8, @splat(0))), 0));
    try expectEqual(@as(?i256, std.math.maxInt(u128)), fromNumeral(.u128, false, &(@as([16]u8, @splat(255))), 0));
    try expectEqual(@as(?i256, std.math.minInt(i128)), fromNumeral(.i128, true, &([_]u8{128} ++ @as([15]u8, @splat(0))), 0));
    // Leading zero digits are the same number, and far more digits than any
    // type holds are out of range.
    try expectEqual(@as(?i256, 300), fromNumeral(.u32, false, &.{ 0, 0, 1, 44 }, 0));
    try expectEqual(@as(?i256, null), fromNumeral(.u128, false, &([_]u8{1} ++ @as([40]u8, @splat(0))), 0));
    // A point is never an integer: `2.5`, `1.0`, `0.050` and `-0.0`.
    try expectEqual(@as(?i256, null), fromNumeral(.u64, false, &.{2}, 1));
    try expectEqual(@as(?i256, null), fromNumeral(.u64, false, &.{1}, 1));
    try expectEqual(@as(?i256, null), fromNumeral(.u64, false, &.{}, 3));
    try expectEqual(@as(?i256, null), fromNumeral(.i64, true, &.{}, 1));
}

test "the numeral builtins are found by the names Builtin.roc gives them" {
    try std.testing.expectEqual(find(.u64, .from_numeral).?, findNamed("Num.U64", "from_numeral").?);
    try std.testing.expectEqual(find(.numeral, .is_negative).?, findNamed("Num.Numeral", "is_negative").?);
    try std.testing.expectEqual(find(.numeral, .digits_after_pt_count).?, findNamed("Num.Numeral", "digits_after_pt_count").?);
    // `I64.is_negative` is not a numeral accessor, and a float's
    // `from_numeral` is not in the table.
    try std.testing.expect(findNamed("Num.I64", "is_negative") == null);
    try std.testing.expect(findNamed("Num.F64", "from_numeral") == null);
    try std.testing.expect(isNumeralMethod(.from_numeral) and !isNumeralMethod(.plus));
}
