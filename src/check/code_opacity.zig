//! Whether a type that a `Code.Binds` translator binds holds an opaque type
//! (design.md "Code Reification", rule "Bound Capture Encoding").
//!
//! The walk asks it of a slot's `Code.Ty`, to bind the slot as the bytes of
//! its encoder. The checker asks it of a capture read's solved type, to
//! require that encoder. Both ask through `holds` and `nominalRead`, so the
//! slots the walk encodes are the reads the checker requires an encoder for.

const std = @import("std");
const static_dispatch = @import("static_dispatch_registry.zig");

const Allocator = std.mem.Allocator;

/// What a type holds, in increasing order: the result of `holds` is the
/// largest of what its nodes are.
pub const Holds = enum(u8) {
    /// No opaque type and no type variable.
    nothing,
    /// A type variable that a later point in the module can still fix.
    open_variable,
    /// A type variable that stays a variable in the module.
    variable,
    /// An opaque type.
    opaque_,
};

/// What one node of a type is. An `inner` node appends the nodes it holds.
pub const Node = enum { inner, open_variable, variable, opaque_ };

/// What the type at `root` holds. `reader.read(id, pending)` returns what the
/// node `id` is, and appends to `pending` the nodes an `inner` node holds. A
/// function type is a leaf: a captured function is described as code. A
/// reader of a type with cycles appends each node once.
pub fn holds(comptime Id: type, gpa: Allocator, reader: anytype, root: Id) Allocator.Error!Holds {
    var pending = std.ArrayList(Id).empty;
    defer pending.deinit(gpa);
    try pending.append(gpa, root);
    var result: Holds = .nothing;
    while (pending.pop()) |current| {
        const found: Holds = switch (try reader.read(current, &pending)) {
            .inner => continue,
            .open_variable => .open_variable,
            .variable => .variable,
            .opaque_ => return .opaque_,
        };
        if (@backingInt(found) > @backingInt(result)) result = found;
    }
    return result;
}

/// How a slot type reads a nominal type.
pub const NominalRead = enum {
    /// A builtin scalar: `Bool`, `Str` or a number type.
    scalar,
    /// The builtin `List`, which holds its item type.
    list,
    /// The nominal's backing type, at the nominal's arguments.
    backing,
    /// An opaque type: a stage never reads its backing.
    opaque_,
};

/// How a slot type reads the nominal type that `owner` names (null for a
/// nominal that names no builtin owner, such as `Try` or a user type), of
/// opacity `is_opaque`. A builtin with a hidden representation is opaque, as
/// a `::` nominal is.
pub fn nominalRead(owner: ?static_dispatch.BuiltinOwner, is_opaque: bool) NominalRead {
    const builtin_owner = owner orelse return if (is_opaque) .opaque_ else .backing;
    return switch (builtin_owner) {
        .bool, .str, .u8, .i8, .u16, .i16, .u32, .i32, .u64, .i64, .u128, .i128, .f32, .f64, .dec => .scalar,
        .list => .list,
        .box,
        .dict,
        .set,
        .fields,
        .field,
        .u8x16,
        .i8x16,
        .u16x8,
        .i16x8,
        .u32x4,
        .i32x4,
        .u64x2,
        .i64x2,
        .parse_tag_union_spec,
        .crypto_sha256_digest,
        .crypto_sha256_hasher,
        .crypto_blake3_digest,
        .crypto_blake3_hasher,
        .iter,
        .stream,
        => .opaque_,
    };
}

test "a builtin with a hidden representation reads as opaque, a scalar and a list do not" {
    try std.testing.expectEqual(NominalRead.opaque_, nominalRead(.box, true));
    try std.testing.expectEqual(NominalRead.scalar, nominalRead(.str, true));
    try std.testing.expectEqual(NominalRead.list, nominalRead(.list, true));
    try std.testing.expectEqual(NominalRead.backing, nominalRead(null, false));
    try std.testing.expectEqual(NominalRead.opaque_, nominalRead(null, true));
}
