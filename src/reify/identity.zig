//! The identities a translator compares (opaque proposal D4, D6): the bits of
//! a `Code.PrimId` and of a `Code.TypeId`.
//!
//! The compiler keys primitives and nominals by their full identity
//! (`ir.PrimOrigin`, `types.Origin`). A translator compares these 128-bit
//! hashes of the same identities instead. `Prim.id` and `Opaque`'s type id
//! (`check/code_emit.zig`) and the constants `Code.prim` and `Code.type_id`
//! (`check/code_reifier.zig`) all come from the functions here, so an id the
//! walk emits equals the one the identity API gives for the same definition.
//!
//! A name can repeat: a module can declare its own `Bool` with a `not`, and
//! its `Prim` has the owner `Bool` and the method `not`, as the builtin's has.
//! An id cannot repeat: a builtin and a declared primitive hash different
//! inputs under different domain prefixes, so a translator that compares ids
//! never takes one for the other.
//!
//! | Identity | Hashed |
//! |---|---|
//! | builtin primitive | its owner and method (`Str`, `concat`), under the builtin prefix |
//! | primitive of a package | the artifact key of its module and its definition (`ir.Definition`) |
//! | builtin nominal | its name as a `Ty` spells it (`Dict`) |
//! | nominal a module declares | the content identity of its module and its declaration (`types.Declaration`) |

const std = @import("std");
const ir = @import("ir.zig");
const types = @import("types.zig");

/// The bits of the `Code.PrimId` of a builtin named `owner` and `method`.
pub fn builtinPrim(owner: []const u8, method: []const u8) u128 {
    var h = std.crypto.hash.Blake3.init(.{});
    h.update("roc prim builtin\x00");
    h.update(owner);
    h.update("\x00");
    h.update(method);
    return finish(&h);
}

/// The bits of the `Code.PrimId` of a function or constant of a package.
pub fn declaredPrim(definition: ir.Definition) u128 {
    var h = std.crypto.hash.Blake3.init(.{});
    h.update("roc prim declared\x00");
    h.update(&definition.module);
    h.update(std.mem.asBytes(&std.mem.nativeToLittle(u32, definition.def)));
    return finish(&h);
}

/// The bits of the `Code.PrimId` of the primitive a `Prim` node names.
pub fn prim(name: ir.PrimName) u128 {
    return switch (name.origin) {
        .builtin => builtinPrim(name.owner, name.method),
        .declared => |definition| declaredPrim(definition),
    };
}

/// The bits of the `Code.TypeId` of the builtin nominal a `Ty` names `name`.
pub fn builtinType(name: []const u8) u128 {
    var h = std.crypto.hash.Blake3.init(.{});
    h.update("roc type builtin\x00");
    h.update(name);
    return finish(&h);
}

/// The bits of the `Code.TypeId` of a nominal a module declares.
pub fn declaredType(declaration: types.Declaration) u128 {
    var h = std.crypto.hash.Blake3.init(.{});
    h.update("roc type declared\x00");
    h.update(&declaration.module);
    h.update(std.mem.asBytes(&std.mem.nativeToLittle(u32, declaration.decl)));
    return finish(&h);
}

fn finish(h: *std.crypto.hash.Blake3) u128 {
    var out: [16]u8 = undefined;
    h.final(&out);
    return std.mem.readInt(u128, &out, .little);
}

test "a builtin and a package function of one name have two ids, and one definition has one" {
    const time: ir.Definition = .{ .module = @splat(1), .def = 4 };
    const other: ir.Definition = .{ .module = @splat(2), .def = 4 };
    try std.testing.expectEqual(declaredPrim(time), prim(.{ .owner = "Time", .method = "is_lt", .origin = .{ .declared = time } }));
    try std.testing.expect(declaredPrim(time) != declaredPrim(other));
    try std.testing.expect(builtinPrim("Str", "concat") != builtinPrim("Str", "concat_"));
    try std.testing.expect(builtinPrim("Str", "concat") != builtinPrim("Strc", "oncat"));
    try std.testing.expect(builtinType("Dict") != declaredType(.{ .module = @splat(0), .decl = 0 }));
}
