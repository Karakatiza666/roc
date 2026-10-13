//! Reification normal form: the IR, its builder, and the passes over it.
//!
//! `roc-reify-normalization-plan.md` is the plan this module implements. The
//! module depends on no compiler stage, so its tests build graphs directly.

pub const ir = @import("ir.zig");
pub const types = @import("types.zig");
pub const prims = @import("prims.zig");
pub const rules = @import("rules/table.zig");
pub const ledger = @import("rules/ledger.zig");
pub const builder = @import("builder.zig");
pub const eval = @import("eval.zig");
pub const verify = @import("verify.zig");
pub const dump = @import("dump.zig");
pub const polarity = @import("polarity.zig");
pub const measure = @import("measure.zig");
pub const digest = @import("digest.zig");
pub const equal = @import("equal.zig");
pub const driver = @import("driver.zig");
pub const rows = @import("rows.zig");
pub const views = @import("views.zig");
pub const provenance = @import("provenance.zig");
pub const live = @import("live.zig");
pub const place = @import("place.zig");
pub const rebuild = @import("rebuild.zig");
pub const number = @import("number.zig");
pub const fuzz_gen = @import("fuzz_gen.zig");

/// The normal-form version (I11). The rules, the speculatable lists and the
/// builtin table change only with it, so a `Code` value carries it and a
/// translator can put it in a cache key. `recorded` pins the fingerprint
/// each version was recorded with.
pub const normal_form_version: u32 = 3;

/// A fingerprint of what the normal-form version covers: the rule table,
/// the builtin table with its speculatable list, and the speculatable list
/// of the ops.
pub fn fingerprint() u64 {
    var h = std.hash.Wyhash.init(0);
    h.update(std.mem.asBytes(&rules.fingerprint()));
    h.update(std.mem.asBytes(&prims.fingerprint()));
    for (std.enums.values(ir.Op)) |op| {
        h.update(@tagName(op));
        h.update(@tagName(builder.opSpeculatable(op)));
    }
    return h.final();
}

/// One released normal-form version and the fingerprint it was recorded with.
const Recorded = struct { version: u32, fingerprint: u64 };

/// Every version, oldest first. A change to the rules, the builtin table or
/// the ops' speculatable list adds an entry here with a new
/// `normal_form_version`; an entry is never edited.
const recorded = [_]Recorded{
    .{ .version = 1, .fingerprint = 0x5a5d7334dda2ac80 },
    // M2: `Payload` and `Elem` are not speculatable, and placement and
    // numbering are canonical.
    .{ .version = 2, .fingerprint = 0x12998df01d3edf85 },
    // M3: `Apply`, rows finalized before their callers with digests and
    // first-read parameters, and the `graph` view.
    .{ .version = 3, .fingerprint = 0x8b7cdb45472514a6 },
};

const std = @import("std");

test "the normal-form version changes exactly when the rules, the builtin table or the ops' speculatable list do" {
    const last = recorded[recorded.len - 1];
    try std.testing.expectEqual(normal_form_version, last.version);
    try std.testing.expectEqual(last.fingerprint, fingerprint());
    for (recorded[1..], recorded[0 .. recorded.len - 1]) |later, earlier| {
        try std.testing.expect(later.version > earlier.version);
        try std.testing.expect(later.fingerprint != earlier.fingerprint);
    }
}

test "reify tests" {
    std.testing.refAllDecls(@import("ir.zig"));
    std.testing.refAllDecls(@import("types.zig"));
    std.testing.refAllDecls(@import("prims.zig"));
    std.testing.refAllDecls(@import("rules/table.zig"));
    std.testing.refAllDecls(@import("rules/ledger.zig"));
    std.testing.refAllDecls(@import("builder.zig"));
    std.testing.refAllDecls(@import("eval.zig"));
    std.testing.refAllDecls(@import("verify.zig"));
    std.testing.refAllDecls(@import("dump.zig"));
    std.testing.refAllDecls(@import("polarity.zig"));
    std.testing.refAllDecls(@import("measure.zig"));
    std.testing.refAllDecls(@import("digest.zig"));
    std.testing.refAllDecls(@import("equal.zig"));
    std.testing.refAllDecls(@import("driver.zig"));
    std.testing.refAllDecls(@import("rows.zig"));
    std.testing.refAllDecls(@import("views.zig"));
    std.testing.refAllDecls(@import("provenance.zig"));
    std.testing.refAllDecls(@import("live.zig"));
    std.testing.refAllDecls(@import("place.zig"));
    std.testing.refAllDecls(@import("rebuild.zig"));
    std.testing.refAllDecls(@import("number.zig"));
    std.testing.refAllDecls(@import("fuzz_gen.zig"));
}
