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
pub const match = @import("match.zig");
pub const rebuild = @import("rebuild.zig");
pub const number = @import("number.zig");
pub const loops = @import("loops.zig");
pub const scalar = @import("scalar.zig");
pub const fuzz_gen = @import("fuzz_gen.zig");

/// The normal-form version (I11). The rules, the speculatable lists and the
/// builtin table change only with it, so a `Code` value carries it and a
/// translator can put it in a cache key. `recorded` pins the fingerprint
/// each version was recorded with.
pub const normal_form_version: u32 = 10;

/// A fingerprint of what the normal-form version covers: the rule table,
/// the builtin table with its speculatable list, the speculatable list of
/// the ops, and the kinds of value a node reads.
pub fn fingerprint() u64 {
    var h = std.hash.Wyhash.init(0);
    h.update(std.mem.asBytes(&rules.fingerprint()));
    h.update(std.mem.asBytes(&prims.fingerprint()));
    for (std.enums.values(ir.Op)) |op| {
        h.update(@tagName(op));
        h.update(@tagName(builder.opSpeculatable(op)));
    }
    for (std.enums.values(ir.Ref.Kind)) |kind| h.update(@tagName(kind));
    for (std.enums.values(ir.RecordForm)) |form| h.update(@tagName(form));
    for (loops.steps) |step| h.update(step);
    for (scalar.steps) |step| h.update(step);
    // The conditions `speculatable` and `speculatable_rest` read the cone.
    h.update("speculatable reads the operand cone");
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
    // M4: input slots, the captured run-time values a root reads (N18), and
    // the kinds of value a node reads in the fingerprint.
    .{ .version = 4, .fingerprint = 0xc85b7416400dd35c },
    // M5: a `Record` node may leave an optional member unset, and says which
    // members it sets (`ir.RecordForm`).
    .{ .version = 5, .fingerprint = 0x087a981c03021a8a },
    // M4: a switch on `Str` equality against a literal is a literal switch
    // keyed by the string (N13n over `Str`), so the arms of a `match` on
    // string literals meet in any order (N7a, `match.zig`).
    .{ .version = 6, .fingerprint = 0x4664538352b123b1 },
    // M5 of the plan: literals of floats, `Str` and chains fold (N13j, N13k),
    // chains of `Str.concat` and `List.concat` flatten (N15a), a `Str`
    // literal goes last in an equality (N15c), and the hand-written
    // algorithms N7b, N13m, N13r and N13d over `Bool.not` run.
    .{ .version = 7, .fingerprint = 0x27ea5d8c8ceef391 },
    // M6 of the plan: three canonical loop forms. A row whose every call to
    // itself is a tail call is a `Loop` (N12); a loop's invariant, dead and
    // equal slots and unread outputs go (N11g to N11j); a loop over
    // `List.iter(xs)` is `ForList(xs)` (N11k); a counter `Loop` is a
    // `ForRange` and `ForRange(0, List.len(xs))` is `ForList(xs)` (N11l). A
    // general `Loop` has outputs of its own, apart from its slots.
    .{ .version = 8, .fingerprint = 0x97ad1e35a8feb8fb },
    // M7 of the plan: a record or tuple that a non-root row only reads by
    // field or index is one parameter per component, and a loop slot the
    // body only reads that way and every `Continue` gives as a construction
    // is one slot per component (N14a, N14b).
    .{ .version = 9, .fingerprint = 0x2255e015149a57ec },
    // Fix of T1.11: the speculatable conditions of the rules hold only when
    // the operand and every node it reads are speculatable, so `x - x` over
    // a field of a loop output keeps the loop.
    .{ .version = 10, .fingerprint = 0xb436a740a244c612 },
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
    std.testing.refAllDecls(@import("match.zig"));
    std.testing.refAllDecls(@import("rebuild.zig"));
    std.testing.refAllDecls(@import("number.zig"));
    std.testing.refAllDecls(@import("loops.zig"));
    std.testing.refAllDecls(@import("scalar.zig"));
    std.testing.refAllDecls(@import("fuzz_gen.zig"));
}
