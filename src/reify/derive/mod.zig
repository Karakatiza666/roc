//! The rule-derivation tool's library (`roc-reify-rule-derivation.md`).
//!
//! A module of its own, so the compiler never imports it: `reify` holds no
//! inference, and `zig build reify-rules` is the only program that runs this.

/// The reify module the tool reads the rule table and builder from.
pub const reify = @import("reify");
pub const term = @import("term.zig");
pub const order = @import("order.zig");
pub const cp = @import("cp.zig");
pub const report = @import("report.zig");
pub const sig = @import("sig.zig");
pub const enumerate = @import("enumerate.zig");
pub const fingerprint = @import("fingerprint.zig");
pub const explore = @import("explore.zig");
pub const smt = @import("smt.zig");
pub const prove = @import("prove.zig");
pub const generalize = @import("generalize.zig");
pub const classify = @import("classify.zig");
pub const triage = @import("triage.zig");
pub const loop = @import("loop.zig");
pub const recall = @import("recall.zig");

test "reify derive tests" {
    const std = @import("std");
    std.testing.refAllDecls(@import("term.zig"));
    std.testing.refAllDecls(@import("order.zig"));
    std.testing.refAllDecls(@import("cp.zig"));
    std.testing.refAllDecls(@import("report.zig"));
    std.testing.refAllDecls(@import("sig.zig"));
    std.testing.refAllDecls(@import("enumerate.zig"));
    std.testing.refAllDecls(@import("fingerprint.zig"));
    std.testing.refAllDecls(@import("explore.zig"));
    std.testing.refAllDecls(@import("smt.zig"));
    std.testing.refAllDecls(@import("prove.zig"));
    std.testing.refAllDecls(@import("generalize.zig"));
    std.testing.refAllDecls(@import("classify.zig"));
    std.testing.refAllDecls(@import("triage.zig"));
    std.testing.refAllDecls(@import("loop.zig"));
    std.testing.refAllDecls(@import("recall.zig"));
    std.testing.refAllDecls(@import("derived_test.zig"));
    std.testing.refAllDecls(@import("holdout_test.zig"));
}
