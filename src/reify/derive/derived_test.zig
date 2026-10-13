//! The tests of every row `--admit` wrote (`roc-reify-rule-derivation.md`
//! 3.6, plan 5.3): on its witness the row fires and the two sides meet, and
//! with the row knocked out it does not fire.

const std = @import("std");
const reify = @import("reify");
const term = @import("term.zig");
const sig_mod = @import("sig.zig");
const triage = @import("triage.zig");

const tests: []const triage.DerivedTest = @import("derived.zon");

fn rowOf(step: []const u8) ?usize {
    for (reify.rules.rules, 0..) |r, i| if (std.mem.eql(u8, r.step, step)) return i;
    return null;
}

test "every admitted row fires on its witness, joins it, and stops under its knockout" {
    const testing = std.testing;
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    for (tests) |t| {
        var vars = try sig_mod.Vars.base(a, sig_mod.find(t.signature).?);
        const lhs = try term.parse(a, t.lhs);
        const row = rowOf(t.step) orelse {
            std.debug.print("admitted row {s} is not in the table\n", .{t.step});
            return error.TestUnexpectedResult;
        };
        var knocked: [reify.rules.count]bool = @splat(false);
        var on: sig_mod.Instance = undefined;
        try on.init(testing.allocator, vars, lhs, .i64, true, &knocked);
        defer on.deinit();
        try testing.expect(on.b.hooks.fired[row] > 0);
        const l = try term.readBack(a, &on.store, &on.types, on.value);
        const r = try sig_mod.normalize(a, testing.allocator, vars, try term.parse(a, t.rhs), &knocked);
        try testing.expect(l.eql(r));
        knocked[row] = true;
        var off: sig_mod.Instance = undefined;
        try off.init(testing.allocator, vars, lhs, .i64, true, &knocked);
        defer off.deinit();
        try testing.expectEqual(@as(u32, 0), off.b.hooks.fired[row]);
        vars.deinit(a);
    }
}

test "every admitted step names one row" {
    for (tests) |t| {
        var rows: usize = 0;
        for (reify.rules.rules) |r| rows += @intFromBool(std.mem.eql(u8, r.step, t.step));
        try std.testing.expectEqual(@as(usize, 1), rows);
    }
}
