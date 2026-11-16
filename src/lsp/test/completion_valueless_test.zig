//! Completion after `value.` leaves out an associated item that the checker
//! refuses to dispatch to because it has no value, such as a method whose
//! annotation is erroneous (`Check.valuelessMethod`).

const std = @import("std");
const integration_spec = @import("integration_spec.zig");
const test_env = @import("integration_env.zig");
const Fixture = @import("issue_12292_test.zig").Fixture;

/// Specs for items that a dispatch cannot select.
pub const specs = [_]integration_spec.Spec{
    .{ .name = "completion: a method with no value is not offered on a value", .run = valuelessMethodNotOffered },
};

const source =
    \\app [process_string] {{ pf: platform "{s}" }}
    \\
    \\Cell := {{ n : I64 }}.{{
    \\    open : Cell -> I64
    \\    open = |Cell.({{ n }})| n
    \\
    \\    peek : Cell -> Missing
    \\    peek = |_| 0
    \\}}
    \\
    \\process_string : Str -> Str
    \\process_string = |_text| {{
    \\    b = Cell.({{ n: 1 }})
    \\    b.open().to_str()
    \\}}
    \\
;

fn valuelessMethodNotOffered() integration_spec.SpecError!void {
    const allocator = test_env.allocator;
    var fixture: Fixture = undefined;
    // The undeclared type in `peek`'s annotation is the one problem.
    try fixture.initWithProblems(source, "completion_valueless.roc", &.{}, 1);
    defer fixture.deinit();

    const edited = try std.mem.replaceOwned(u8, allocator, fixture.source, "b.open().to_str()", "b.");
    defer allocator.free(edited);

    const result = try fixture.checker.getCompletionsAtPosition(fixture.file_uri, edited, 13, 6) orelse return error.TestUnexpectedResult;
    defer result.deinit();

    var has_open = false;
    var has_peek = false;
    for (result.items) |item| {
        if (std.mem.eql(u8, item.label, "open")) has_open = true;
        if (std.mem.eql(u8, item.label, "peek")) has_peek = true;
    }
    if (has_open and !has_peek) return;
    std.debug.print("\ncompletion after `b.` has open={} peek={}; items:", .{ has_open, has_peek });
    for (result.items) |item| std.debug.print(" {s}", .{item.label});
    std.debug.print("\n", .{});
    return error.TestUnexpectedResult;
}
