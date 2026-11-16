//! Hover, goto definition and completion on a method of a type declared in a
//! block. The method's def is a statement of that block, so only its method
//! table entry (`ModuleEnv.lookupMethodBindingForOwnerConst`) reaches it.

const std = @import("std");
const integration_spec = @import("integration_spec.zig");
const test_env = @import("integration_env.zig");
const fixture_mod = @import("issue_12292_test.zig");
const Fixture = fixture_mod.Fixture;

/// Specs for methods of a type declared in a block.
pub const specs = [_]integration_spec.Spec{
    .{ .name = "block method: hover on a call shows the method's doc", .run = hoverShowsDoc },
    .{ .name = "block method: goto definition on a call goes to the method", .run = definitionGoesToMethod },
    .{ .name = "block method: completion after the receiver shows the method's type and doc", .run = completionShowsTypeAndDoc },
};

const source =
    \\app [process_string] {{ pf: platform "{s}" }}
    \\
    \\process_string : Str -> Str
    \\process_string = |_text| {{
    \\    Cell := {{ n : I64 }}.{{
    \\        ## Reads the box.
    \\        open : Cell -> I64
    \\        open = |Cell.({{ n }})| n
    \\    }}
    \\    b = Cell.({{ n: 1 }})
    \\    b.open().to_str()
    \\}}
    \\
;

fn hoverShowsDoc() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(source, "block_method_hover.roc", &.{});
    defer fixture.deinit();

    try fixture.expectHoverRange(10, 6, "Cell -> I64", "```roc\nI64\n", 6, 10);
    try fixture.expectHover(10, 6, "Reads the box.", "never matches");
}

fn definitionGoesToMethod() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(source, "block_method_definition.roc", &.{});
    defer fixture.deinit();

    try fixture.expectDefinition(10, 6, "block_method_definition.roc", 7);
}

fn completionShowsTypeAndDoc() integration_spec.SpecError!void {
    const allocator = test_env.allocator;
    var fixture: Fixture = undefined;
    try fixture.init(source, "block_method_completion.roc", &.{});
    defer fixture.deinit();

    const edited = try std.mem.replaceOwned(u8, allocator, fixture.source, "b.open().to_str()", "b.");
    defer allocator.free(edited);

    const result = try fixture.checker.getCompletionsAtPosition(fixture.file_uri, edited, 10, 6) orelse return error.TestUnexpectedResult;
    defer result.deinit();

    for (result.items) |item| {
        if (!std.mem.eql(u8, item.label, "open")) continue;
        const detail = item.detail orelse "";
        const documentation = item.documentation orelse "";
        if (std.mem.find(u8, detail, "Cell -> I64") != null and std.mem.find(u8, documentation, "Reads the box.") != null) return;
        std.debug.print("\n`open` has detail \"{s}\" and documentation \"{s}\"\n", .{ detail, documentation });
        return error.TestUnexpectedResult;
    }
    std.debug.print("\ncompletion after `b.` misses `open`; items:", .{});
    for (result.items) |item| std.debug.print(" {s}", .{item.label});
    std.debug.print("\n", .{});
    return error.TestUnexpectedResult;
}
