//! Rename of an associated item of a type declared in a block. A use through
//! a local alias, as `C.zero`, is checked into a lookup of the item's binding,
//! and only its member is renamed. A sibling item's name is taken.

const std = @import("std");
const integration_spec = @import("integration_spec.zig");
const test_env = @import("integration_env.zig");
const Fixture = @import("issue_12292_test.zig").Fixture;
const reify_lsp = @import("reify_lsp_test.zig");
const Occurrence = reify_lsp.Occurrence;

/// Specs for renaming associated items through their uses.
pub const specs = [_]integration_spec.Spec{
    .{ .name = "rename member: uses through an alias, the type and bare keep their qualifiers", .run = renameKeepsQualifiers },
    .{ .name = "rename member: a sibling item's name is refused", .run = renameRefusesSiblingName },
};

const source =
    \\app [process_string] {{ pf: platform "{s}" }}
    \\
    \\process_string : Str -> Str
    \\process_string = |_text| {{
    \\    Cell := {{ n : I64 }}.{{
    \\        zero : I64
    \\        zero = 0
    \\
    \\        one : I64
    \\        one = zero + 1
    \\    }}
    \\    C : Cell
    \\    Str.concat(C.zero.to_str(), Cell.zero.to_str())
    \\}}
    \\
;

fn renameKeepsQualifiers() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(source, "rename_member_qualifiers.roc", &.{});
    defer fixture.deinit();

    // The annotation, the binder, the bare use, and the members of `C.zero` and `Cell.zero`.
    const zero = &[_]Occurrence{ .{ 5, 8, 12 }, .{ 6, 8, 12 }, .{ 9, 14, 18 }, .{ 12, 17, 21 }, .{ 12, 37, 41 } };
    try reify_lsp.expectRenameRanges(&fixture, 6, 9, "nil", "zero", zero);
    try reify_lsp.expectRenameRanges(&fixture, 12, 18, "nil", "zero", zero);
}

fn renameRefusesSiblingName() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(source, "rename_member_sibling.roc", &.{});
    defer fixture.deinit();

    const outcome = try fixture.checker.getRenameEditsAtPosition(fixture.file_uri, fixture.source, 6, 9, "one") orelse
        return error.TestUnexpectedResult;
    switch (outcome) {
        .rejected => |rejection| try std.testing.expect(rejection == .name_already_in_scope),
        .edits => |result| {
            result.deinit(test_env.allocator);
            std.debug.print("\nrename of `zero` to `one` was accepted\n", .{});
            return error.TestUnexpectedResult;
        },
    }
}
