//! Language-server requests on names at reifying sites.
//!
//! Field completion on a lambda parameter at a `Code` position lists every
//! field of the parameter's type, as it does at an ordinary position.
//!
//! An associated item, such as the `code_primitives` list that a translator
//! declares and the reifier reads by name, has its declaration among its
//! references and highlights, with or without an annotation and uses.

const std = @import("std");
const integration_spec = @import("integration_spec.zig");
const test_env = @import("integration_env.zig");
const fixture_mod = @import("issue_12292_test.zig");
const Fixture = fixture_mod.Fixture;
const completeAt = @import("completion_modules_test.zig").completeAt;

/// Specs for language-server requests at reifying sites.
pub const specs = [_]integration_spec.Spec{
    .{ .name = "reify lsp: field completion on a lambda parameter at a Code position", .run = lambdaParameterFieldsAtCodePosition },
    .{ .name = "reify lsp: references and highlights of associated items", .run = associatedItemOccurrences },
    .{ .name = "reify lsp: expect test placeholder lists every field of a split record", .run = expectTestListsSplitRecordFields },
    .{ .name = "reify lsp: rename of an associated item keeps the qualifier of its uses", .run = renameAssociatedItem },
};

const field_kind: u32 = 5;

const product_template =
    \\app [process_string] {{ pf: platform "{s}" }}
    \\
    \\Product : {{ id : I64, title : Str, price : Dec }}
    \\
    \\describe : Code(Product -> out) -> Str
    \\describe = |code| code.version().to_str()
    \\
    \\shown : Str
    \\shown = describe(|p| {{ a: p.title, b: p.price }})
    \\
    \\process_string : Str -> Str
    \\process_string = |text| Str.concat(text, shown)
    \\
;

fn lambdaParameterFieldsAtCodePosition() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(product_template, "reify_lambda_fields.roc", &.{});
    defer fixture.deinit();

    const all = &.{ "id", "price", "title" };
    const kinds = &.{ .{ "id", field_kind }, .{ "price", field_kind }, .{ "title", field_kind } };
    // The checked buffer, with the cursor after the first `p.`.
    try completeAt(&fixture, "{ a: p.", "{ a: p.", all, &.{}, kinds);
    // An edited buffer, where the first access has no field yet.
    try completeAt(&fixture, "{ a: p.title", "{ a: p.", all, &.{}, kinds);
}

const shapes_template =
    \\app [process_string] {{ pf: platform "{s}" }}
    \\
    \\Shapes :: {{}}.{{
    \\    double : F64 -> F64
    \\    double = |x| x * 2.0
    \\
    \\    no_input : Str
    \\    no_input = "none"
    \\
    \\    code_primitives = [Code.prim(Shapes.double)]
    \\}}
    \\
    \\process_string : Str -> Str
    \\process_string = |text| Str.concat(text, Shapes.no_input)
    \\
;

/// One expected occurrence: a line and the columns it spans.
pub const Occurrence = struct { u32, u32, u32 };

fn associatedItemOccurrences() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(shapes_template, "reify_associated_items.roc", &.{});
    defer fixture.deinit();

    // An unannotated item with no uses is its own only occurrence.
    try expectOccurrences(&fixture, 9, 6, &.{.{ 9, 4, 19 }});
    // An annotated item: the annotation name, the binder and the use, once each.
    const no_input = &.{ .{ 6, 4, 12 }, .{ 7, 4, 12 }, .{ 13, 41, 56 } };
    try expectOccurrences(&fixture, 7, 6, no_input);
    try expectOccurrences(&fixture, 6, 6, no_input);
}

/// References with the declaration and document highlights at `line`:`col`
/// are exactly `expected`, in any order.
fn expectOccurrences(fixture: *Fixture, line: u32, col: u32, expected: []const Occurrence) integration_spec.SpecError!void {
    const allocator = test_env.allocator;
    const references = try fixture.checker.getReferencesAtPosition(fixture.file_uri, fixture.source, line, col, true) orelse {
        std.debug.print("\nreferences returned null at {d}:{d}\n", .{ line, col });
        return error.TestUnexpectedResult;
    };
    defer references.deinit(allocator);
    try expectRanges("references", line, col, references.regions, expected);

    const highlights = try fixture.checker.getHighlightsAtPosition(fixture.file_uri, fixture.source, line, col) orelse {
        std.debug.print("\nhighlights returned null at {d}:{d}\n", .{ line, col });
        return error.TestUnexpectedResult;
    };
    defer highlights.deinit(allocator);
    try expectRanges("highlights", line, col, highlights.regions, expected);
}

fn expectRanges(what: []const u8, line: u32, col: u32, ranges: anytype, expected: []const Occurrence) integration_spec.SpecError!void {
    var matched = ranges.len == expected.len;
    for (expected) |occurrence| {
        var found = false;
        for (ranges) |range| {
            if (range.start_line == occurrence[0] and range.end_line == occurrence[0] and
                range.start_col == occurrence[1] and range.end_col == occurrence[2]) found = true;
        }
        if (!found) matched = false;
    }
    if (matched) return;
    std.debug.print("\n{s} at {d}:{d} were:", .{ what, line, col });
    for (ranges) |range| std.debug.print(" {d}:{d}-{d}:{d}", .{ range.start_line, range.start_col, range.end_line, range.end_col });
    std.debug.print("\n", .{});
    return error.TestUnexpectedResult;
}

const split_record_template =
    \\app [process_string] {{ pf: platform "{s}" }}
    \\
    \\Product : {{ id : I64, title : Str }}
    \\
    \\show : Product -> Str
    \\show = |p| p.title
    \\
    \\pick = |p| Str.concat(p.title, show(p))
    \\
    \\process_string : Str -> Str
    \\process_string = |text| text
    \\
;

fn expectTestListsSplitRecordFields() integration_spec.SpecError!void {
    const allocator = test_env.allocator;
    var fixture: Fixture = undefined;
    try fixture.init(split_record_template, "reify_split_record_action.roc", &.{});
    defer fixture.deinit();

    const result = try fixture.checker.getCodeActions(fixture.file_uri, fixture.source, 7, 0, 7, 0) orelse
        return error.TestUnexpectedResult;
    defer result.deinit(allocator);

    for (result.actions) |action| {
        if (!std.mem.startsWith(u8, action.title, "Generate an expect test for 'pick'")) continue;
        const has_both = std.mem.find(u8, action.new_text, "title:") != null and
            std.mem.find(u8, action.new_text, "id:") != null;
        if (!has_both) std.debug.print("\nplaceholder was:\n{s}\n", .{action.new_text});
        try std.testing.expect(has_both);
        return;
    }
    std.debug.print("\nno expect test action was offered for 'pick'\n", .{});
    return error.TestUnexpectedResult;
}

fn renameAssociatedItem() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(shapes_template, "reify_rename_associated.roc", &.{});
    defer fixture.deinit();

    // The annotation name, the binder, and the member segment of the use.
    const no_input = &.{ .{ 6, 4, 12 }, .{ 7, 4, 12 }, .{ 13, 48, 56 } };
    try expectRenameRanges(&fixture, 7, 6, "nothing", "no_input", no_input);
    try expectRenameRanges(&fixture, 13, 50, "nothing", "no_input", no_input);
    // An item with no annotation and no uses.
    try expectRenameRanges(&fixture, 9, 6, "primitives", "code_primitives", &.{.{ 9, 4, 19 }});
    // A new name of another kind is still refused.
    const outcome = try fixture.checker.getRenameEditsAtPosition(fixture.file_uri, fixture.source, 7, 6, "Nothing") orelse
        return error.TestUnexpectedResult;
    switch (outcome) {
        .rejected => |rejection| try std.testing.expect(rejection == .bad_new_name and rejection.bad_new_name == .changes_ident_kind),
        .edits => |result| {
            result.deinit(test_env.allocator);
            return error.TestUnexpectedResult;
        },
    }
}

/// A rename at `line`:`col` to `new_name` replaces `old_name` at exactly `expected`.
pub fn expectRenameRanges(fixture: *Fixture, line: u32, col: u32, new_name: []const u8, old_name: []const u8, expected: []const Occurrence) integration_spec.SpecError!void {
    const outcome = try fixture.checker.getRenameEditsAtPosition(fixture.file_uri, fixture.source, line, col, new_name) orelse
        return error.TestUnexpectedResult;
    switch (outcome) {
        .rejected => |rejection| {
            std.debug.print("\nrename at {d}:{d} was rejected: {any}\n", .{ line, col, rejection });
            return error.TestUnexpectedResult;
        },
        .edits => |result| {
            defer result.deinit(test_env.allocator);
            try std.testing.expectEqualStrings(old_name, result.old_name);
            try expectRanges("rename edits", line, col, result.regions, expected);
        },
    }
}
