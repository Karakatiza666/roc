//! Hover on an intrinsic, a declaration with a type and no Roc body, shows
//! the badge "intrinsic: no Roc body" after the type. Hover on anything else
//! does not.

const integration_spec = @import("integration_spec.zig");
const fixture_mod = @import("issue_12292_test.zig");
const Fixture = fixture_mod.Fixture;

/// Hover specs for intrinsics.
pub const specs = [_]integration_spec.Spec{
    .{ .name = "intrinsic hover: the declaration name of an intrinsic shows the badge", .run = hoverOnDeclarationShowsBadge },
    .{ .name = "intrinsic hover: a local use of an intrinsic shows the badge", .run = hoverOnLocalUseShowsBadge },
    .{ .name = "intrinsic hover: a use of an intrinsic of an imported module shows the badge", .run = hoverOnImportedUseShowsBadge },
    .{ .name = "intrinsic hover: a function with a body shows no badge", .run = hoverOnFunctionWithBodyShowsNoBadge },
};

const badge = "intrinsic: no Roc body";

fn hoverOnDeclarationShowsBadge() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\is_email : Str -> Bool
        \\
        \\process_string : Str -> Str
        \\process_string = |text| text
        \\
    , "hover_intrinsic_declaration.roc", &.{});
    defer fixture.deinit();

    try fixture.expectHover(2, 2, badge, "never matches");
}

fn hoverOnLocalUseShowsBadge() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\is_email : Str -> Bool
        \\
        \\check_email : Str -> Bool
        \\check_email = |text| is_email(text)
        \\
        \\process_string : Str -> Str
        \\process_string = |text| text
        \\
    , "hover_intrinsic_local_use.roc", &.{});
    defer fixture.deinit();

    try fixture.expectHover(5, 26, badge, "never matches");
}

fn hoverOnImportedUseShowsBadge() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\import Text
        \\
        \\check_email : Str -> Bool
        \\check_email = |text| Text.is_email(text)
        \\
        \\process_string : Str -> Str
        \\process_string = |text| text
        \\
    , "hover_intrinsic_imported_use.roc", &.{.{ .name = "Text.roc", .source = text_source }});
    defer fixture.deinit();

    try fixture.expectHover(5, 32, badge, "never matches");
}

fn hoverOnFunctionWithBodyShowsNoBadge() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\is_email : Str -> Bool
        \\
        \\shout : Str -> Str
        \\shout = |text| Str.with_ascii_uppercased(text)
        \\
        \\process_string : Str -> Str
        \\process_string = |text| shout(text)
        \\
    , "hover_intrinsic_none.roc", &.{});
    defer fixture.deinit();

    try fixture.expectHover(5, 1, "Str -> Str", badge);
    try fixture.expectHover(8, 26, "Str -> Str", badge);
}

const text_source =
    \\Text :: {}.{
    \\    is_email : Str -> Bool
    \\}
    \\
;
