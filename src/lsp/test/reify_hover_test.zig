//! Hover on a name at a `Code` position, or on the argument of `Code.prim`,
//! shows the type and doc comment of the definition that the name refers to.
//! It never shows the `Code` type, its doc, or the parameter type of
//! `Code.prim`.

const integration_spec = @import("integration_spec.zig");
const fixture_mod = @import("issue_12292_test.zig");
const Fixture = fixture_mod.Fixture;

/// Hover specs for names at reifying sites.
pub const specs = [_]integration_spec.Spec{
    .{ .name = "reify hover: a function with a doc comment at a Code position", .run = hoverOnDocumentedFunctionAtCodePosition },
    .{ .name = "reify hover: a function without a doc comment at a Code position", .run = hoverOnUndocumentedFunctionAtCodePosition },
    .{ .name = "reify hover: a qualified function of another module at a Code position", .run = hoverOnQualifiedFunctionAtCodePosition },
    .{ .name = "reify hover: the argument of Code.prim", .run = hoverOnCodePrimArgument },
};

/// A phrase of the builtin doc comment of `Code`.
const code_doc = "cannot be constructed by hand";

fn hoverOnDocumentedFunctionAtCodePosition() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\## Doubles a number.
        \\double : F64 -> F64
        \\double = |x| x * 2.0
        \\
        \\describe : Code(f) -> Str
        \\describe = |_c| "x"
        \\
        \\process_string : Str -> Str
        \\process_string = |text| Str.concat(text, describe(double))
        \\
    , "hover_reify_documented.roc", &.{});
    defer fixture.deinit();

    // The use at the Code position shows what hover on the definition shows.
    try fixture.expectHover(4, 2, "F64 -> F64", "Code(");
    try fixture.expectHover(10, 54, "F64 -> F64", "Code(");
    try fixture.expectHover(10, 54, "Doubles a number.", code_doc);
}

fn hoverOnUndocumentedFunctionAtCodePosition() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\triple : F64 -> F64
        \\triple = |x| x * 3.0
        \\
        \\describe : Code(f) -> Str
        \\describe = |_c| "x"
        \\
        \\process_string : Str -> Str
        \\process_string = |text| Str.concat(text, describe(triple))
        \\
    , "hover_reify_undocumented.roc", &.{});
    defer fixture.deinit();

    try fixture.expectHover(9, 54, "F64 -> F64", "Code(");
    try fixture.expectHover(9, 54, "```roc\nF64 -> F64\n```", code_doc);
}

fn hoverOnQualifiedFunctionAtCodePosition() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\import Halving
        \\
        \\describe : Code(f) -> Str
        \\describe = |_c| "x"
        \\
        \\process_string : Str -> Str
        \\process_string = |text| Str.concat(text, describe(Halving.halve))
        \\
    , "hover_reify_qualified.roc", &.{.{ .name = "Halving.roc", .source = halving_source }});
    defer fixture.deinit();

    // On the function name and on the module qualifier.
    try fixture.expectHover(8, 62, "F64 -> F64", "Code(");
    try fixture.expectHover(8, 62, "Halves a number.", code_doc);
    try fixture.expectHover(8, 54, "F64 -> F64", "Code(");
}

fn hoverOnCodePrimArgument() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\import Halving
        \\
        \\## Doubles a number.
        \\double : F64 -> F64
        \\double = |x| x * 2.0
        \\
        \\prims : List(Code.PrimId)
        \\prims = [Code.prim(Halving.halve), Code.prim(double)]
        \\
        \\process_string : Str -> Str
        \\process_string = |text| Str.concat(text, prims.len().to_str())
        \\
    , "hover_reify_prim.roc", &.{.{ .name = "Halving.roc", .source = halving_source }});
    defer fixture.deinit();

    try fixture.expectHover(9, 29, "F64 -> F64", "_f");
    try fixture.expectHover(9, 29, "Halves a number.", "PrimId");
    try fixture.expectHover(9, 21, "F64 -> F64", "_f");
    try fixture.expectHover(9, 47, "F64 -> F64", "_f");
    try fixture.expectHover(9, 47, "Doubles a number.", "PrimId");
}

const halving_source =
    \\Halving :: {}.{
    \\    ## Halves a number.
    \\    halve : F64 -> F64
    \\    halve = |x| x / 2.0
    \\}
    \\
;
