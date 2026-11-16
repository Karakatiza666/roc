//! Goto definition on a type name anywhere hover finds one: in a where
//! clause, in a type declaration's header, and in an annotation on a
//! statement nested in any expression.

const integration_spec = @import("integration_spec.zig");
const fixture_mod = @import("issue_12292_test.zig");
const Fixture = fixture_mod.Fixture;

/// Goto definition specs for names in annotations.
pub const specs = [_]integration_spec.Spec{
    .{ .name = "annotation definition: a type in a where clause goes to its declaration", .run = typeInWhereClause },
    .{ .name = "annotation definition: the name in a type declaration's header goes to that declaration", .run = nameInTypeHeader },
    .{ .name = "annotation definition: a type in an annotation in a block inside a list goes to its declaration", .run = typeInBlockInsideList },
};

fn typeInWhereClause() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\## A point on the plane.
        \\Point : {{ x : F64, y : F64 }}
        \\
        \\measure : a -> F64 where [a.at : a -> Point]
        \\measure = |x| x.at().x
        \\
        \\process_string : Str -> Str
        \\process_string = |text| text
        \\
    , "definition_where_type.roc", &.{});
    defer fixture.deinit();

    try fixture.expectDefinition(5, 38, "definition_where_type.roc", 3);
}

fn nameInTypeHeader() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\## A point on the plane.
        \\Point : {{ x : F64, y : F64 }}
        \\
        \\## Wraps a label.
        \\Holder := {{ label : Str }}
        \\
        \\process_string : Str -> Str
        \\process_string = |text| text
        \\
    , "definition_type_header.roc", &.{});
    defer fixture.deinit();

    try fixture.expectDefinition(3, 0, "definition_type_header.roc", 3);
    try fixture.expectDefinition(6, 0, "definition_type_header.roc", 6);
}

fn typeInBlockInsideList() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\## A point on the plane.
        \\Point : {{ x : F64, y : F64 }}
        \\
        \\process_string : Str -> Str
        \\process_string = |text| {{
        \\    points = [{{
        \\        origin : Point
        \\        origin = {{ x: 0.0, y: 0.0 }}
        \\        origin
        \\    }}]
        \\    Str.concat(text, List.len(points).to_str())
        \\}}
        \\
    , "definition_nested_list.roc", &.{});
    defer fixture.deinit();

    // Hover already reaches this annotation; definition must too.
    try fixture.expectHover(8, 17, "A point on the plane.", "never matches");
    try fixture.expectDefinition(8, 17, "definition_nested_list.roc", 3);
}
