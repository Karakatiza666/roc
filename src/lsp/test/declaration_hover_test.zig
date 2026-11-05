//! Hover on the name of a type annotation line, and on names inside type
//! alias and nominal declarations.

const integration_spec = @import("integration_spec.zig");
const fixture_mod = @import("issue_12292_test.zig");
const Fixture = fixture_mod.Fixture;

/// Hover specs for declaration names.
pub const specs = [_]integration_spec.Spec{
    .{ .name = "declaration hover: the name on an annotation line shows the type and doc of the definition", .run = hoverOnAnnotationName },
    .{ .name = "declaration hover: the name of an alias declaration shows the declaration and its doc", .run = hoverOnAliasName },
    .{ .name = "declaration hover: a type used in an alias body shows that type and its doc", .run = hoverOnTypeInAliasBody },
    .{ .name = "declaration hover: a type in an ordinary annotation shows its declaration and doc", .run = hoverOnTypeInOrdinaryAnnotation },
    .{ .name = "declaration hover: a nominal name and an imported type in its body show their declarations", .run = hoverOnTypesOfOtherDeclarations },
    .{ .name = "declaration hover: a type in an annotation inside a block shows its declaration and doc", .run = hoverOnTypeInNestedAnnotation },
    .{ .name = "declaration hover: a record field label in an alias shows the field and its type", .run = hoverOnFieldLabelInAlias },
    .{ .name = "declaration hover: a record field label in a nominal declaration shows the field and its type", .run = hoverOnFieldLabelInNominal },
    .{ .name = "declaration hover: a method name in a where clause shows the required method", .run = hoverOnWhereClauseMethod },
    .{ .name = "method hover: a method of an imported type shows the method and its name range", .run = hoverOnImportedMethodCall },
    .{ .name = "method hover: a method of a local type shows the method and its name range", .run = hoverOnLocalMethodCall },
    .{ .name = "method hover: a builtin method shows the method and its name range", .run = hoverOnBuiltinMethodCall },
};

fn hoverOnAnnotationName() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\## Doubles a number.
        \\double : F64 -> F64
        \\double = |x| x * 2.0
        \\
        \\process_string : Str -> Str
        \\process_string = |text| text
        \\
    , "hover_annotation_name.roc", &.{});
    defer fixture.deinit();

    try fixture.expectHover(3, 2, "F64 -> F64", "never matches");
    try fixture.expectHover(3, 2, "Doubles a number.", "never matches");
    try fixture.expectHover(6, 5, "Str -> Str", "never matches");
}

const alias_source =
    \\app [process_string] {{ pf: platform "{s}" }}
    \\
    \\## A point on the plane.
    \\Point : {{ x : F64, y : F64 }}
    \\
    \\## A stage of work.
    \\Stage : {{ at : Point, label : Str }}
    \\
    \\process_string : Str -> Str
    \\process_string = |text| text
    \\
;

fn hoverOnAliasName() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(alias_source, "hover_alias_name.roc", &.{});
    defer fixture.deinit();

    try fixture.expectHover(6, 2, "A stage of work.", "never matches");
    try fixture.expectHover(6, 2, "Stage", "never matches");
}

fn hoverOnTypeInAliasBody() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(alias_source, "hover_alias_body.roc", &.{});
    defer fixture.deinit();

    // `Point` inside the body of `Stage`.
    try fixture.expectHover(6, 16, "A point on the plane.", "A stage of work.");
}

fn hoverOnTypesOfOtherDeclarations() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\import Shapes
        \\
        \\## Wraps a shape.
        \\Holder := {{ shape : Shapes }}
        \\
        \\process_string : Str -> Str
        \\process_string = |text| text
        \\
    , "hover_decl_other.roc", &.{.{ .name = "Shapes.roc", .source = shapes_source }});
    defer fixture.deinit();

    // The nominal's own name, and an imported type in its body.
    try fixture.expectHover(5, 2, "Wraps a shape.", "A shape.");
    try fixture.expectHover(5, 2, "Holder :=", "A shape.");
    try fixture.expectHover(5, 21, "A shape.", "Wraps a shape.");
    try fixture.expectHover(5, 21, "Shapes :=", "Wraps a shape.");
}

const shapes_source =
    \\## A shape.
    \\Shapes := [Circle, Square]
    \\
;

fn hoverOnTypeInOrdinaryAnnotation() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\## A point on the plane.
        \\Point : {{ x : F64, y : F64 }}
        \\
        \\shift : Point, F64 -> Point
        \\shift = |p, d| {{ x: p.x + d, y: p.y }}
        \\
        \\process_string : Str -> Str
        \\process_string = |text| text
        \\
    , "hover_type_in_annotation.roc", &.{});
    defer fixture.deinit();

    // Both uses of `Point` show the declaration, not the type of `shift`.
    try fixture.expectHover(5, 9, "A point on the plane.", "->");
    try fixture.expectHover(5, 9, "Point : {", "->");
    try fixture.expectHover(5, 27, "A point on the plane.", "->");
    // The annotation's own name keeps showing the type of the definition.
    try fixture.expectHover(5, 2, "Point, F64 -> Point", "A point on the plane.");
}

fn hoverOnTypeInNestedAnnotation() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\## A point on the plane.
        \\Point : {{ x : F64, y : F64 }}
        \\
        \\process_string : Str -> Str
        \\process_string = |text| {{
        \\    origin : Point
        \\    origin = {{ x: 0.0, y: 0.0 }}
        \\    Str.concat(text, F64.to_str(origin.x))
        \\}}
        \\
    , "hover_nested_annotation.roc", &.{});
    defer fixture.deinit();

    // `Point` in the annotation of a local binding.
    try fixture.expectHover(7, 14, "A point on the plane.", "never matches");
}

const counter_source =
    \\Counter :: { n : I64 }.{
    \\    ## Reads the count.
    \\    get : Counter -> I64
    \\    get = |Counter.({ n })| n
    \\
    \\    make : I64 -> Counter
    \\    make = |n| Counter.({ n: n })
    \\}
    \\
;

fn hoverOnImportedMethodCall() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\import Counter
        \\
        \\process_string : Str -> Str
        \\process_string = |_text| {{
        \\    c = Counter.make(1)
        \\    c.get().to_str()
        \\}}
        \\
    , "hover_imported_method.roc", &.{.{ .name = "Counter.roc", .source = counter_source }});
    defer fixture.deinit();

    // `get` shows the method, not the `I64` that the call returns.
    try fixture.expectHoverRange(7, 6, "Counter -> I64", "```roc\nI64\n", 6, 9);
    try fixture.expectHover(7, 6, "Reads the count.", "never matches");
}

fn hoverOnLocalMethodCall() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\Cell := {{ n : I64 }}.{{
        \\    ## Reads the box.
        \\    open : Cell -> I64
        \\    open = |Cell.({{ n }})| n
        \\}}
        \\
        \\process_string : Str -> Str
        \\process_string = |_text| {{
        \\    b = Cell.({{ n: 1 }})
        \\    b.open().to_str()
        \\}}
        \\
    , "hover_local_method.roc", &.{});
    defer fixture.deinit();

    try fixture.expectHoverRange(11, 6, "Cell -> I64", "```roc\nI64\n", 6, 10);
    try fixture.expectHover(11, 6, "Reads the box.", "never matches");
}

fn hoverOnBuiltinMethodCall() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\process_string : Str -> Str
        \\process_string = |_text| I64.abs(-5).to_str()
        \\
    , "hover_builtin_method.roc", &.{});
    defer fixture.deinit();

    // `to_str` takes an `I64` and gives a `Str`.
    try fixture.expectHoverRange(3, 39, "I64 -> Str", "```roc\nStr\n", 37, 43);
}

fn hoverOnFieldLabelInAlias() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\Shape : {{
        \\    ## The width.
        \\    width : F64,
        \\    label ?: Str,
        \\    area : F64 -> F64,
        \\}}
        \\
        \\process_string : Str -> Str
        \\process_string = |text| text
        \\
    , "hover_field_label_alias.roc", &.{});
    defer fixture.deinit();

    try fixture.expectHoverRange(4, 5, "width : F64", "never matches", 4, 9);
    try fixture.expectHover(4, 5, "The width.", "never matches");
    try fixture.expectHover(5, 5, "label ?: Str", "never matches");
    try fixture.expectHover(6, 6, "area : F64 -> F64", "never matches");
    // The type after the label still shows the type declaration or nothing, never the field.
    try fixture.expectHover(4, 14, "F64", "width :");
}

fn hoverOnFieldLabelInNominal() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\Person := {{ name : Str, greet : Str -> Str }}.{{
        \\    name : Person -> Str
        \\    name = |_p| "method"
        \\}}
        \\
        \\process_string : Str -> Str
        \\process_string = |text| text
        \\
    , "hover_field_label_nominal.roc", &.{});
    defer fixture.deinit();

    try fixture.expectHoverRange(2, 14, "name : Str", "Person -> Str", 12, 16);
    try fixture.expectHover(2, 26, "greet : Str -> Str", "never matches");
}

fn hoverOnWhereClauseMethod() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [process_string] {{ pf: platform "{s}" }}
        \\
        \\show : a -> Str where [a.render : a -> Str]
        \\show = |x| x.render()
        \\
        \\process_string : Str -> Str
        \\process_string = |text| text
        \\
    , "hover_where_method.roc", &.{});
    defer fixture.deinit();

    try fixture.expectHoverRange(2, 27, "a.render : a -> Str", "never matches", 25, 31);
}
