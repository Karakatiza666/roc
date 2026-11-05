//! Completion after `Module.` and after `value.` for types of other modules.
//!
//! `Foo.` lists the members of the sibling module that the import names.
//! `value.` lists the backing fields of a `::` opaque type only where the
//! checker allows field access on it, which is the type's own module. It
//! lists the methods of a type from another module, and only associated
//! items whose first parameter can take the receiver. A field and a method
//! may share a name, since `value.name` reads the field and `value.name()`
//! calls the method, so both are offered.

const std = @import("std");
const integration_spec = @import("integration_spec.zig");
const test_env = @import("integration_env.zig");
const fixture_mod = @import("issue_12292_test.zig");
const Fixture = fixture_mod.Fixture;
const SyntaxChecker = @import("lsp").syntax.SyntaxChecker;

/// Completion specs for module members, opaque fields and imported methods.
pub const specs = [_]integration_spec.Spec{
    .{ .name = "completion: members of a sibling module after its name and a dot", .run = siblingModuleMembersAfterDot },
    .{ .name = "completion: members of an aliased sibling module after the alias and a dot", .run = aliasedSiblingModuleMembersAfterDot },
    .{ .name = "completion: opaque fields are hidden outside the defining module", .run = opaqueFieldsHiddenOutsideModule },
    .{ .name = "completion: opaque fields are offered inside the defining module", .run = opaqueFieldsOfferedInsideModule },
    .{ .name = "completion: methods of an imported type are offered on a value", .run = importedMethodsOfferedOnValue },
    .{ .name = "completion: a Code value offers its methods and no backing fields", .run = codeValueOffersMethodsOnly },
    .{ .name = "completion: a field and a method of one name are both offered", .run = fieldAndMethodOfOneName },
    .{ .name = "completion: record fields are offered in name order", .run = recordFieldsInNameOrder },
    .{ .name = "completion: module members are offered in a file with a type error", .run = moduleMembersWithTypeError },
    .{ .name = "completion: methods are offered on a value in a file with a type error", .run = valueMethodsWithTypeError },
};

const method_kind: u32 = 2;
const field_kind: u32 = 5;

const foo_source =
    \\Foo :: { secret : I64 }.{
    \\    make : I64 -> Foo
    \\    make = |n| Foo.({ secret: n })
    \\
    \\    get : Foo -> I64
    \\    get = |Foo.(inner)| inner.secret
    \\
    \\    zero : () -> Foo
    \\    zero = || Foo.({ secret: 0 })
    \\}
    \\
;

const main_template =
    \\app [process_string] {{ pf: platform "{s}" }}
    \\
    \\import Foo
    \\
    \\Bar :: {{ hidden : I64 }}.{{
    \\    make_bar : I64 -> Bar
    \\    make_bar = |n| Bar.({{ hidden: n }})
    \\}}
    \\
    \\describe : Code(f) -> Str
    \\describe = |code| code.version().to_str()
    \\
    \\process_string : Str -> Str
    \\process_string = |text| {{
    \\    f = Foo.make(1)
    \\    b = Bar.make_bar(2)
    \\    Str.concat(text, Str.concat(f.get().to_str(), b.hidden.to_str()))
    \\}}
    \\
;

const aliased_template =
    \\app [process_string] {{ pf: platform "{s}" }}
    \\
    \\import Foo as F
    \\
    \\process_string : Str -> Str
    \\process_string = |text| {{
    \\    f = F.make(1)
    \\    Str.concat(text, f.get().to_str())
    \\}}
    \\
;

const siblings = [_]fixture_mod.Sibling{.{ .name = "Foo.roc", .source = foo_source }};

/// The labels and kinds completion offers when `complete` in the checked
/// source is replaced by `incomplete`, with the cursor at its end.
pub fn completeAt(fixture: *Fixture, complete: []const u8, incomplete: []const u8, labels: []const []const u8, absent: []const []const u8, kinds: []const struct { []const u8, u32 }) integration_spec.SpecError!void {
    const allocator = test_env.allocator;
    const edited = try std.mem.replaceOwned(u8, allocator, fixture.source, complete, incomplete);
    defer allocator.free(edited);

    const start = std.mem.find(u8, edited, incomplete) orelse return error.TestUnexpectedResult;
    const cursor = start + incomplete.len;
    var line: u32 = 0;
    var line_start: usize = 0;
    for (edited[0..cursor], 0..) |byte, index| {
        if (byte == '\n') {
            line += 1;
            line_start = index + 1;
        }
    }
    const character: u32 = @intCast(cursor - line_start);

    const result = try fixture.checker.getCompletionsAtPosition(fixture.file_uri, edited, line, character) orelse {
        std.debug.print("\ncompletion returned null after `{s}`\n", .{incomplete});
        return error.TestUnexpectedResult;
    };
    defer result.deinit();

    var failed = false;
    for (labels) |label| {
        if (findItem(result.items, label) == null) {
            std.debug.print("\ncompletion after `{s}` misses `{s}`\n", .{ incomplete, label });
            failed = true;
        }
    }
    for (absent) |label| {
        if (findItem(result.items, label) != null) {
            std.debug.print("\ncompletion after `{s}` offers `{s}`\n", .{ incomplete, label });
            failed = true;
        }
    }
    for (kinds) |expected| {
        const kind = if (findItem(result.items, expected[0])) |item| item.kind else continue;
        if (kind != expected[1]) {
            std.debug.print("\ncompletion after `{s}` offers `{s}` with kind {any}, expected {d}\n", .{ incomplete, expected[0], kind, expected[1] });
            failed = true;
        }
    }
    if (failed) {
        std.debug.print("items:", .{});
        for (result.items) |item| std.debug.print(" {s}", .{item.label});
        std.debug.print("\n", .{});
        return error.TestUnexpectedResult;
    }
}

fn findItem(items: anytype, label: []const u8) ?@TypeOf(items[0]) {
    for (items) |item| {
        if (std.mem.eql(u8, item.label, label)) return item;
    }
    return null;
}

fn siblingModuleMembersAfterDot() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(main_template, "completion_sibling_members.roc", &siblings);
    defer fixture.deinit();

    try completeAt(&fixture, "f = Foo.make(1)", "f = Foo.", &.{ "make", "get", "zero" }, &.{}, &.{});
}

fn aliasedSiblingModuleMembersAfterDot() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(aliased_template, "completion_aliased_members.roc", &siblings);
    defer fixture.deinit();

    try completeAt(&fixture, "f = F.make(1)", "f = F.", &.{ "make", "get", "zero" }, &.{}, &.{});
}

fn opaqueFieldsHiddenOutsideModule() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(main_template, "completion_opaque_hidden.roc", &siblings);
    defer fixture.deinit();

    try completeAt(&fixture, "f.get().to_str()", "f.", &.{}, &.{"secret"}, &.{});
}

fn opaqueFieldsOfferedInsideModule() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(main_template, "completion_opaque_inside.roc", &siblings);
    defer fixture.deinit();

    try completeAt(&fixture, "b.hidden.to_str()", "b.", &.{"hidden"}, &.{}, &.{.{ "hidden", field_kind }});
}

fn importedMethodsOfferedOnValue() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(main_template, "completion_imported_methods.roc", &siblings);
    defer fixture.deinit();

    // `make` takes an `I64` and `zero` takes nothing, so `f.make()` and
    // `f.zero()` do not check.
    try completeAt(&fixture, "f.get().to_str()", "f.", &.{"get"}, &.{ "make", "zero" }, &.{.{ "get", method_kind }});
}

fn codeValueOffersMethodsOnly() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(main_template, "completion_code_methods.roc", &siblings);
    defer fixture.deinit();

    try completeAt(
        &fixture,
        "code.version().to_str()",
        "code.",
        &.{ "graph", "version", "refuse_at" },
        &.{ "site", "proxy", "type_id", "ty_of" },
        &.{ .{ "graph", method_kind }, .{ "version", method_kind } },
    );
}

const person_template =
    \\app [process_string] {{ pf: platform "{s}" }}
    \\
    \\Person := {{ name : Str, age : U8 }}.{{
    \\    name : Person -> Str
    \\    name = |person| Str.concat("Dr. ", person.name)
    \\}}
    \\
    \\process_string : Str -> Str
    \\process_string = |text| {{
    \\    p : Person
    \\    p = {{ name: text, age: 3 }}
    \\    Str.concat(p.name, p.name())
    \\}}
    \\
;

fn fieldAndMethodOfOneName() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(person_template, "completion_field_and_method.roc", &.{});
    defer fixture.deinit();

    const edited = try std.mem.replaceOwned(u8, test_env.allocator, fixture.source, "Str.concat(p.name, p.name())", "Str.concat(p.");
    defer test_env.allocator.free(edited);
    const cursor = (std.mem.find(u8, edited, "Str.concat(p.") orelse return error.TestUnexpectedResult) + "Str.concat(p.".len;
    const line: u32 = @intCast(std.mem.count(u8, edited[0..cursor], "\n"));
    const line_start = (std.mem.findScalarLast(u8, edited[0..cursor], '\n') orelse return error.TestUnexpectedResult) + 1;
    const character: u32 = @intCast(cursor - line_start);

    const result = try fixture.checker.getCompletionsAtPosition(fixture.file_uri, edited, line, character) orelse return error.TestUnexpectedResult;
    defer result.deinit();

    var name_field = false;
    var name_method = false;
    var age_field = false;
    for (result.items) |item| {
        if (std.mem.eql(u8, item.label, "name") and item.kind == field_kind) name_field = true;
        if (std.mem.eql(u8, item.label, "name") and item.kind == method_kind) name_method = true;
        if (std.mem.eql(u8, item.label, "age") and item.kind == field_kind) age_field = true;
    }
    if (!(name_field and name_method and age_field)) {
        std.debug.print("\nfield name: {}, method name: {}, field age: {}; items:", .{ name_field, name_method, age_field });
        for (result.items) |item| std.debug.print(" {s}({any})", .{ item.label, item.kind });
        std.debug.print("\n", .{});
        return error.TestUnexpectedResult;
    }
}

const type_error_tail =
    \\
    \\bad : Str
    \\bad = 5
    \\
;

/// Completion of `incomplete` in the checked source plus a type error, asked
/// of a checker that has not built the file before.
fn completeWithTypeError(fixture: *Fixture, incomplete: []const u8, labels: []const []const u8) integration_spec.SpecError!void {
    const allocator = test_env.allocator;
    const with_error = try std.mem.concat(allocator, u8, &.{ fixture.source, type_error_tail });
    defer allocator.free(with_error);
    const edited = with_error;
    const cursor = (std.mem.find(u8, edited, incomplete) orelse return error.TestUnexpectedResult) + incomplete.len;
    const line: u32 = @intCast(std.mem.count(u8, edited[0..cursor], "\n"));
    const line_start = (std.mem.findScalarLast(u8, edited[0..cursor], '\n') orelse return error.TestUnexpectedResult) + 1;
    const character: u32 = @intCast(cursor - line_start);

    var checker = SyntaxChecker.init(allocator, test_env.io, .{}, null);
    defer checker.deinit();
    checker.cache_config.cache_dir = std.fs.path.dirname(fixture.file_path) orelse fixture.file_path;

    const result = try checker.getCompletionsAtPosition(fixture.file_uri, edited, line, character) orelse return error.TestUnexpectedResult;
    defer result.deinit();
    var failed = false;
    for (labels) |label| {
        if (findItem(result.items, label) == null) {
            std.debug.print("\ncompletion after `{s}` misses `{s}`\n", .{ incomplete, label });
            failed = true;
        }
    }
    if (failed) return error.TestUnexpectedResult;
}

fn moduleMembersWithTypeError() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(main_template, "completion_module_type_error.roc", &siblings);
    defer fixture.deinit();

    try completeWithTypeError(&fixture, "f = Foo.", &.{ "make", "get", "zero" });
}

fn valueMethodsWithTypeError() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(main_template, "completion_value_type_error.roc", &siblings);
    defer fixture.deinit();

    try completeWithTypeError(&fixture, "Foo.make(1)\n    b = Bar.make_bar(2)\n    Str.concat(text, Str.concat(f.", &.{"get"});
}

const unsorted_record_template =
    \\app [process_string] {{ pf: platform "{s}" }}
    \\
    \\Product : {{ zeta : I64, mid : Str, alpha : Dec }}
    \\
    \\process_string : Str -> Str
    \\process_string = |text| {{
    \\    p : Product
    \\    p = {{ zeta: 1, mid: text, alpha: 2.0 }}
    \\    Str.concat(p.mid, p.mid)
    \\}}
    \\
;

/// Fields come in name order, whatever order the names were first written.
fn recordFieldsInNameOrder() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(unsorted_record_template, "completion_field_order.roc", &.{});
    defer fixture.deinit();

    const edited = try std.mem.replaceOwned(u8, test_env.allocator, fixture.source, "Str.concat(p.mid, p.mid)", "Str.concat(p.");
    defer test_env.allocator.free(edited);
    const cursor = (std.mem.find(u8, edited, "Str.concat(p.") orelse return error.TestUnexpectedResult) + "Str.concat(p.".len;
    const line: u32 = @intCast(std.mem.count(u8, edited[0..cursor], "\n"));
    const line_start = (std.mem.findScalarLast(u8, edited[0..cursor], '\n') orelse return error.TestUnexpectedResult) + 1;
    const character: u32 = @intCast(cursor - line_start);

    const result = try fixture.checker.getCompletionsAtPosition(fixture.file_uri, edited, line, character) orelse return error.TestUnexpectedResult;
    defer result.deinit();

    const expected = [_][]const u8{ "alpha", "mid", "zeta" };
    var found: usize = 0;
    for (result.items) |item| {
        if (item.kind != field_kind) continue;
        if (found >= expected.len or !std.mem.eql(u8, item.label, expected[found])) {
            std.debug.print("\nfield `{s}` is out of order at position {d}\n", .{ item.label, found });
            return error.TestUnexpectedResult;
        }
        found += 1;
    }
    try std.testing.expectEqual(expected.len, found);
}
