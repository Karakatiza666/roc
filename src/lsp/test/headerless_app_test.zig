//! A headerless app, and an app header that names no platform, run on the
//! default Echo platform. The language server checks them the way `roc check`
//! does: the platform's requirements apply to `main!`, the checks after type
//! checking run, and the wiring that staging adds is not part of the
//! document.

const std = @import("std");
const lsp = @import("lsp");
const SyntaxChecker = lsp.syntax.SyntaxChecker;
const uri_util = lsp.uri;
const integration_spec = @import("integration_spec.zig");
const test_env = @import("integration_env.zig");

/// Specs for documents that run on the default platform.
pub const specs = [_]integration_spec.Spec{
    .{ .name = "headerless app: main! must have the platform's type", .run = mainMustHavePlatformType },
    .{ .name = "headerless app: hover on main!'s argument shows the platform's type", .run = hoverOnMainArgumentShowsPlatformType },
    .{ .name = "headerless app: a call to an intrinsic from main! exists only in reified code", .run = intrinsicCallExistsOnlyInReifiedCode },
    .{ .name = "headerless app: a refusal located in an imported module is published", .run = refusalInImportedModuleIsPublished },
    .{ .name = "headerless app: document symbols list no staging wiring", .run = documentSymbolsListNoWiring },
    .{ .name = "platformless app: a missing main! is reported", .run = platformlessAppReportsMissingMain },
    .{ .name = "headerless app: a sibling module's diagnostic is published at the sibling's file", .run = siblingDiagnosticAtSiblingFile },
    .{ .name = "headerless app: goto definition on a file import goes to the imported file", .run = definitionOnFileImportGoesToFile },
    .{ .name = "headerless app: goto definition and references across a sibling use the files' URIs", .run = definitionAndReferencesAcrossSibling },
};

/// A file written next to the document before it is checked.
const Sibling = struct {
    name: []const u8,
    source: []const u8,
};

/// One checked document and the diagnostics its check published.
const Fixture = struct {
    tmp: test_env.TmpDir,
    source: []const u8,
    file_uri: []u8,
    checker: SyntaxChecker,
    publish_sets: []lsp.diagnostics.PublishDiagnostics,

    fn init(fixture: *Fixture, source: []const u8, file_name: []const u8, siblings: []const Sibling) integration_spec.SpecError!void {
        const allocator = test_env.allocator;
        fixture.tmp = test_env.tmpDir(.{});
        errdefer fixture.tmp.cleanup();

        for (siblings) |sibling| {
            try fixture.tmp.dir.writeFile(test_env.io, .{ .sub_path = sibling.name, .data = sibling.source });
        }

        fixture.source = source;
        try fixture.tmp.dir.writeFile(test_env.io, .{ .sub_path = file_name, .data = source });
        const file_path = try fixture.tmp.dir.realPathFileAlloc(test_env.io, file_name, allocator);
        defer allocator.free(file_path);
        fixture.file_uri = try uri_util.pathToUri(allocator, file_path);
        errdefer allocator.free(fixture.file_uri);

        fixture.checker = SyntaxChecker.init(allocator, test_env.io, .{}, null);
        errdefer fixture.checker.deinit();
        test_env.configureChecker(&fixture.checker, std.fs.path.dirname(file_path) orelse file_path);

        fixture.publish_sets = try fixture.checker.check(fixture.file_uri, source, null, null);
    }

    fn deinit(fixture: *Fixture) void {
        const allocator = test_env.allocator;
        for (fixture.publish_sets) |*set| set.deinit(allocator);
        allocator.free(fixture.publish_sets);
        fixture.checker.deinit();
        allocator.free(fixture.file_uri);
        fixture.tmp.cleanup();
    }

    /// The document must have a diagnostic whose message contains `needle`
    /// and that starts on `line`.
    fn expectDiagnostic(fixture: *Fixture, needle: []const u8, line: u32) integration_spec.SpecError!void {
        for (fixture.publish_sets) |set| {
            if (!std.mem.eql(u8, set.uri, fixture.file_uri)) continue;
            for (set.diagnostics) |diagnostic| {
                if (std.mem.find(u8, diagnostic.message, needle) != null and diagnostic.range.start.line == line) return;
            }
        }
        std.debug.print("\nno diagnostic containing \"{s}\" on line {d}; published:\n", .{ needle, line });
        fixture.printDiagnostics();
        return error.TestUnexpectedResult;
    }

    /// The URI of the file `name` beside the document. Caller owns it.
    fn siblingUri(fixture: *Fixture, name: []const u8) integration_spec.SpecError![]u8 {
        const allocator = test_env.allocator;
        const path = try fixture.tmp.dir.realPathFileAlloc(test_env.io, name, allocator);
        defer allocator.free(path);
        return uri_util.pathToUri(allocator, path);
    }

    /// Goto definition at `line`:`character` must go to `expected_uri`.
    fn expectDefinitionUri(fixture: *Fixture, line: u32, character: u32, expected_uri: []const u8) integration_spec.SpecError!void {
        var result = try fixture.checker.getDefinitionAtPosition(fixture.file_uri, fixture.source, line, character) orelse {
            std.debug.print("\ngoto definition returned null at {d}:{d}\n", .{ line, character });
            return error.TestUnexpectedResult;
        };
        defer result.deinit(test_env.allocator);
        if (!std.mem.eql(u8, result.uri, expected_uri)) {
            std.debug.print("\ngoto definition at {d}:{d} went to {s}, expected {s}\n", .{ line, character, result.uri, expected_uri });
            return error.TestUnexpectedResult;
        }
    }

    fn printDiagnostics(fixture: *Fixture) void {
        for (fixture.publish_sets) |set| {
            for (set.diagnostics) |diagnostic| {
                std.debug.print("{s} {d}:{d}\n{s}\n", .{ set.uri, diagnostic.range.start.line, diagnostic.range.start.character, diagnostic.message });
            }
        }
    }
};

fn mainMustHavePlatformType() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\main! = |_args| 42
        \\
    , "main.roc", &.{});
    defer fixture.deinit();

    try fixture.expectDiagnostic("Try(_a, [Exit(I8)])", 0);
}

fn hoverOnMainArgumentShowsPlatformType() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\main! = |args| {
        \\    echo!(args.len().to_str())
        \\    Ok({})
        \\}
        \\
    , "main.roc", &.{});
    defer fixture.deinit();

    const result = try fixture.checker.getTypeAtPosition(fixture.file_uri, fixture.source, 1, 11) orelse {
        std.debug.print("\nhover returned null\n", .{});
        return error.TestUnexpectedResult;
    };
    defer test_env.allocator.free(result.type_str);
    if (std.mem.find(u8, result.type_str, "List(Str)") == null) {
        std.debug.print("\nhover was:\n{s}\n", .{result.type_str});
        return error.TestUnexpectedResult;
    }
    const range = result.range orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(u32, 1), range.start_line);
    try std.testing.expectEqual(@as(u32, 10), range.start_col);
}

fn intrinsicCallExistsOnlyInReifiedCode() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\secret : F64 -> F64
        \\
        \\main! = |_args| {
        \\    echo!(secret(1.0).to_str())
        \\    Ok({})
        \\}
        \\
    , "main.roc", &.{});
    defer fixture.deinit();

    try fixture.expectDiagnostic("reaches an intrinsic", 3);
}

const refusing_translator_source =
    \\Tr :: {}.{
    \\    stop : Code(f) -> Str
    \\    stop = |code| {
    \\        rows = code.graph().rows()
    \\        match rows.last() {
    \\            Ok(row) => code.refuse_at({ row: row.id, node: 0 }, "the last row is refused")
    \\            Err(_) => "none"
    \\        }
    \\    }
    \\}
    \\
;

const helper_source =
    \\Helper :: {}.{
    \\    h : F64 -> F64
    \\    h = |x| x.sqrt() * 2.0
    \\}
    \\
;

fn refusalInImportedModuleIsPublished() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\import Tr
        \\import Helper
        \\
        \\f : F64 -> F64
        \\f = |x| Helper.h(x) + 1.0
        \\
        \\expr = Tr.stop(f)
        \\
        \\main! = |_args| {
        \\    echo!(expr)
        \\    Ok({})
        \\}
        \\
    , "main.roc", &.{
        .{ .name = "Tr.roc", .source = refusing_translator_source },
        .{ .name = "Helper.roc", .source = helper_source },
    });
    defer fixture.deinit();

    try fixture.expectDiagnostic("A translator refused code", 4);
}

fn documentSymbolsListNoWiring() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\greeting = "hi"
        \\
        \\main! = |_args| {
        \\    echo!(greeting)
        \\    Ok({})
        \\}
        \\
    , "main.roc", &.{});
    defer fixture.deinit();

    const allocator = test_env.allocator;
    const symbols = try fixture.checker.getDocumentSymbols(allocator, fixture.file_uri, fixture.source);
    defer {
        for (symbols) |symbol| allocator.free(symbol.name);
        allocator.free(symbols);
    }

    var saw_main = false;
    var saw_greeting = false;
    for (symbols) |symbol| {
        if (std.mem.eql(u8, symbol.name, "echo!")) {
            std.debug.print("\ndocument symbols list the staging's echo! at {d}:{d}\n", .{ symbol.location.range.start.line, symbol.location.range.start.character });
            return error.TestUnexpectedResult;
        }
        if (std.mem.eql(u8, symbol.name, "main!")) {
            saw_main = true;
            try std.testing.expectEqual(@as(u32, 2), symbol.location.range.start.line);
        }
        if (std.mem.eql(u8, symbol.name, "greeting")) {
            saw_greeting = true;
            try std.testing.expectEqual(@as(u32, 0), symbol.location.range.start.line);
        }
    }
    try std.testing.expect(saw_main);
    try std.testing.expect(saw_greeting);
}

fn platformlessAppReportsMissingMain() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\app [main!] {}
        \\
        \\x = 1
        \\
    , "main.roc", &.{});
    defer fixture.deinit();

    var found = false;
    for (fixture.publish_sets) |set| {
        if (!std.mem.eql(u8, set.uri, fixture.file_uri)) continue;
        for (set.diagnostics) |diagnostic| {
            if (std.mem.find(u8, diagnostic.message, "main!") != null) found = true;
        }
    }
    if (!found) {
        std.debug.print("\nno diagnostic names main!; published:\n", .{});
        fixture.printDiagnostics();
        return error.TestUnexpectedResult;
    }
}

/// A sibling's own warning is published at the sibling's file, not at the
/// copy of its path under the scratch directory that holds the staged app.
fn siblingDiagnosticAtSiblingFile() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\import Bool as Flag
        \\
        \\main! = |_args| {
        \\    echo!("hi")
        \\    Ok({})
        \\}
        \\
    , "main.roc", &.{.{ .name = "Bool.roc", .source =
        \\Bool :: { n : I64 }.{
        \\    not : Bool -> Bool
        \\    not = |Bool.(b)| Bool.{ n: 1 - b.n }
        \\
        \\    level : Bool -> I64
        \\    level = |Bool.(b)| b.n
        \\}
        \\
    }});
    defer fixture.deinit();

    const sibling_uri = try fixture.siblingUri("Bool.roc");
    defer test_env.allocator.free(sibling_uri);
    for (fixture.publish_sets) |set| {
        if (!std.mem.eql(u8, set.uri, sibling_uri)) continue;
        for (set.diagnostics) |diagnostic| {
            if (std.mem.find(u8, diagnostic.message, "shadows a builtin type") != null and diagnostic.range.start.line == 0) return;
        }
    }
    std.debug.print("\nno shadowing warning at {s}; published:\n", .{sibling_uri});
    fixture.printDiagnostics();
    return error.TestUnexpectedResult;
}

/// A file import names a file beside the document, so goto definition on it
/// goes to that file.
fn definitionOnFileImportGoesToFile() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\import "greeting.txt" as greeting : Str
        \\
        \\main! = |_args| {
        \\    echo!(greeting)
        \\    Ok({})
        \\}
        \\
    , "main.roc", &.{.{ .name = "greeting.txt", .source = "hello\n" }});
    defer fixture.deinit();

    const file_uri = try fixture.siblingUri("greeting.txt");
    defer test_env.allocator.free(file_uri);
    try fixture.expectDefinitionUri(0, 10, file_uri);
}

/// Goto definition on a sibling's value goes to the sibling's file, and the
/// references of an imported name are places in the document.
fn definitionAndReferencesAcrossSibling() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\import Helper
        \\
        \\twice = |x| Helper.h(x) + Helper.h(x)
        \\
        \\main! = |_args| {
        \\    echo!(twice(1.0).to_str())
        \\    Ok({})
        \\}
        \\
    , "main.roc", &.{.{ .name = "Helper.roc", .source = helper_source }});
    defer fixture.deinit();

    const helper_uri = try fixture.siblingUri("Helper.roc");
    defer test_env.allocator.free(helper_uri);
    try fixture.expectDefinitionUri(2, 19, helper_uri);
    try fixture.expectDefinitionUri(5, 11, fixture.file_uri);

    const references = try fixture.checker.getReferencesAtPosition(fixture.file_uri, fixture.source, 2, 0, true) orelse {
        std.debug.print("\nreferences returned null\n", .{});
        return error.TestUnexpectedResult;
    };
    defer references.deinit(test_env.allocator);
    try std.testing.expectEqual(@as(usize, 2), references.regions.len);
    try std.testing.expectEqual(@as(u32, 2), references.regions[0].start_line);
    try std.testing.expectEqual(@as(u32, 5), references.regions[1].start_line);
}
