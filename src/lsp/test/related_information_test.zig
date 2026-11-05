//! Diagnostics name the other places a report names as `relatedInformation`,
//! from the report's explicit locations. A report whose primary place is in
//! another module's file is shown in the reporting module's file, at the
//! place that reaches it, and its related information names the other file.

const std = @import("std");
const lsp = @import("lsp");
const SyntaxChecker = lsp.syntax.SyntaxChecker;
const Diagnostics = lsp.diagnostics;
const uri_util = lsp.uri;
const integration_spec = @import("integration_spec.zig");
const test_env = @import("integration_env.zig");

/// Specs for the related information of published diagnostics.
pub const specs = [_]integration_spec.Spec{
    .{ .name = "related information: a refusal in an imported module is shown at the site that reaches it", .run = foreignRefusalIsShownAtItsSite },
    .{ .name = "related information: a duplicate record field names the first field", .run = duplicateRecordFieldNamesFirstField },
    .{ .name = "related information: a client that does not accept it gets none", .run = clientWithoutCapabilityGetsNone },
};

/// A file written next to the document before it is checked.
const Sibling = struct {
    name: []const u8,
    source: []const u8,
};

/// One checked document and the diagnostics its check published.
const Fixture = struct {
    tmp: test_env.TmpDir,
    file_uri: []u8,
    checker: SyntaxChecker,
    publish_sets: []Diagnostics.PublishDiagnostics,

    fn init(fixture: *Fixture, source: []const u8, siblings: []const Sibling, related_information: bool) integration_spec.SpecError!void {
        const allocator = test_env.allocator;
        fixture.tmp = test_env.tmpDir(.{});
        errdefer fixture.tmp.cleanup();

        for (siblings) |sibling| {
            try fixture.tmp.dir.writeFile(test_env.io, .{ .sub_path = sibling.name, .data = sibling.source });
        }

        try fixture.tmp.dir.writeFile(test_env.io, .{ .sub_path = "main.roc", .data = source });
        const file_path = try fixture.tmp.dir.realPathFileAlloc(test_env.io, "main.roc", allocator);
        defer allocator.free(file_path);
        fixture.file_uri = try uri_util.pathToUri(allocator, file_path);
        errdefer allocator.free(fixture.file_uri);

        fixture.checker = SyntaxChecker.init(allocator, test_env.io, .{}, null);
        errdefer fixture.checker.deinit();
        test_env.configureChecker(&fixture.checker, std.fs.path.dirname(file_path) orelse file_path);
        fixture.checker.related_information = related_information;

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

    /// The document's one diagnostic whose message contains `needle`.
    fn diagnostic(fixture: *Fixture, needle: []const u8) integration_spec.SpecError!Diagnostics.Diagnostic {
        var found: ?Diagnostics.Diagnostic = null;
        for (fixture.publish_sets) |set| {
            if (!std.mem.eql(u8, set.uri, fixture.file_uri)) continue;
            for (set.diagnostics) |item| {
                if (std.mem.find(u8, item.message, needle) == null) continue;
                if (found != null) {
                    std.debug.print("\nmore than one diagnostic contains \"{s}\"\n", .{needle});
                    return error.TestUnexpectedResult;
                }
                found = item;
            }
        }
        return found orelse {
            std.debug.print("\nno diagnostic in the document contains \"{s}\"; published:\n", .{needle});
            fixture.printDiagnostics();
            return error.TestUnexpectedResult;
        };
    }

    fn printDiagnostics(fixture: *Fixture) void {
        for (fixture.publish_sets) |set| {
            for (set.diagnostics) |item| {
                std.debug.print("{s} {d}:{d}-{d}:{d}\n{s}\n", .{ set.uri, item.range.start.line, item.range.start.character, item.range.end.line, item.range.end.character, item.message });
                for (item.relatedInformation) |related| {
                    const range = related.location.range;
                    std.debug.print("  related {s} {d}:{d}-{d}:{d} {s}\n", .{ related.location.uri, range.start.line, range.start.character, range.end.line, range.end.character, related.message });
                }
            }
        }
    }
};

fn expectRange(actual: Diagnostics.Range, start_line: u32, start_character: u32, end_line: u32, end_character: u32) integration_spec.SpecError!void {
    const expected: Diagnostics.Range = .{
        .start = .{ .line = start_line, .character = start_character },
        .end = .{ .line = end_line, .character = end_character },
    };
    if (std.meta.eql(actual, expected)) return;
    std.debug.print("\nexpected range {d}:{d}-{d}:{d}, got {d}:{d}-{d}:{d}\n", .{
        start_line,        start_character,        end_line,        end_character,
        actual.start.line, actual.start.character, actual.end.line, actual.end.character,
    });
    return error.TestUnexpectedResult;
}

const time_source =
    \\Time :: { nanos : I64 }.{
    \\    to_nanos : Time -> I64
    \\    to_nanos = |t| t.nanos
    \\
    \\    shifted : I64 -> I64
    \\    shifted = |nanos| Time.to_nanos(Time.{ nanos }) + 1
    \\}
    \\
;

const stage_source =
    \\Stage :: {}.{
    \\    describe : Code(f) -> Str
    \\    describe = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
    \\}
    \\
;

/// The walk stops in `Time.roc`, which the report shows first. The document
/// shows the report at the lambda in `main.roc` that reaches it, and the
/// related information names the place in `Time.roc`.
fn foreignRefusalIsShownAtItsSite() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\import Stage
        \\import Time
        \\
        \\away : Str
        \\away = Stage.describe(|x| Time.shifted(x))
        \\
        \\main! = |_args| {
        \\    echo!(away)
        \\    Ok({})
        \\}
        \\
    , &.{
        .{ .name = "Time.roc", .source = time_source },
        .{ .name = "Stage.roc", .source = stage_source },
    }, true);
    defer fixture.deinit();

    const diagnostic = try fixture.diagnostic("no form for this type");
    try expectRange(diagnostic.range, 4, 22, 4, 41);

    if (diagnostic.relatedInformation.len != 1) {
        std.debug.print("\nexpected one related location; published:\n", .{});
        fixture.printDiagnostics();
        return error.TestUnexpectedResult;
    }
    const related = diagnostic.relatedInformation[0];
    if (!std.mem.endsWith(u8, related.location.uri, "/Time.roc")) {
        std.debug.print("\nrelated location is in {s}\n", .{related.location.uri});
        return error.TestUnexpectedResult;
    }
    try expectRange(related.location.range, 5, 36, 5, 50);
}

/// The second `a` is the problem; the first one is its related place, in the
/// same document.
fn duplicateRecordFieldNamesFirstField() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\record = { a: 1, a: 2 }
        \\
        \\main! = |_args| {
        \\    echo!(record.a.to_str())
        \\    Ok({})
        \\}
        \\
    , &.{}, true);
    defer fixture.deinit();

    const diagnostic = try fixture.diagnostic("appears more than once");
    try expectRange(diagnostic.range, 0, 17, 0, 18);

    if (diagnostic.relatedInformation.len != 1) {
        std.debug.print("\nexpected one related location; published:\n", .{});
        fixture.printDiagnostics();
        return error.TestUnexpectedResult;
    }
    const related = diagnostic.relatedInformation[0];
    try std.testing.expectEqualStrings(fixture.file_uri, related.location.uri);
    try expectRange(related.location.range, 0, 11, 0, 12);
}

fn clientWithoutCapabilityGetsNone() integration_spec.SpecError!void {
    var fixture: Fixture = undefined;
    try fixture.init(
        \\record = { a: 1, a: 2 }
        \\
        \\main! = |_args| {
        \\    echo!(record.a.to_str())
        \\    Ok({})
        \\}
        \\
    , &.{}, false);
    defer fixture.deinit();

    const diagnostic = try fixture.diagnostic("appears more than once");
    try std.testing.expectEqual(@as(usize, 0), diagnostic.relatedInformation.len);
}
