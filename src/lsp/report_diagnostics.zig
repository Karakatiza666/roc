//! Compiler reports as LSP diagnostics.
//!
//! A report gives its places as data (`Report.primaryLocation`,
//! `reached_from`, `related`). A diagnostic is published in the file of the
//! module that reports it, at `reached_from` when that is set and at the
//! primary place otherwise.

const std = @import("std");
const reporting = @import("reporting");
const pos = @import("position.zig");
const uri_util = @import("uri.zig");
const Diagnostics = @import("diagnostics.zig");
const BuildEnvHandle = @import("build_env_handle.zig").BuildEnvHandle;

const Allocator = std.mem.Allocator;

/// Converts the reports of one build.
pub const Converter = struct {
    allocator: Allocator,
    handle: *BuildEnvHandle,
    /// The client's open documents, URI to path.
    client_paths: *const std.StringArrayHashMapUnmanaged([]u8),
    /// Whether the client accepts related information.
    related_information: bool,

    pub fn diagnostic(self: Converter, rep: reporting.Report) (Allocator.Error || error{WriteFailed})!Diagnostics.Diagnostic {
        const range = self.rangeFromReport(rep);
        var writer: std.Io.Writer.Allocating = .init(self.allocator);
        defer writer.deinit();
        try reporting.renderReportToLsp(&rep, &writer.writer, reporting.ReportingConfig.initLsp());
        const message = writer.toOwnedSlice() catch return error.OutOfMemory;
        errdefer self.allocator.free(message);

        return .{
            .range = range,
            .severity = rep.severity.toLspSeverity(),
            .source = "roc",
            .message = message,
            .relatedInformation = if (self.related_information) try self.relatedInformation(rep) else &.{},
        };
    }

    /// The range a report is shown at. A report whose primary place is in
    /// another file is shown at the place in this file that reaches it, and
    /// its related information then names the primary place.
    fn rangeFromReport(self: Converter, rep: reporting.Report) Diagnostics.Range {
        const zero: Diagnostics.Range = .{ .start = .{ .line = 0, .character = 0 }, .end = .{ .line = 0, .character = 0 } };
        const location = rep.reached_from orelse rep.primaryLocation() orelse return zero;
        const text = self.reportSourceText(location.file) orelse return zero;
        return rangeFromLocation(location, text);
    }

    /// The related information of a report: its primary place when the report
    /// is shown at `reached_from`, then each related place. A place in no file
    /// of the build (such as a builtin's) has no URI, so it is left out.
    fn relatedInformation(self: Converter, rep: reporting.Report) Allocator.Error![]const Diagnostics.DiagnosticRelatedInformation {
        var items: std.ArrayList(Diagnostics.DiagnosticRelatedInformation) = .empty;
        errdefer {
            for (items.items) |item| {
                self.allocator.free(item.location.uri);
                self.allocator.free(item.message);
            }
            items.deinit(self.allocator);
        }
        if (rep.reached_from != null) {
            if (rep.primaryLocation()) |primary| try self.appendRelated(&items, primary, rep.title);
        }
        for (rep.related.items) |related| try self.appendRelated(&items, related.location, related.message);
        return items.toOwnedSlice(self.allocator);
    }

    fn appendRelated(
        self: Converter,
        items: *std.ArrayList(Diagnostics.DiagnosticRelatedInformation),
        location: reporting.Location,
        message: []const u8,
    ) Allocator.Error!void {
        const text = self.reportSourceText(location.file) orelse return;
        const uri = try uri_util.clientUriForPath(self.allocator, self.client_paths, location.file);
        errdefer self.allocator.free(uri);
        const owned_message = try self.allocator.dupe(u8, message);
        errdefer self.allocator.free(owned_message);
        try items.append(self.allocator, .{
            .location = .{ .uri = uri, .range = rangeFromLocation(location, text) },
            .message = owned_message,
        });
    }

    /// The text of the file at `path` as report locations count its lines: a
    /// staged document's own text, since reports map the staging back to it,
    /// or the source of the build's module at that path. Null for a path that
    /// names no file of the build.
    fn reportSourceText(self: Converter, path: []const u8) ?[]const u8 {
        if (self.handle.staged_document) |staged| {
            if (std.mem.eql(u8, path, staged.user_path)) return staged.staged.original_source;
        }
        const module_state = self.handle.envPtr().findModuleByPath(path) orelse return null;
        const module_env = module_state.moduleEnv() orelse return null;
        return module_env.common.source;
    }
};

/// Convert a report location to an LSP range over `text`, the text of its
/// file. Columns are converted from the source bytes, never the visible
/// diagnostic text: escaping a control must not move its editor highlight.
pub fn rangeFromLocation(location: reporting.Location, text: []const u8) Diagnostics.Range {
    return .{
        .start = reportPosition(text, location.start_line, location.start_column),
        .end = reportPosition(text, location.end_line, location.end_column),
    };
}

fn reportPosition(source: []const u8, line: u32, column: u32) Diagnostics.Position {
    var lines = std.mem.splitScalar(u8, source, '\n');
    var current: u32 = 1;
    while (lines.next()) |text| : (current += 1) {
        if (current == line) return .{
            .line = saturatingMinusOne(line),
            .character = pos.byteOffsetToUtf16Column(text, saturatingMinusOne(column)),
        };
    }
    // Reports can point immediately past the available source at EOF.
    return .{ .line = saturatingMinusOne(line), .character = 0 };
}

fn saturatingMinusOne(value: u32) u32 {
    return if (value == 0) 0 else value - 1;
}

/// Temporary suppression to avoid noisy name-not-in-scope diagnostics from BuildEnv.
pub fn shouldSuppress(rep: reporting.Report) bool {
    if (!std.mem.startsWith(u8, rep.title, "Name Not In Scope")) return false;

    const disallowed = [_][]const u8{ "Stderr", "Stdin", "Stdout" };
    return reportContainsAny(rep, &disallowed);
}

fn reportContainsAny(rep: reporting.Report, needles: []const []const u8) bool {
    var idx: usize = 0;
    while (rep.document.getElement(idx)) |element| : (idx += 1) {
        if (elementContainsAny(element, needles)) return true;
    }
    return false;
}

fn elementContainsAny(element: reporting.DocumentElement, needles: []const []const u8) bool {
    switch (element) {
        .text => |t| return textHasAny(t, needles),
        .annotated => |a| return textHasAny(a.content, needles),
        inline .raw, .reflowing_text, .link => |r| return textHasAny(r, needles),
        inline .vertical_stack, .horizontal_concat => |stack| {
            for (stack) |el| if (elementContainsAny(el, needles)) return true;
        },
        .source_code_region => |region| return textHasAny(region.line_text, needles),
        .source_code_multi_region => |multi| return textHasAny(multi.source, needles),
        .source_code_with_underlines => |with_underlines| return textHasAny(with_underlines.display_region.line_text, needles),
        .source_location => {},
        .line_break,
        .indent,
        .space,
        .horizontal_rule,
        .annotation_start,
        .annotation_end,
        => {},
    }
    return false;
}

fn textHasAny(text: []const u8, needles: []const []const u8) bool {
    for (needles) |needle| {
        if (std.mem.find(u8, text, needle) != null) return true;
    }
    return false;
}

test "bidi diagnostic range uses original UTF-16 source positions" {
    const source = "# \u{1F642} \u{5D0}\u{5D1}\u{202E}\n";
    const start = std.mem.find(u8, source, "\u{202E}").?;
    var report = try reporting.Report.init(std.testing.allocator, "Bidi Test", "A control is forbidden.", .runtime_error);
    defer report.deinit();
    try report.document.addSourceRegion(.{
        .start_line_idx = 0,
        .start_col_idx = @intCast(start),
        .end_line_idx = 0,
        .end_col_idx = @intCast(start + "\u{202E}".len),
    }, .error_highlight, "Probe.roc", source, &.{0});
    const range = rangeFromLocation(report.primaryLocation().?, source);
    try std.testing.expectEqual(@as(u32, 0), range.start.line);
    try std.testing.expectEqual(@as(u32, 7), range.start.character);
    try std.testing.expectEqual(@as(u32, 8), range.end.character);
}
