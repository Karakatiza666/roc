//! Report system for formatted warning and error reports.
//!
//! This module provides the Report struct and related functionality for creating
//! structured error reports that can be rendered to different output formats.
//!
//! Reports combine a title, severity level, and formatted document content.

const std = @import("std");
const builtin = @import("builtin");
const base = @import("base");

const Allocator = std.mem.Allocator;
const Severity = @import("severity.zig").Severity;
const Document = @import("document.zig").Document;
const RenderTarget = @import("renderer.zig").RenderTarget;
const RegionInfo = base.RegionInfo;
const renderReport = @import("renderer.zig").renderReport;
const validateUtf8 = @import("config.zig").validateUtf8;
const truncateUtf8 = @import("config.zig").truncateUtf8;

/// Default maximum message size in bytes for truncation
const DEFAULT_MAX_MESSAGE_BYTES: usize = 4096;

/// True if `title` contains `needle` (which must be lowercase) as a substring,
/// compared case-insensitively.
fn titleContainsIgnoreCase(title: []const u8, needle: []const u8) bool {
    if (needle.len == 0 or title.len < needle.len) return false;
    var i: usize = 0;
    while (i + needle.len <= title.len) : (i += 1) {
        var matches = true;
        for (needle, 0..) |nc, j| {
            const tc = title[i + j];
            const lowered = if (tc >= 'A' and tc <= 'Z') tc + ('a' - 'A') else tc;
            if (lowered != nc) {
                matches = false;
                break;
            }
        }
        if (matches) return true;
    }
    return false;
}

/// In debug builds, enforce the house style for error-report title/description
/// text. These are compiled out of release builds.
///
/// A title must be:
///   - all ASCII;
///   - trimmed, with no newlines or consecutive spaces;
///   - title case outside backticks: every non-minor word begins with a capital
///     letter (or a digit), every word contains only alphanumeric characters,
///     except for `UTF-` prefixed words such as `UTF-8`, and the title has at
///     least one lowercase letter (so source code reads as `Title Case`, not
///     `ALL CAPS`; diagnostic renderers display it in lowercase);
///   - allowed to contain backticked inline code spans, whose contents must be
///     non-empty and trimmed, but are not title-cased;
///   - free of the word "comptime", which is a Zig term, not a Roc one, and so
///     must never reach user-facing text;
///   - free of any pairing of "annotation" with "need" or "miss"—Roc never
///     tells users they must annotate their types (see the panic below).
fn isTrimmed(text: []const u8) bool {
    return std.mem.eql(u8, text, std.mem.trim(u8, text, " \t\r\n"));
}

fn isAsciiLower(c: u8) bool {
    return c >= 'a' and c <= 'z';
}

fn isAsciiUpper(c: u8) bool {
    return c >= 'A' and c <= 'Z';
}

fn isAsciiDigit(c: u8) bool {
    return c >= '0' and c <= '9';
}

fn isAsciiAlphaNum(c: u8) bool {
    return isAsciiLower(c) or isAsciiUpper(c) or isAsciiDigit(c);
}

fn isUtfPrefixedTitleWord(word: []const u8) bool {
    const prefix = "UTF-";
    if (!std.mem.startsWith(u8, word, prefix)) return false;
    if (word.len == prefix.len) return false;

    for (word[prefix.len..]) |c| {
        if (!isAsciiAlphaNum(c)) return false;
    }

    return true;
}

fn containsNewline(text: []const u8) bool {
    return std.mem.findScalar(u8, text, '\n') != null or
        std.mem.findScalar(u8, text, '\r') != null;
}

fn isLowercaseTitleParticle(word: []const u8) bool {
    const particles = [_][]const u8{
        "a",   "an",   "and",    "as",      "at",      "but", "by",
        "for", "from", "in",     "into",    "nor",     "of",  "on",
        "or",  "over", "per",    "the",     "through", "to",  "via",
        "vs",  "with", "within", "without",
    };
    for (particles) |particle| {
        if (std.mem.eql(u8, word, particle)) return true;
    }
    return false;
}

fn isValidTitleWord(word: []const u8, is_first: bool, is_last: bool, has_lower: *bool) bool {
    if (word.len == 0) return false;

    const utf_prefixed = isUtfPrefixedTitleWord(word);
    for (word) |c| {
        if (!isAsciiAlphaNum(c) and !(utf_prefixed and c == '-')) return false;
        if (isAsciiLower(c)) has_lower.* = true;
    }

    if (isAsciiLower(word[0])) {
        return !is_first and !is_last and isLowercaseTitleParticle(word);
    }

    return true;
}

fn countTitleTokens(title: []const u8) ?usize {
    var count: usize = 0;
    var i: usize = 0;
    while (i < title.len) {
        if (title[i] == ' ') {
            i += 1;
            continue;
        }

        if (title[i] == '`') {
            const start = i + 1;
            i = start;
            while (i < title.len and title[i] != '`') : (i += 1) {}
            if (i == title.len) return null;

            const code = title[start..i];
            if (code.len == 0 or !isTrimmed(code)) return null;

            count += 1;
            i += 1;
        } else {
            const start = i;
            while (i < title.len and title[i] != ' ' and title[i] != '`') : (i += 1) {}
            if (start == i) return null;

            count += 1;
        }

        if (i < title.len and title[i] != ' ') return null;
    }

    return count;
}

fn validateTitleTokens(title: []const u8, token_count: usize) bool {
    var token_index: usize = 0;
    var has_lower = false;
    var i: usize = 0;
    while (i < title.len) {
        if (title[i] == ' ') {
            i += 1;
            continue;
        }

        if (title[i] == '`') {
            i += 1;
            while (i < title.len and title[i] != '`') : (i += 1) {}
            if (i == title.len) return false;
            i += 1;
            token_index += 1;
            continue;
        }

        const start = i;
        while (i < title.len and title[i] != ' ' and title[i] != '`') : (i += 1) {}
        if (!isValidTitleWord(title[start..i], token_index == 0, token_index + 1 == token_count, &has_lower)) {
            return false;
        }
        token_index += 1;
    }

    return token_index == token_count and has_lower;
}

fn isValidReportTitle(title: []const u8) bool {
    if (title.len == 0 or !isTrimmed(title) or containsNewline(title)) return false;
    if (std.mem.find(u8, title, "  ") != null) return false;

    for (title) |c| {
        if (c >= 0x80) return false;
    }

    const token_count = countTitleTokens(title) orelse return false;
    if (token_count == 0) return false;

    return validateTitleTokens(title, token_count);
}

fn isValidReportDescription(description: []const u8) bool {
    return isTrimmed(description);
}

fn assertValidTitleAndDescription(title: []const u8, description: []const u8) void {
    if (builtin.mode != .debug) return;

    std.debug.assert(isValidReportTitle(title));
    std.debug.assert(isValidReportDescription(description));
    std.debug.assert(!titleContainsIgnoreCase(title, "comptime"));

    if (titleContainsIgnoreCase(title, "annotation") and
        (titleContainsIgnoreCase(title, "need") or titleContainsIgnoreCase(title, "miss")))
    {
        base.invariant("{s}", .{"Error-report title pairs \"annotation\" with \"need\"/\"miss\". Roc never tells " ++
            "users they NEED to annotate their types: unlike many languages, type annotations " ++
            "are never required as a matter of course, so no part of a diagnostic report should " ++
            "say a type needs, or is missing, an annotation. When a type is ambiguous, explain " ++
            "the ambiguity itself; at most, note that one way to make it unambiguous is to " ++
            "introduce a type annotation somewhere. Reword this report's title, headline, and " ++
            "body to describe the ambiguity rather than to demand an annotation."});
    }
}

/// A span of a source file in 1-based display coordinates. Lines and byte
/// columns count from 1. The end column is one past the span's last byte.
pub const Location = struct {
    /// The path of the file, as the report names it. Owned by the report.
    file: []const u8,
    start_line: u32,
    start_column: u32,
    end_line: u32,
    end_column: u32,

    /// The location of `region`, given in 0-based coordinates, in `file`.
    pub fn fromRegionInfo(file: []const u8, region: RegionInfo) Location {
        return .{
            .file = file,
            .start_line = region.start_line_idx + 1,
            .start_column = region.start_col_idx + 1,
            .end_line = region.end_line_idx + 1,
            .end_column = region.end_col_idx + 1,
        };
    }

    fn assertValid(self: Location) void {
        std.debug.assert(self.start_line != 0 and self.start_column != 0);
        std.debug.assert(self.end_line > self.start_line or
            (self.end_line == self.start_line and self.end_column >= self.start_column));
    }
};

/// A place other than the primary one that a report names, with a short
/// message that says what is there.
pub const RelatedLocation = struct {
    location: Location,
    /// Owned by the report.
    message: []const u8,
};

/// A structured report containing error information and formatted content.
///
/// Besides the document, a report gives its places as data, so that a
/// consumer such as the language server reads them and does not search the
/// document for them:
///   - `primaryLocation()` is the place the report is about;
///   - `reached_from` is set when that place is in a file other than the file
///     of the module that reports it;
///   - `related` lists the other places the report names.
pub const Report = struct {
    title: []const u8,
    /// One-sentence summary shown below the terminal header, below the title
    /// in markdown/HTML, or first in LSP. Rich content preserves inline code,
    /// type names, and operators. Builders with a plain headline pass it to `init`; builders
    /// that need inline styling pass `""` and add to this document directly.
    headline: Document,
    severity: Severity,
    /// The kind of problem the report is about, for a consumer that acts on
    /// one kind of report. Builders set it after `init`.
    kind: Kind,
    document: Document,
    /// The file a report is about as a whole, for a report that has no source
    /// region because nothing in the file's text is the problem (for example,
    /// a definition the file lacks). Renderers name it in place of a position.
    /// Owned by `owned_strings`.
    file: ?[]const u8,
    /// The place the report is about, when a builder names it. When null, the
    /// place is the report's first highlighted source region
    /// (`primaryLocation`).
    primary: ?Location,
    /// When the primary place is in a file other than the file of the module
    /// that reports it: the place in that module's file that reaches it. A
    /// consumer that shows reports in the reporting module's file shows the
    /// report here. Null when the primary place is in that file.
    reached_from: ?Location,
    /// The other places the report names, in the order the document names
    /// them. Each one is also in the document, as prose or as source.
    related: std.ArrayList(RelatedLocation),
    allocator: Allocator,

    /// The kinds of problem that a consumer of reports must tell apart.
    pub const Kind = enum {
        /// A definition crashed during compile-time evaluation.
        compile_time_crash,
        /// Every other problem.
        other,
    };

    pub fn init(allocator: Allocator, title: []const u8, headline: []const u8, severity: Severity) Allocator.Error!Report {
        assertValidTitleAndDescription(title, headline);
        var report = Report{
            .title = title,
            .headline = Document.init(allocator),
            .severity = severity,
            .kind = .other,
            .document = Document.init(allocator),
            .file = null,
            .primary = null,
            .reached_from = null,
            .related = .empty,
            .allocator = allocator,
        };
        if (headline.len > 0) {
            try report.headline.addReflowingText(headline);
        }
        return report;
    }

    /// A report whose headline names a file: `before`, then `path`, then
    /// `after`. Renderers show the path relative to the working directory.
    pub fn initWithPath(
        allocator: Allocator,
        title: []const u8,
        before: []const u8,
        path: []const u8,
        after: []const u8,
        severity: Severity,
    ) Allocator.Error!Report {
        var report = try init(allocator, title, "", severity);
        errdefer report.deinit();
        try report.headline.addReflowingText(before);
        try report.headline.addAnnotated(path, .path);
        try report.headline.addReflowingText(after);
        return report;
    }

    pub fn deinit(self: *Report) void {
        self.headline.deinit();
        self.document.deinit();
        self.related.deinit(self.allocator);
    }

    /// Add a string that the report will take ownership of.
    /// Returns the owned copy of the string, which lives in the report's
    /// document content and can be safely used in either document.
    pub fn addOwnedString(self: *Report, string: []const u8) Allocator.Error![]const u8 {
        return self.document.ownString(string);
    }

    /// Mark the report as being about `path` as a whole. A report with a
    /// source region already names its file there, so it never has one.
    pub fn setFile(self: *Report, path: []const u8) Allocator.Error!void {
        self.file = try self.addOwnedString(path);
    }

    /// Copy `location`'s file into the report.
    fn ownLocation(self: *Report, location: Location) Allocator.Error!Location {
        location.assertValid();
        var owned = location;
        owned.file = try self.addOwnedString(location.file);
        return owned;
    }

    /// Name the place the report is about, for a report whose first
    /// highlighted source region is not that place.
    pub fn setPrimary(self: *Report, location: Location) Allocator.Error!void {
        self.primary = try self.ownLocation(location);
    }

    /// Name the place in the reporting module's file that reaches a primary
    /// place in another file.
    pub fn setReachedFrom(self: *Report, location: Location) Allocator.Error!void {
        self.reached_from = try self.ownLocation(location);
    }

    /// Record `location` as a related place with `message`, without adding
    /// anything to the document.
    pub fn addRelated(self: *Report, location: Location, message: []const u8) Allocator.Error!void {
        const owned = try self.ownLocation(location);
        const owned_message = try self.addOwnedString(message);
        try self.related.append(self.allocator, .{ .location = owned, .message = owned_message });
    }

    /// Name `location` in the document as `path:line:col`, inline with the
    /// surrounding prose, and record it as a related place with `message`.
    pub fn addRelatedSourceLocation(self: *Report, location: Location, message: []const u8) Allocator.Error!void {
        try self.addRelated(location, message);
        try self.document.addForeignSourceLocation(location.file, location.start_line, location.start_column);
    }

    /// The place the report is about: the place a builder named with
    /// `setPrimary`, else the report's first highlighted source region. Null
    /// for a report with no source region, or whose first region names no
    /// file.
    pub fn primaryLocation(self: *const Report) ?Location {
        if (self.primary) |primary| return primary;
        const region, const file = self.firstHighlightedRegion() orelse return null;
        return .{
            .file = file orelse return null,
            .start_line = region.start_line_idx,
            .start_column = region.start_col_idx,
            .end_line = region.end_line_idx,
            .end_column = region.end_col_idx,
        };
    }

    /// Render the report to the specified writer and target format.
    pub fn render(self: *const Report, writer: *std.Io.Writer, target: RenderTarget) (Allocator.Error || error{WriteFailed})!void {
        try renderReport(self, writer, target);
    }

    /// Add a section header to the report.
    pub fn addHeader(self: *Report, header: []const u8) Allocator.Error!void {
        try self.document.addLineBreak();
        try self.document.addAnnotated(header, .emphasized);
        try self.document.addLineBreak();
    }

    /// Add source context using RegionInfo for better accuracy and simplicity.
    pub fn addSourceContext(self: *Report, region: RegionInfo, filename: ?[]const u8, source: []const u8, line_starts: []const u32) Allocator.Error!void {
        validateUtf8(region.calculateLineText(source, line_starts)) catch |err| switch (err) {
            error.InvalidUtf8 => {
                try self.document.addError("[Invalid UTF-8 in source context]");
                try self.document.addLineBreak();
                return;
            },
        };

        // Use proper source region API for consistent formatting
        // addSourceRegion now expects 0-based coordinates and handles conversion internally
        try self.document.addSourceRegion(
            region,
            .error_highlight,
            filename,
            source,
            line_starts,
        );
    }

    /// Add a suggestion with proper formatting and UTF-8 validation.
    pub fn addSuggestion(self: *Report, suggestion: []const u8) Allocator.Error!void {
        validateUtf8(suggestion) catch |err| switch (err) {
            error.InvalidUtf8 => {
                try self.document.addError("[Invalid UTF-8 in suggestion]");
                try self.document.addLineBreak();
                return;
            },
        };

        const truncated_suggestion = if (suggestion.len > DEFAULT_MAX_MESSAGE_BYTES) blk: {
            const truncated = truncateUtf8(self.allocator, suggestion, DEFAULT_MAX_MESSAGE_BYTES) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.InvalidUtf8, error.CannotTruncate => unreachable, // `suggestion` was validated as UTF-8 above, and the limit always leaves a truncation point
            };
            break :blk truncated;
        } else suggestion;
        defer if (truncated_suggestion.ptr != suggestion.ptr) self.allocator.free(truncated_suggestion);

        try self.document.addLineBreak();
        try self.document.addAnnotated("Hint: ", .suggestion);
        try self.document.addText(truncated_suggestion);
        try self.document.addLineBreak();
    }

    /// Add a note with dimmed styling.
    pub fn addNote(self: *Report, note: []const u8) Allocator.Error!void {
        try self.document.addLineBreak();
        try self.document.addAnnotated("Note: ", .dimmed);
        try self.document.addText(note);
        try self.document.addLineBreak();
    }

    /// Add an error message with proper styling.
    pub fn addErrorMessage(self: *Report, message: []const u8) Allocator.Error!void {
        try self.document.addError(message);
        try self.document.addLineBreak();
    }

    /// Add a warning message with proper styling.
    pub fn addWarningMessage(self: *Report, message: []const u8) Allocator.Error!void {
        try self.document.addWarning(message);
        try self.document.addLineBreak();
    }

    /// Extract region information from the document elements.
    /// Returns the first highlighted region in 1-based display coordinates,
    /// or null if none exists. Context surrounding an underline is not part
    /// of the diagnostic location.
    pub fn getRegionInfo(self: *const Report) ?RegionInfo {
        const region, _ = self.firstHighlightedRegion() orelse return null;
        return region;
    }

    /// The first highlighted region in 1-based display coordinates, and the
    /// file its source element names.
    fn firstHighlightedRegion(self: *const Report) ?struct { RegionInfo, ?[]const u8 } {
        for (self.document.elements.items) |element| {
            switch (element) {
                .source_code_region => |region_data| {
                    return .{ RegionInfo{
                        .start_line_idx = region_data.start_line,
                        .start_col_idx = region_data.start_column,
                        .end_line_idx = region_data.end_line,
                        .end_col_idx = region_data.end_column,
                    }, region_data.filename };
                },
                .source_code_with_underlines => |underlines_data| {
                    if (underlines_data.underline_regions.len == 0) continue;
                    const region = underlines_data.underline_regions[0];
                    return .{ RegionInfo{
                        .start_line_idx = region.start_line,
                        .start_col_idx = region.start_column,
                        .end_line_idx = region.end_line,
                        .end_col_idx = region.end_column,
                    }, underlines_data.display_region.filename };
                },
                .source_code_multi_region => |multi| {
                    if (multi.regions.len == 0) continue;
                    const region = multi.regions[0];
                    return .{ RegionInfo{
                        .start_line_idx = region.start_line,
                        .start_col_idx = region.start_column,
                        .end_line_idx = region.end_line,
                        .end_col_idx = region.end_column,
                    }, multi.filename };
                },
                .text,
                .annotated,
                .line_break,
                .indent,
                .space,
                .horizontal_rule,
                .annotation_start,
                .annotation_end,
                .raw,
                .reflowing_text,
                .link,
                .vertical_stack,
                .horizontal_concat,
                .source_location,
                => {},
            }
        }
        return null;
    }

    /// Check if the report is empty (has no content).
    pub fn isEmpty(self: *const Report) bool {
        return self.document.isEmpty();
    }
};

// Tests
const testing = std.testing;

test "Report title validation allows backticked code" {
    try testing.expect(isValidReportTitle("`dbg` in Optimized Build"));
    try testing.expect(isValidReportTitle("Type `main!` Should Take 1 Argument"));
    try testing.expect(isValidReportTitle("Try Operator Outside Function"));
    try testing.expect(isValidReportTitle("Invalid UTF-8"));
}

test "Report title validation rejects malformed titles" {
    try testing.expect(!isValidReportTitle(" Debug Error"));
    try testing.expect(!isValidReportTitle("Debug Error "));
    try testing.expect(!isValidReportTitle("Debug\nError"));
    try testing.expect(!isValidReportTitle("Debug  Error"));
    try testing.expect(!isValidReportTitle("Debug-Error"));
    try testing.expect(!isValidReportTitle("debug Error"));
    try testing.expect(!isValidReportTitle("Debug in"));
    try testing.expect(!isValidReportTitle("Debug ` dbg` Error"));
    try testing.expect(!isValidReportTitle("Debug `dbg ` Error"));
    try testing.expect(!isValidReportTitle("Debug `` Error"));
    try testing.expect(!isValidReportTitle("Debug `dbg Error"));
    try testing.expect(!isValidReportTitle("Debug UTF- Error"));
    try testing.expect(!isValidReportTitle("Debug UTF-8-16 Error"));
}

test "Report description validation checks trimming" {
    try testing.expect(isValidReportDescription(""));
    try testing.expect(isValidReportDescription("Something went wrong."));
    try testing.expect(!isValidReportDescription(" Something went wrong."));
    try testing.expect(!isValidReportDescription("Something went wrong. "));
}

test "Report basic functionality" {
    var report = try Report.init(testing.allocator, "Test Error", "Something went wrong in the test.", .runtime_error);
    defer report.deinit();

    try report.document.addText("This is a test error message.");
    try report.addSuggestion("Try fixing the issue.");

    try testing.expect(!report.isEmpty());
}

test "Report diagnostic location uses the underline rather than its context" {
    var report = try Report.init(testing.allocator, "Type Mismatch", "", .runtime_error);
    defer report.deinit();
    try report.document.addSourceCodeWithUnderlines(.{
        .line_text = "match value {\n    A(_) => 1\n}",
        .start_line = 3,
        .start_column = 1,
        .end_line = 5,
        .end_column = 2,
        .region_annotation = .dimmed,
        .filename = "test.roc",
    }, &.{.{
        .start_line = 4,
        .start_column = 5,
        .end_line = 4,
        .end_column = 9,
        .annotation = .error_highlight,
    }});
    const region = report.getRegionInfo().?;
    try testing.expectEqual(@as(u32, 4), region.start_line_idx);
    try testing.expectEqual(@as(u32, 5), region.start_col_idx);
    try testing.expectEqual(@as(u32, 4), region.end_line_idx);
    try testing.expectEqual(@as(u32, 9), region.end_col_idx);
}

test "Report primary location is the first highlighted region unless a builder names one" {
    var report = try Report.init(testing.allocator, "Type Mismatch", "", .runtime_error);
    defer report.deinit();
    try testing.expectEqual(@as(?Location, null), report.primaryLocation());

    const source = "x = 1\ny = 2\n";
    try report.document.addSourceRegion(
        .{ .start_line_idx = 1, .start_col_idx = 4, .end_line_idx = 1, .end_col_idx = 5 },
        .error_highlight,
        "Main.roc",
        source,
        &.{ 0, 6 },
    );
    const derived = report.primaryLocation().?;
    try testing.expectEqualStrings("Main.roc", derived.file);
    try testing.expectEqual(@as(u32, 2), derived.start_line);
    try testing.expectEqual(@as(u32, 5), derived.start_column);
    try testing.expectEqual(@as(u32, 2), derived.end_line);
    try testing.expectEqual(@as(u32, 6), derived.end_column);

    try report.setPrimary(.{ .file = "Other.roc", .start_line = 3, .start_column = 1, .end_line = 3, .end_column = 4 });
    try report.setReachedFrom(derived);
    const named = report.primaryLocation().?;
    try testing.expectEqualStrings("Other.roc", named.file);
    try testing.expectEqual(@as(u32, 3), named.start_line);
    try testing.expectEqualStrings("Main.roc", report.reached_from.?.file);
}

test "Report related source location is data and renders as before" {
    var report = try Report.init(testing.allocator, "Duplicate Tag", "", .runtime_error);
    defer report.deinit();
    const region: RegionInfo = .{ .start_line_idx = 2, .start_col_idx = 6, .end_line_idx = 2, .end_col_idx = 9 };
    try report.document.addText("first defined in ");
    try report.addRelatedSourceLocation(.fromRegionInfo("Main.roc", region), "The tag was first defined here.");

    try testing.expectEqual(@as(usize, 1), report.related.items.len);
    const related = report.related.items[0];
    try testing.expectEqualStrings("Main.roc", related.location.file);
    try testing.expectEqualStrings("The tag was first defined here.", related.message);
    try testing.expectEqual(@as(u32, 3), related.location.start_line);
    try testing.expectEqual(@as(u32, 7), related.location.start_column);
    try testing.expectEqual(@as(u32, 3), related.location.end_line);
    try testing.expectEqual(@as(u32, 10), related.location.end_column);

    // The document holds the same element `Document.addSourceLocation` adds.
    var expected = Document.init(testing.allocator);
    defer expected.deinit();
    try expected.addText("first defined in ");
    try expected.addSourceLocation(region, "Main.roc");
    try testing.expectEqual(expected.elements.items.len, report.document.elements.items.len);
    const actual_location = report.document.elements.items[1].source_location;
    const expected_location = expected.elements.items[1].source_location;
    try testing.expectEqualStrings(expected_location.filename.?, actual_location.filename.?);
    try testing.expectEqual(expected_location.line, actual_location.line);
    try testing.expectEqual(expected_location.column, actual_location.column);
}
