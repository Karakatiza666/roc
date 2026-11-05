//! The one boundary between an open document and its checked module.
//!
//! A request names positions in the document, and queries answer with ranges
//! of the module. For most documents these are the same text. A document on
//! the default platform is checked as a staged app (`StagedDocument`), whose
//! module holds the staged source: positions move into it, and ranges move
//! back out, leaving out text that staging wrote. Handlers convert only here.

const std = @import("std");
const can = @import("can");
const pos = @import("position.zig");
const cir_queries = @import("cir_queries.zig");
const semantic_tokens = @import("semantic_tokens.zig");
const completion_context = @import("completion/context.zig");
const StagedDocument = @import("staged_document.zig").StagedDocument;

const Allocator = std.mem.Allocator;
const ModuleEnv = can.ModuleEnv;
const Region = @import("base").Region;
const LspRange = cir_queries.LspRange;

/// A line and UTF-16 character in the document.
pub const Position = struct {
    line: u32,
    character: u32,
};

/// A document and the module it was checked as.
pub const DocumentView = struct {
    module_env: *ModuleEnv,
    /// Set when the document was checked as a staged app.
    staged: ?*const StagedDocument,

    /// The module offset of a document position, or null when the document
    /// has no such position or staging changed the text there.
    pub fn offsetAt(self: DocumentView, line: u32, character: u32) ?u32 {
        const staged = self.staged orelse return pos.positionToOffset(self.module_env, line, character);
        return stagedOffset(staged, line, character, .reject);
    }

    /// `offsetAt`, clamped as `position.positionToOffsetClamped` clamps: a
    /// column past its line's end is the line's end, and a line past the last
    /// one is the end of the document.
    pub fn offsetAtClamped(self: DocumentView, line: u32, character: u32) ?u32 {
        const staged = self.staged orelse return pos.positionToOffsetClamped(self.module_env, line, character);
        const user_offset = pos.offsetOnLine(staged.user_lines.source, staged.user_lines.offsets, line, character, .clamp_to_line_end) orelse
            @as(u32, @intCast(staged.user_lines.source.len));
        return @intCast(staged.staged.stagedOffset(user_offset) orelse return null);
    }

    /// The document range of a module range, or null when it lies in text
    /// that staging wrote.
    pub fn rangeOf(self: DocumentView, range: LspRange) ?LspRange {
        const staged = self.staged orelse return range;
        const start = toUser(staged, range.start_line, range.start_col) orelse return null;
        const end = toUser(staged, range.end_line, range.end_col) orelse return null;
        return .{ .start_line = start.line, .start_col = start.character, .end_line = end.line, .end_col = end.character };
    }

    /// The document range of a module region.
    pub fn rangeOfRegion(self: DocumentView, region: Region) ?LspRange {
        return self.rangeOf(cir_queries.regionToRange(self.module_env, region) orelse return null);
    }

    /// The document position of a module position, or null when staging
    /// wrote the text there.
    pub fn positionOf(self: DocumentView, line: u32, character: u32) ?Position {
        const staged = self.staged orelse return .{ .line = line, .character = character };
        return toUser(staged, line, character);
    }

    /// Convert owned module ranges to document ranges in place, leaving out
    /// the ones in text that staging wrote. Frees `ranges` on failure.
    pub fn documentRanges(self: DocumentView, allocator: Allocator, ranges: []LspRange) Allocator.Error![]LspRange {
        var kept: usize = 0;
        for (ranges) |range| {
            ranges[kept] = self.rangeOf(range) orelse continue;
            kept += 1;
        }
        if (kept == ranges.len) return ranges;
        return allocator.realloc(ranges, kept) catch |err| {
            allocator.free(ranges);
            return err;
        };
    }

    /// Whether every module range is in the document's own text.
    pub fn allInDocument(self: DocumentView, ranges: []const LspRange) bool {
        for (ranges) |range| {
            if (self.rangeOf(range) == null) return false;
        }
        return true;
    }

    /// The source the module's positions count in: the staged source, or
    /// `document_text` for a document checked as written.
    pub fn moduleSource(self: DocumentView, document_text: []const u8) []const u8 {
        const staged = self.staged orelse return document_text;
        return staged.staged.synthetic_source;
    }

    /// The semantic tokens of the document, found in the module and moved to
    /// the document. A token in text that staging wrote is left out.
    pub fn semanticTokens(
        self: DocumentView,
        allocator: Allocator,
        document_text: []const u8,
        document_lines: *const pos.LineOffsets,
    ) Allocator.Error![]semantic_tokens.SemanticToken {
        const staged = self.staged orelse
            return semantic_tokens.extractSemanticTokensFromChecked(allocator, document_text, document_lines, self.module_env);
        const tokens = try semantic_tokens.extractSemanticTokensFromChecked(allocator, staged.staged.synthetic_source, &staged.staged_lines, self.module_env);
        var kept: usize = 0;
        for (tokens) |token| {
            const start = toUser(staged, token.line, token.start_char) orelse continue;
            tokens[kept] = token;
            tokens[kept].line = start.line;
            tokens[kept].start_char = start.character;
            kept += 1;
        }
        if (kept == tokens.len) return tokens;
        return allocator.realloc(tokens, kept) catch |err| {
            allocator.free(tokens);
            return err;
        };
    }
};

/// A completion context and cursor found in the document's current text,
/// moved into the module of a build made from earlier text. Null when an
/// offset lies in a header that staging rewrote.
pub fn completionContext(
    staged_opt: ?*const StagedDocument,
    context: completion_context.CompletionContext,
    cursor: u32,
) ?struct { completion_context.CompletionContext, u32 } {
    const staged = staged_opt orelse return .{ context, cursor };
    const moved: completion_context.CompletionContext = switch (context) {
        .after_module_dot, .after_colon, .expression => context,
        .after_value_dot => |value_dot| .{ .after_value_dot = .{
            .access_chain = value_dot.access_chain,
            .chain_start = staged.editedTextOffset(value_dot.chain_start) orelse return null,
            .receiver_segment_start = staged.editedTextOffset(value_dot.receiver_segment_start) orelse return null,
            .dot_offset = staged.editedTextOffset(value_dot.dot_offset) orelse return null,
        } },
        .after_receiver_dot => |receiver_dot| .{ .after_receiver_dot = .{
            .dot_offset = staged.editedTextOffset(receiver_dot.dot_offset) orelse return null,
            .call_chain = receiver_dot.call_chain,
            .chain_start = staged.editedTextOffset(receiver_dot.chain_start) orelse return null,
        } },
    };
    return .{ moved, staged.editedTextOffset(cursor) orelse return null };
}

fn stagedOffset(staged: *const StagedDocument, line: u32, character: u32, past_line_end: pos.PastLineEnd) ?u32 {
    const user_offset = pos.offsetOnLine(staged.user_lines.source, staged.user_lines.offsets, line, character, past_line_end) orelse return null;
    return @intCast(staged.staged.stagedOffset(user_offset) orelse return null);
}

fn toUser(staged: *const StagedDocument, line: u32, character: u32) ?Position {
    const staged_offset = staged.staged_lines.offsetAt(line, character) orelse return null;
    const user_offset = staged.staged.userOffset(staged_offset) orelse return null;
    const converted = pos.offsetToPosition(@intCast(user_offset), &staged.user_lines);
    return .{ .line = converted.line, .character = converted.character };
}
