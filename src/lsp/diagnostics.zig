//! LSP diagnostic types for reporting errors, warnings, and hints to editors.

const std = @import("std");

/// The position of the diagnostic
pub const Position = struct {
    line: u32,
    character: u32,
};

/// The range of characters that the diagnostic applies to
pub const Range = struct {
    start: Position,
    end: Position,
};

/// A place in a document, named by its URI.
pub const Location = struct {
    uri: []const u8,
    range: Range,
};

/// Another place a diagnostic names, with a message that says what is there.
pub const DiagnosticRelatedInformation = struct {
    location: Location,
    message: []const u8,
};

/// Diagnostic expected by LSP specifications
pub const Diagnostic = struct {
    range: Range,
    severity: ?u32 = null,
    source: ?[]const u8 = null,
    message: []const u8,
    /// Owned like `message`. Empty when the report names no other place, or
    /// when the client does not accept related information.
    relatedInformation: []const DiagnosticRelatedInformation = &.{},

    /// Free the strings and slices the diagnostic owns.
    pub fn deinit(self: Diagnostic, allocator: std.mem.Allocator) void {
        allocator.free(self.message);
        for (self.relatedInformation) |related| {
            allocator.free(related.location.uri);
            allocator.free(related.message);
        }
        allocator.free(self.relatedInformation);
    }

    /// A copy that owns its own strings and slices.
    pub fn clone(self: Diagnostic, allocator: std.mem.Allocator) std.mem.Allocator.Error!Diagnostic {
        var copy = self;
        copy.message = try allocator.dupe(u8, self.message);
        errdefer allocator.free(copy.message);
        const related = try allocator.alloc(DiagnosticRelatedInformation, self.relatedInformation.len);
        var copied: usize = 0;
        errdefer {
            for (related[0..copied]) |item| {
                allocator.free(item.location.uri);
                allocator.free(item.message);
            }
            allocator.free(related);
        }
        for (self.relatedInformation, related) |source, *target| {
            const uri = try allocator.dupe(u8, source.location.uri);
            errdefer allocator.free(uri);
            target.* = .{
                .location = .{ .uri = uri, .range = source.location.range },
                .message = try allocator.dupe(u8, source.message),
            };
            copied += 1;
        }
        copy.relatedInformation = related;
        return copy;
    }

    /// Write the diagnostic as the protocol has it. The protocol makes
    /// `relatedInformation` optional, so an empty list is left out.
    pub fn jsonStringify(self: Diagnostic, writer: anytype) error{WriteFailed}!void {
        try writer.beginObject();
        try writer.objectField("range");
        try writer.write(self.range);
        try writer.objectField("severity");
        try writer.write(self.severity);
        try writer.objectField("source");
        try writer.write(self.source);
        try writer.objectField("message");
        try writer.write(self.message);
        if (self.relatedInformation.len != 0) {
            try writer.objectField("relatedInformation");
            try writer.write(self.relatedInformation);
        }
        try writer.endObject();
    }
};

/// Container for diagnostics destined for a single URI.
pub const PublishDiagnostics = struct {
    uri: []u8,
    diagnostics: []Diagnostic,

    pub fn deinit(self: *PublishDiagnostics, allocator: std.mem.Allocator) void {
        allocator.free(self.uri);
        freeAll(allocator, self.diagnostics);
        self.* = undefined;
    }
};

/// A copy of `diagnostics` that owns its own strings and slices.
pub fn cloneAll(allocator: std.mem.Allocator, diagnostics: []const Diagnostic) std.mem.Allocator.Error![]Diagnostic {
    const copy = try allocator.alloc(Diagnostic, diagnostics.len);
    var copied: usize = 0;
    errdefer {
        for (copy[0..copied]) |diag| diag.deinit(allocator);
        allocator.free(copy);
    }
    for (diagnostics, copy) |diag, *target| {
        target.* = try diag.clone(allocator);
        copied += 1;
    }
    return copy;
}

/// Free owned diagnostics and the slice that holds them.
pub fn freeAll(allocator: std.mem.Allocator, diagnostics: []Diagnostic) void {
    for (diagnostics) |diag| diag.deinit(allocator);
    allocator.free(diagnostics);
}
