//! A document that runs on the default Echo platform: a headerless app, or an
//! app header that names no platform.
//!
//! The server checks it the way `roc check` does. `compile.default_app`
//! stages the document text into a scratch directory beside the Echo platform,
//! and the build compiles that staged app. Its module therefore holds the
//! staged source. `DocumentView` converts positions between the document and
//! the module with the byte map kept here.

const std = @import("std");
const compile = @import("compile");
const pos = @import("position.zig");

const Allocator = std.mem.Allocator;
const default_app = compile.default_app;

/// A staged document and the scratch directory that holds its staged files.
/// It lives as long as the build that compiled it.
pub const StagedDocument = struct {
    allocator: Allocator,
    staged: default_app.Staged,
    /// The document's absolute path.
    user_path: []u8,
    /// The staged app's absolute path. The build knows the document's module
    /// by this path.
    staged_path: []u8,
    scratch: compile.artifacts.Scratch,
    user_lines: pos.LineOffsets,
    staged_lines: pos.LineOffsets,

    /// Errors from staging a document.
    pub const Error = Allocator.Error || error{DefaultAppStagingFailed};

    /// Stage `text`, the document at `user_path`, into a new scratch directory
    /// under the cache directory. Returns null when the document needs no
    /// default platform.
    pub fn create(
        allocator: Allocator,
        io: std.Io,
        fs: compile.CoreCtx,
        cache_config: compile.CacheConfig,
        user_path: []const u8,
        text: []const u8,
    ) Error!?*StagedDocument {
        const source_dir = std.fs.path.dirname(user_path) orelse ".";
        const result = try default_app.stage(allocator, source_dir, text, .checking, user_path);
        var staged = switch (result) {
            .unmodified => return null,
            .staged => |staged| staged,
            .invalid => unreachable, // stage reports nothing for .checking: parse errors and non-app roots come back .unmodified
        };
        errdefer staged.deinit(allocator);

        const cache_root = cache_config.getEffectiveCacheDir(allocator) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.NoHomeDirectory => return error.DefaultAppStagingFailed,
        };
        defer allocator.free(cache_root);
        var scratch = compile.artifacts.Scratch.create(allocator, io, cache_root) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.IoFailure => return error.DefaultAppStagingFailed,
        };
        errdefer scratch.deinit();

        const staged_path = default_app.writeCheckSources(allocator, fs, scratch.path(), user_path, &staged) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return error.DefaultAppStagingFailed,
        };
        errdefer allocator.free(staged_path);

        const owned_user_path = try allocator.dupe(u8, user_path);
        errdefer allocator.free(owned_user_path);

        const self = try allocator.create(StagedDocument);
        errdefer allocator.destroy(self);
        self.* = .{
            .allocator = allocator,
            .staged = staged,
            .user_path = owned_user_path,
            .staged_path = staged_path,
            .scratch = scratch,
            .user_lines = undefined,
            .staged_lines = undefined,
        };
        self.user_lines = try pos.LineOffsets.init(allocator, self.staged.original_source);
        errdefer self.user_lines.deinit();
        self.staged_lines = try pos.LineOffsets.init(allocator, self.staged.synthetic_source);
        return self;
    }

    pub fn destroy(self: *StagedDocument) void {
        const allocator = self.allocator;
        self.staged_lines.deinit();
        self.user_lines.deinit();
        self.scratch.deinit();
        allocator.free(self.staged_path);
        allocator.free(self.user_path);
        self.staged.deinit(allocator);
        allocator.destroy(self);
    }

    /// Point the build's reports at the document instead of the staged app,
    /// and resolve the document's imports from the document's directory.
    /// Both are what `roc check` sets for a staged app.
    pub fn configure(self: *const StagedDocument, env: *compile.BuildEnv) void {
        env.setRootSourceDirOverride(std.fs.path.dirname(self.user_path) orelse ".");
        env.setSyntheticRootSourceMappingWithLineOffset(
            self.user_path,
            self.staged.original_source,
            self.staged.header_len,
            self.staged.header_lines,
        );
    }

    /// The module path that stands for `path`: the staged app's path for the
    /// document, and `path` itself for any other file.
    pub fn modulePath(self: *const StagedDocument, path: []const u8) []const u8 {
        return if (std.mem.eql(u8, path, self.user_path)) self.staged_path else path;
    }

    /// The staged offset of an offset in the document's current text, which
    /// may differ from the text this staging was made from. Completion reads
    /// a module built from earlier text with offsets in the current text, as
    /// it does for every document; the body moves by the same amount in
    /// either text. Null in a header that staging rewrote.
    pub fn editedTextOffset(self: *const StagedDocument, offset: u32) ?u32 {
        if (offset >= self.staged.body_start) return @intCast(offset + self.staged.header_len);
        return if (self.staged.prefix_verbatim) offset else null;
    }
};
