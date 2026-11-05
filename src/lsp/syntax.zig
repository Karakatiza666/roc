//! Syntax checking integration that runs the Roc compiler and converts
//! reports to LSP diagnostics.

const std = @import("std");
const builtin = @import("builtin");
const compile = @import("compile");
const reporting = @import("reporting");
const build_options = @import("build_options");
const CoreCtx = @import("ctx").CoreCtx;
const Allocator = std.mem.Allocator;
const base = @import("base");
const can = @import("can");
const eval = @import("eval");
const types = @import("types");

const Diagnostics = @import("diagnostics.zig");
const uri_util = @import("uri.zig");
const compiled_builtins = @import("compiled_builtins");
const scope_map = @import("scope_map.zig");
const BuildSession = @import("build_session.zig").BuildSession;
const cir_queries = @import("cir_queries.zig");
const module_lookup = @import("module_lookup.zig");
const module_envs = @import("module_envs.zig");
const lookup_target = @import("lookup_target.zig");
const anno_targets = @import("anno_targets.zig");
const hover = @import("hover.zig");
const completion_context = @import("completion/context.zig");
const completion_builtins = @import("completion/builtins.zig");
const completion_builder = @import("completion/builder.zig");
const BuildEnvHandle = @import("build_env_handle.zig").BuildEnvHandle;
const DocumentView = @import("document_view.zig").DocumentView;
const document_view = @import("document_view.zig");
const report_diagnostics = @import("report_diagnostics.zig");
const rename_rules = @import("rename.zig");
const code_action = @import("code_action.zig");

const BuildEnv = compile.BuildEnv;
const CacheManager = compile.CacheManager;
const roc_target = @import("roc_target");
const CacheConfig = compile.CacheConfig;
const ModuleEnv = can.ModuleEnv;
const CIR = can.CIR;
const Region = base.Region;

pub const DebugFlags = @import("debug.zig").DebugFlags;

/// Errors that can occur while preparing the syntax check build environment.
pub const SyntaxBuildEnvError = Allocator.Error || std.Io.Dir.RealPathFileAllocError || eval.BuiltinModules.InitError || BuildSession.InitError;
/// Errors that can occur while preparing a document for syntax checking.
pub const SyntaxPrepareDocumentError = SyntaxBuildEnvError;
/// Errors that can occur while checking syntax for a document.
pub const SyntaxCheckError = SyntaxPrepareDocumentError || error{WriteFailed};
/// Errors that can occur while answering syntax-backed LSP queries.
pub const SyntaxQueryError = SyntaxPrepareDocumentError || error{WriteFailed};

/// The name of a failed syntax query, for request handlers that log it and
/// answer the client with an empty result. Allocation failure propagates instead.
pub fn queryFailureName(err: SyntaxQueryError) Allocator.Error![]const u8 {
    return switch (err) {
        error.OutOfMemory => error.OutOfMemory,
        error.AccessDenied,
        error.AntivirusInterference,
        error.BadPathName,
        error.BuiltinArtifactVersionMismatch,
        error.Canceled,
        error.CorruptArtifact,
        error.CorruptBuiltinArtifact,
        error.CorruptEmbeddedBuiltins,
        error.DefaultAppStagingFailed,
        error.DeviceBusy,
        error.FileBusy,
        error.FileNotFound,
        error.FileSystem,
        error.FileTooBig,
        error.InputOutput,
        error.IsDir,
        error.NameTooLong,
        error.NetworkNotFound,
        error.NoDevice,
        error.NoSpaceLeft,
        error.NotDir,
        error.OperationUnsupported,
        error.PathAlreadyExists,
        error.PermissionDenied,
        error.PipeBusy,
        error.ProcessFdQuotaExceeded,
        error.StaleEmbeddedBuiltins,
        error.SymLinkLoop,
        error.SystemFdQuotaExceeded,
        error.SystemResources,
        error.Unexpected,
        error.UnrecognizedVolume,
        error.WriteFailed,
        => |other| @errorName(other),
    };
}

/// Unwraps `result`; on allocation failure records it in `oom` and yields
/// null, for queries that report "nothing found" as null.
/// Blake3 hash of a document's text, identifying the content a build saw.
fn contentHash(text: []const u8) [32]u8 {
    var hash: [32]u8 = undefined;
    std.crypto.hash.Blake3.hash(text, &hash, .{});
    return hash;
}

fn noteOom(oom: *?Allocator.Error, result: anytype) ?@typeInfo(@TypeOf(result)).error_union.payload {
    return result catch |err| {
        oom.* = err;
        return null;
    };
}

/// Runs BuildEnv-backed syntax/type checks and converts reports to LSP diagnostics.
pub const SyntaxChecker = struct {
    allocator: std.mem.Allocator,
    std_io: std.Io,
    mutex: std.Io.Mutex = std.Io.Mutex.init,
    /// Current build environment owned by the live check path.
    build_env: ?*BuildEnvHandle = null,
    /// Previous successful BuildEnv kept for module lookups (e.g., semantic tokens).
    /// This is swapped with build_env after each successful build.
    previous_build_env: ?*BuildEnvHandle = null,
    /// Snapshot of the most recent successful build per module (kept for completions).
    snapshot_envs: std.StringHashMapUnmanaged(*BuildEnvHandle) = .{},
    /// Pre-published Builtin module reused by each fresh LSP BuildEnv.
    builtin_modules: ?*eval.BuiltinModules = null,
    /// Content hash of the last text built for each absolute document path,
    /// used to skip rebuilding unchanged documents. Keys are owned.
    content_hashes: std.StringHashMapUnmanaged([32]u8) = .{},
    /// Absolute workspace root from LSP initialize (`rootUri`), used to prefer
    /// `{workspace_root}/main.roc` for package-alias resolution.
    workspace_root: ?[]u8 = null,
    /// URIs for which we last published a non-empty diagnostic set. Used to
    /// emit empty clears when those diagnostics are no longer valid.
    published_diagnostic_uris: std.StringHashMapUnmanaged(void) = .{},
    /// Each checked URI of an open document, exactly as the client spelled it,
    /// mapped to the absolute path the build knows that document's module by.
    /// Diagnostics and locations for a path go to the client under these URIs:
    /// a URI rebuilt from the path can spell the same file differently (percent
    /// encoding, drive-letter case, a symlinked directory), and the client keys
    /// its documents by the exact string. Kept in check order, so the URI a
    /// location query picks for a file open under several URIs is deterministic.
    /// Keys and values are owned.
    client_document_paths: std.StringArrayHashMapUnmanaged([]u8) = .empty,
    cache_config: CacheConfig,
    log_file: ?std.Io.File = null,
    debug: DebugFlags,
    /// Whether the client accepts diagnostics with related information. Set
    /// from its `initialize` capabilities.
    related_information: bool = false,

    // Owner tags used for BuildEnvHandle debugging.
    const owner_build = "build_env";
    const owner_previous = "previous_build_env";
    const owner_snapshot = "snapshot";
    const owner_semantic_tokens = "semantic_tokens";
    pub const CheckError = SyntaxCheckError;
    pub const QueryError = SyntaxQueryError;

    const DocumentIdentity = struct {
        absolute_path: [:0]u8,
        content_hash: [32]u8,

        fn deinit(self: *DocumentIdentity, allocator: Allocator) void {
            allocator.free(self.absolute_path);
        }
    };

    const DocumentBuild = struct {
        checker: *SyntaxChecker,
        identity: ?DocumentIdentity,
        session: ?BuildSession,
        handle: *BuildEnvHandle,
        env: *BuildEnv,
        absolute_path: []const u8,
        build_succeeded: bool,
        has_reports: bool,
        reused: bool,

        fn deinit(self: *DocumentBuild) void {
            if (self.session) |*session| {
                session.deinit();
            }
            if (self.identity) |*identity| {
                identity.deinit(self.checker.allocator);
            }
            self.checker.allocator.free(self.absolute_path);
        }

        fn getModuleEnv(self: *DocumentBuild) ?*ModuleEnv {
            if (self.reused) {
                return self.checker.getModuleEnvByPathInEnv(self.handle, self.absolute_path);
            }
            if (self.session) |*s| {
                return s.getModuleEnv();
            }
            return null;
        }

        /// The path the build knows the document's module by. A staged
        /// document's module has the staged app's path.
        fn modulePath(self: *const DocumentBuild) []const u8 {
            return self.handle.modulePath(self.absolute_path);
        }

        /// The view that converts between the document and `module_env`, the
        /// document's module in this build.
        fn view(self: *const DocumentBuild, module_env: *ModuleEnv) DocumentView {
            return .{ .module_env = module_env, .staged = self.handle.staged_document };
        }

        /// The context that resolves references of `module_env`, the
        /// document's module in this build.
        fn lookupContext(self: *const DocumentBuild, env: *BuildEnv, module_env: *ModuleEnv) lookup_target.Context {
            return .{ .build_env = env, .module_env = module_env, .module_path = self.modulePath() };
        }
    };

    fn isCompilerOwnedBuiltin(self: *const SyntaxChecker, path: []const u8) bool {
        const filename = std.fs.path.basename(path);
        if (!std.mem.eql(u8, filename, "Builtin.roc")) return false;
        if (self.cache_config.getModuleCacheDir(self.allocator)) |cache_dir| {
            defer self.allocator.free(cache_dir);
            const builtin_cache_path = std.fs.path.join(self.allocator, &.{ cache_dir, "Builtin.roc" }) catch return false;
            defer self.allocator.free(builtin_cache_path);
            return std.mem.eql(u8, path, builtin_cache_path);
        } else |_| {}
        return false;
    }

    pub fn init(allocator: std.mem.Allocator, std_io: std.Io, debug: DebugFlags, log_file: ?std.Io.File) SyntaxChecker {
        var cache_config = CacheConfig{ .roc_ctx = CoreCtx.default(allocator, allocator, std_io) };
        if (builtin.is_test) {
            cache_config.enabled = false;
        }

        return .{
            .allocator = allocator,
            .std_io = std_io,
            .cache_config = cache_config,
            .debug = debug,
            .log_file = log_file,
        };
    }

    pub fn deinit(self: *SyntaxChecker) void {
        // Release live handles first, then snapshots.
        // Handles guarantee the BuildEnv is freed exactly once.
        if (self.build_env) |handle| {
            handle.release(owner_build);
            self.build_env = null;
        }
        if (self.previous_build_env) |handle| {
            handle.release(owner_previous);
            self.previous_build_env = null;
        }

        self.clearSnapshots();

        // Free hashmap allocations
        self.snapshot_envs.deinit(self.allocator);

        if (self.workspace_root) |root| {
            self.allocator.free(root);
            self.workspace_root = null;
        }
        self.clearPublishedDiagnosticUris();
        self.published_diagnostic_uris.deinit(self.allocator);

        for (self.client_document_paths.keys(), self.client_document_paths.values()) |uri, path| {
            self.allocator.free(uri);
            self.allocator.free(path);
        }
        self.client_document_paths.deinit(self.allocator);

        if (self.builtin_modules) |builtin_modules| {
            builtin_modules.deinit();
            self.allocator.destroy(builtin_modules);
            self.builtin_modules = null;
        }

        var hash_keys = self.content_hashes.keyIterator();
        while (hash_keys.next()) |key| self.allocator.free(key.*);
        self.content_hashes.deinit(self.allocator);
    }

    fn clearPublishedDiagnosticUris(self: *SyntaxChecker) void {
        var it = self.published_diagnostic_uris.keyIterator();
        while (it.next()) |key| {
            self.allocator.free(key.*);
        }
        self.published_diagnostic_uris.clearRetainingCapacity();
    }

    /// Test helper: record a URI as having published non-empty diagnostics.
    ///
    /// Not gated on `builtin.is_test` (unlike `getDocumentForTesting` in server.zig):
    /// the LSP integration harness runs as a plain executable (`addExecutable`, not
    /// `addTest`), so `builtin.is_test` is false there and such a guard would make
    /// this helper silently inert for the integration specs that rely on it.
    pub fn seedPublishedDiagnosticUriForTesting(self: *SyntaxChecker, uri: []const u8) Allocator.Error!void {
        const owned = try self.allocator.dupe(u8, uri);
        const gop = try self.published_diagnostic_uris.getOrPut(self.allocator, owned);
        if (gop.found_existing) self.allocator.free(owned);
    }

    /// Test helper: whether a URI is tracked as having published non-empty diagnostics.
    /// See `seedPublishedDiagnosticUriForTesting` for why this isn't gated on `builtin.is_test`.
    pub fn hasPublishedDiagnosticUriForTesting(self: *SyntaxChecker, uri: []const u8) bool {
        return self.published_diagnostic_uris.contains(uri);
    }

    /// Forget a document the client closed. Its URI no longer names its file, so
    /// diagnostics and locations for that file go to a URI built from the path.
    pub fn closeDocument(self: *SyntaxChecker, uri: []const u8) void {
        self.mutex.lockUncancelable(self.std_io);
        defer self.mutex.unlock(self.std_io);

        const removed = self.client_document_paths.fetchOrderedRemove(uri) orelse return;
        self.allocator.free(removed.key);
        self.allocator.free(removed.value);
    }

    /// Record that the client names the document at `absolute_path` by `uri`.
    fn recordClientDocument(self: *SyntaxChecker, uri: []const u8, absolute_path: []const u8) Allocator.Error!void {
        if (self.client_document_paths.getPtr(uri)) |path| {
            if (std.mem.eql(u8, path.*, absolute_path)) return;
            const owned_path = try self.allocator.dupe(u8, absolute_path);
            self.allocator.free(path.*);
            path.* = owned_path;
            return;
        }

        const owned_uri = try self.allocator.dupe(u8, uri);
        errdefer self.allocator.free(owned_uri);
        const owned_path = try self.allocator.dupe(u8, absolute_path);
        errdefer self.allocator.free(owned_path);
        try self.client_document_paths.put(self.allocator, owned_uri, owned_path);
    }

    /// The URI to give the client for the file at `absolute_path`: the first URI
    /// the client opened it under, or one built from the path when it isn't open.
    fn uriForPath(self: *const SyntaxChecker, absolute_path: []const u8) Allocator.Error![]u8 {
        return uri_util.clientUriForPath(self.allocator, &self.client_document_paths, absolute_path);
    }

    /// Append a publish of `diagnostics` for every URI the client opened the
    /// file at `absolute_path` under, or for a URI built from the path when it
    /// isn't open. Takes ownership of `diagnostics`.
    fn appendPathPublishes(
        self: *SyntaxChecker,
        publish_list: *std.ArrayList(Diagnostics.PublishDiagnostics),
        absolute_path: []const u8,
        diagnostics: []Diagnostics.Diagnostic,
    ) Allocator.Error!void {
        errdefer Diagnostics.freeAll(self.allocator, diagnostics);

        // `diagnostics` itself goes to the first URI; every later URI gets a copy.
        var first_uri: ?[]const u8 = null;
        for (self.client_document_paths.keys(), self.client_document_paths.values()) |uri, path| {
            if (!std.mem.eql(u8, path, absolute_path)) continue;
            if (first_uri == null) {
                first_uri = uri;
                continue;
            }
            const copy = try Diagnostics.cloneAll(self.allocator, diagnostics);
            errdefer Diagnostics.freeAll(self.allocator, copy);
            const owned_uri = try self.allocator.dupe(u8, uri);
            errdefer self.allocator.free(owned_uri);
            try publish_list.append(self.allocator, .{ .uri = owned_uri, .diagnostics = copy });
        }

        const uri = if (first_uri) |client_uri|
            try self.allocator.dupe(u8, client_uri)
        else
            try uri_util.pathToUri(self.allocator, absolute_path);
        errdefer self.allocator.free(uri);
        try publish_list.append(self.allocator, .{ .uri = uri, .diagnostics = diagnostics });
    }

    fn updateWorkspaceRoot(self: *SyntaxChecker, workspace_root: ?[]const u8) Allocator.Error!void {
        if (self.workspace_root) |old| {
            self.allocator.free(old);
            self.workspace_root = null;
        }
        if (workspace_root) |root| {
            self.workspace_root = try self.allocator.dupe(u8, root);
        }
    }

    fn documentIdentityFromText(self: *SyntaxChecker, uri: []const u8, text: []const u8) std.mem.Allocator.Error!DocumentIdentity {
        const path = try uri_util.uriToPath(self.allocator, uri);
        defer self.allocator.free(path);

        const absolute_path: [:0]u8 = std.Io.Dir.cwd().realPathFileAlloc(self.std_io, path, self.allocator) catch
            try self.allocator.dupeSentinel(u8, path, 0);

        return .{
            .absolute_path = absolute_path,
            .content_hash = contentHash(text),
        };
    }

    fn matchingBuildEnvHandle(self: *SyntaxChecker, absolute_path: []const u8, content_hash: [32]u8) ?*BuildEnvHandle {
        if (self.build_env) |handle| {
            if (handle.matchesDocumentContent(absolute_path, content_hash)) {
                return handle;
            }
        }

        if (self.snapshot_envs.get(absolute_path)) |handle| {
            if (handle.matchesDocumentContent(absolute_path, content_hash)) {
                return handle;
            }
        }

        if (self.previous_build_env) |handle| {
            if (handle.matchesDocumentContent(absolute_path, content_hash)) {
                return handle;
            }
        }

        return null;
    }

    fn documentHasReports(_: *SyntaxChecker, absolute_path: []const u8, drained_reports: ?[]BuildEnv.DrainedModuleReports) bool {
        const drained = drained_reports orelse return true;
        for (drained) |entry| {
            if (std.mem.eql(u8, entry.abs_path, absolute_path) and entry.reports.len > 0) {
                return true;
            }
        }
        return false;
    }

    fn prepareDocumentBuild(self: *SyntaxChecker, uri: []const u8, override_text: ?[]const u8) SyntaxPrepareDocumentError!DocumentBuild {
        var identity: ?DocumentIdentity = if (override_text) |text|
            try self.documentIdentityFromText(uri, text)
        else
            null;
        errdefer if (identity) |*document| document.deinit(self.allocator);

        if (identity) |document| {
            if (self.matchingBuildEnvHandle(document.absolute_path, document.content_hash)) |handle| {
                const env = handle.envPtr();
                const abs_path = try self.allocator.dupe(u8, document.absolute_path);
                return .{
                    .checker = self,
                    .identity = identity,
                    .session = null,
                    .handle = handle,
                    .env = env,
                    .absolute_path = abs_path,
                    .build_succeeded = documentParsedCleanly(handle, document.absolute_path),
                    .has_reports = handle.hasDocumentReports(),
                    .reused = true,
                };
            }
        }

        const path = try uri_util.uriToPath(self.allocator, uri);
        defer self.allocator.free(path);

        if (self.isCompilerOwnedBuiltin(path)) {
            const env_handle = try self.createFreshBuildEnv();
            const env = env_handle.envPtr();
            const abs_path = try self.allocator.dupe(u8, path);
            return .{
                .checker = self,
                .identity = identity,
                .session = null,
                .handle = env_handle,
                .env = env,
                .absolute_path = abs_path,
                .build_succeeded = false,
                .has_reports = false,
                .reused = false,
            };
        }

        const env_handle = try self.createFreshBuildEnv();
        const env = env_handle.envPtr();

        var session = try BuildSession.init(self.allocator, self.std_io, env_handle, uri, override_text, self.workspace_root, self.cache_config);
        errdefer session.deinit();

        const has_reports = self.documentHasReports(session.absolute_path, session.drained_reports);

        if (identity) |document| {
            env_handle.setDocumentContent(document.absolute_path, document.content_hash, has_reports) catch |err| {
                self.logDebug(.build, "Failed to record document content: {s}", .{@errorName(err)});
            };
        }

        const abs_path = try self.allocator.dupe(u8, session.absolute_path);
        return .{
            .checker = self,
            .identity = identity,
            .session = session,
            .handle = env_handle,
            .env = env,
            .absolute_path = abs_path,
            .build_succeeded = session.build_succeeded and documentParsedCleanly(env_handle, session.absolute_path),
            .has_reports = has_reports,
            .reused = false,
        };
    }

    /// Check the file referenced by the URI and return diagnostics grouped by URI.
    /// The absolute path of an existing file, or null when it cannot be
    /// resolved.
    fn realAbsolutePath(self: *SyntaxChecker, path: []const u8) std.mem.Allocator.Error!?[:0]u8 {
        return std.Io.Dir.cwd().realPathFileAlloc(self.std_io, path, self.allocator) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.AccessDenied,
            error.AntivirusInterference,
            error.BadPathName,
            error.Canceled,
            error.DeviceBusy,
            error.FileBusy,
            error.FileNotFound,
            error.FileSystem,
            error.FileTooBig,
            error.InputOutput,
            error.IsDir,
            error.NameTooLong,
            error.NetworkNotFound,
            error.NoDevice,
            error.NoSpaceLeft,
            error.NotDir,
            error.OperationUnsupported,
            error.PathAlreadyExists,
            error.PermissionDenied,
            error.PipeBusy,
            error.ProcessFdQuotaExceeded,
            error.SymLinkLoop,
            error.SystemFdQuotaExceeded,
            error.SystemResources,
            error.Unexpected,
            error.UnrecognizedVolume,
            => null,
        };
    }

    /// Drop what was kept for a document the client closed: its last-built
    /// content hash and its completion snapshot, which holds a whole build.
    pub fn forget(self: *SyntaxChecker, uri: []const u8) std.mem.Allocator.Error!void {
        self.mutex.lockUncancelable(self.std_io);
        defer self.mutex.unlock(self.std_io);

        const path = try uri_util.uriToPath(self.allocator, uri);
        defer self.allocator.free(path);
        const abs_path = try self.realAbsolutePath(path);
        defer if (abs_path) |a| self.allocator.free(a);
        const key: []const u8 = abs_path orelse path;

        if (self.content_hashes.fetchRemove(key)) |removed| self.allocator.free(removed.key);
        if (self.snapshot_envs.fetchRemove(key)) |removed| {
            removed.value.release(owner_snapshot);
            self.allocator.free(removed.key);
        }
    }

    /// Check the document and return the diagnostics to publish, grouped by
    /// URI. Once `cancel_request` is set the build is abandoned and this
    /// returns `error.Canceled`, leaving every retained build, content hash,
    /// and published-URI record as it was before the call.
    pub fn check(
        self: *SyntaxChecker,
        uri: []const u8,
        override_text: ?[]const u8,
        workspace_root: ?[]const u8,
        cancel_request: ?*const std.atomic.Value(bool),
    ) CheckError![]Diagnostics.PublishDiagnostics {
        self.mutex.lockUncancelable(self.std_io);
        defer self.mutex.unlock(self.std_io);

        try self.updateWorkspaceRoot(workspace_root);

        const check_path = try uri_util.uriToPath(self.allocator, uri);
        defer self.allocator.free(check_path);

        if (self.isCompilerOwnedBuiltin(check_path)) {
            return try self.allocator.alloc(Diagnostics.PublishDiagnostics, 0);
        }

        // Check if content has changed using hash comparison BEFORE building.
        // This avoids unnecessary rebuilds on focus/blur events. The new hash
        // is recorded only once the build completes, so a canceled build
        // never makes the next check of the same text skip.
        var hashed_path: ?[:0]u8 = null;
        defer if (hashed_path) |a| self.allocator.free(a);
        if (override_text) |text| {
            const path = try uri_util.uriToPath(self.allocator, uri);
            defer self.allocator.free(path);

            hashed_path = try self.realAbsolutePath(path);

            if (hashed_path) |ap| {
                const new_hash = contentHash(text);
                const old_hash = self.content_hashes.get(ap);

                if (old_hash) |existing| {
                    // A URI not yet checked has never been sent this document's
                    // diagnostics, so it needs a build even for unchanged text.
                    if (std.mem.eql(u8, &existing, &new_hash) and self.client_document_paths.contains(uri)) {
                        self.logDebug(.build, "[INCREMENTAL] SKIP rebuild for {s}: content hash unchanged ({x}...)", .{
                            ap,
                            new_hash[0..4].*,
                        });
                        return &[_]Diagnostics.PublishDiagnostics{};
                    }
                    self.logDebug(.build, "[INCREMENTAL] REBUILD {s}: content hash changed ({x}... -> {x}...)", .{
                        ap,
                        existing[0..4].*,
                        new_hash[0..4].*,
                    });
                } else {
                    self.logDebug(.build, "[INCREMENTAL] INITIAL build for {s}: no previous hash (new hash: {x}...)", .{
                        ap,
                        new_hash[0..4].*,
                    });
                }
            }
        }

        const env_handle = try self.createBuildEnv();
        var env_handle_installed = false;
        errdefer if (!env_handle_installed) env_handle.release(owner_build);
        const env = env_handle.envPtr();
        env.setCancelRequest(cancel_request);

        var session = try BuildSession.init(self.allocator, self.std_io, env_handle, uri, override_text, self.workspace_root, self.cache_config);
        defer session.deinit();
        // The flag is reused for later checks, which this build, once
        // retained for queries, must not observe.
        env.setCancelRequest(null);

        self.installBuildEnv(env_handle);
        env_handle_installed = true;
        if (hashed_path) |ap| {
            const entry = try self.content_hashes.getOrPut(self.allocator, ap);
            if (!entry.found_existing) {
                entry.key_ptr.* = self.allocator.dupe(u8, ap) catch |err| {
                    self.content_hashes.removeByPtr(entry.key_ptr);
                    return err;
                };
            }
            entry.value_ptr.* = contentHash(override_text.?);
        }

        const absolute_path = session.absolute_path;
        try self.recordClientDocument(uri, absolute_path);

        if (override_text) |text| {
            env_handle.setDocumentContent(absolute_path, contentHash(text), self.documentHasReports(absolute_path, session.drained_reports)) catch |err| {
                self.logDebug(.build, "Failed to record document content: {s}", .{@errorName(err)});
            };
        }

        var publish_list: std.ArrayList(Diagnostics.PublishDiagnostics) = .empty;
        errdefer {
            for (publish_list.items) |*set| set.deinit(self.allocator);
            publish_list.deinit(self.allocator);
        }
        if (session.drained_reports) |drained_reports| {
            // if the build succeeded, consider snapshotting the BuildEnv for completions
            if (self.shouldSnapshotBuild(env_handle, session.absolute_path, drained_reports)) {
                try self.storeSnapshotEnv(env_handle, session.absolute_path);
            }
            const converter: report_diagnostics.Converter = .{
                .allocator = self.allocator,
                .handle = env_handle,
                .client_paths = &self.client_document_paths,
                .related_information = self.related_information,
            };
            for (drained_reports) |entry| {
                const mapped_path = if (entry.abs_path.len == 0) session.absolute_path else entry.abs_path;

                var diags: std.ArrayList(Diagnostics.Diagnostic) = .empty;
                errdefer {
                    for (diags.items) |diag| diag.deinit(self.allocator);
                    diags.deinit(self.allocator);
                }

                for (entry.reports) |*rep| {
                    const report = rep.*;
                    //we don't deinit here because BuildSession will free later

                    if (report_diagnostics.shouldSuppress(report)) continue;

                    self.logDebug(.syntax, "report: {s}", .{report.title});
                    const diag = try converter.diagnostic(report);
                    try diags.append(self.allocator, diag);
                }
                //we also don't don't deinit the entries because buildSession will free them
                //self.allocator.free(entry.reports);

                try self.appendPathPublishes(&publish_list, mapped_path, try diags.toOwnedSlice(self.allocator));
            }

            if (publish_list.items.len == 0) {
                try publish_list.append(self.allocator, .{
                    .uri = try self.allocator.dupe(u8, uri),
                    .diagnostics = &.{},
                });
            }

            try self.finishDiagnosticPublishes(&publish_list, uri);
            return publish_list.toOwnedSlice(self.allocator);
        } else {
            // No reports drained, return a diagnostic showing the failure to get diagnostics
            try publish_list.append(self.allocator, .{
                .uri = try self.allocator.dupe(u8, uri),
                .diagnostics = try self.allocator.dupe(Diagnostics.Diagnostic, &.{
                    .{
                        .range = .{
                            .start = .{ .line = 0, .character = 0 },
                            .end = .{ .line = 0, .character = 1 },
                        },
                        .severity = reporting.Severity.fatal.toLspSeverity(),
                        .source = "roc",
                        .message = try std.fmt.allocPrint(self.allocator, "Failed to retrieve diagnostics for {s}", .{absolute_path}),
                    },
                }),
            });
            try self.finishDiagnosticPublishes(&publish_list, uri);
            return publish_list.toOwnedSlice(self.allocator);
        }
    }

    fn publishListContainsUri(publish_list: *const std.ArrayList(Diagnostics.PublishDiagnostics), uri: []const u8) bool {
        for (publish_list.items) |set| {
            if (std.mem.eql(u8, set.uri, uri)) return true;
        }
        return false;
    }

    fn publishListHasDiagnostics(publish_list: *const std.ArrayList(Diagnostics.PublishDiagnostics), uri: []const u8) bool {
        for (publish_list.items) |set| {
            if (set.diagnostics.len > 0 and std.mem.eql(u8, set.uri, uri)) return true;
        }
        return false;
    }

    /// Ensure the checked URI is published, clear stale URIs from prior publishes,
    /// and refresh the set of URIs that currently have non-empty diagnostics.
    fn finishDiagnosticPublishes(
        self: *SyntaxChecker,
        publish_list: *std.ArrayList(Diagnostics.PublishDiagnostics),
        checked_uri: []const u8,
    ) Allocator.Error!void {
        if (!publishListContainsUri(publish_list, checked_uri)) {
            try publish_list.append(self.allocator, .{
                .uri = try self.allocator.dupe(u8, checked_uri),
                .diagnostics = &.{},
            });
        }

        // Every URI that had diagnostics last time and is not published now
        // gets an empty set, which clears it in the editor.
        var it = self.published_diagnostic_uris.keyIterator();
        while (it.next()) |prev| {
            if (!publishListContainsUri(publish_list, prev.*)) {
                const stale_uri = try self.allocator.dupe(u8, prev.*);
                errdefer self.allocator.free(stale_uri);
                try publish_list.append(self.allocator, .{
                    .uri = stale_uri,
                    .diagnostics = &.{},
                });
            }
        }

        // Keep the URIs that still have diagnostics, so a document whose
        // errors persist across edits keeps its owned key.
        var keys = self.published_diagnostic_uris.keyIterator();
        while (keys.next()) |key| {
            if (publishListHasDiagnostics(publish_list, key.*)) continue;
            const owned = key.*;
            self.published_diagnostic_uris.removeByPtr(key);
            self.allocator.free(owned);
        }
        for (publish_list.items) |set| {
            if (set.diagnostics.len == 0) continue;
            const gop = try self.published_diagnostic_uris.getOrPut(self.allocator, set.uri);
            if (gop.found_existing) continue;
            gop.key_ptr.* = self.allocator.dupe(u8, set.uri) catch |err| {
                self.published_diagnostic_uris.removeByPtr(gop.key_ptr);
                return err;
            };
        }
    }

    /// Creates a fresh BuildEnv for a new build.
    /// The previous build_env is moved to previous_build_env for module lookups.
    fn createFreshBuildEnv(self: *SyntaxChecker) SyntaxBuildEnvError!*BuildEnvHandle {
        const handle = try self.createBuildEnv();
        self.installBuildEnv(handle);
        return handle;
    }

    /// Make `handle`, created by `createBuildEnv`, the current build_env.
    /// The current one becomes previous_build_env for module lookups.
    fn installBuildEnv(self: *SyntaxChecker, handle: *BuildEnvHandle) void {
        if (self.previous_build_env) |old_prev| {
            old_prev.release(owner_previous);
            self.previous_build_env = null;
        }

        // Move build_env to previous_build_env, transferring ownership tag.
        if (self.build_env) |current| {
            current.retain(owner_previous);
            current.release(owner_build);
            self.previous_build_env = current;
        }
        self.build_env = handle;
    }

    /// Create a fresh BuildEnv owned under `owner_build` but not yet
    /// installed. previous_build_env is released first, since installing
    /// the new one replaces it, so at most two builds are retained while
    /// this one runs.
    fn createBuildEnv(self: *SyntaxChecker) SyntaxBuildEnvError!*BuildEnvHandle {
        self.logDebug(.build, "createBuildEnv: prev_build_env={any} build_env={any}", .{ self.previous_build_env != null, self.build_env != null });

        if (self.previous_build_env) |old_prev| {
            old_prev.release(owner_previous);
            self.previous_build_env = null;
        }

        // Create a fresh BuildEnv. The LSP reuses one pre-published Builtin
        // across checks; each BuildEnv borrows it and never deinitializes it.
        const cwd = try std.Io.Dir.cwd().realPathFileAlloc(self.std_io, ".", self.allocator);
        errdefer self.allocator.free(cwd);
        const builtin_modules = try self.sharedBuiltinModules();
        var env = BuildEnv.initBorrowingBuiltinModules(
            self.allocator,
            .single_threaded,
            1,
            roc_target.RocTarget.detectNative(),
            cwd,
            self.std_io,
            builtin_modules,
        );
        errdefer env.deinit();
        env.compiler_version = build_options.compiler_compatibility_id;
        env.source_pin_version = @import("compiler_version").compiler_version;
        env.setFinalizeExecutableArtifacts(false);

        if (self.cache_config.enabled) {
            const cache_manager = try self.allocator.create(CacheManager);
            cache_manager.* = CacheManager.init(self.allocator, self.cache_config, CoreCtx.default(self.allocator, self.allocator, self.std_io));
            env.setCacheManager(cache_manager);
        }

        const debug_handles = self.debug.build or self.debug.syntax or self.debug.server;
        return BuildEnvHandle.create(self.allocator, env, cwd, owner_build, debug_handles);
    }

    fn sharedBuiltinModules(self: *SyntaxChecker) (Allocator.Error || eval.BuiltinModules.InitError)!*eval.BuiltinModules {
        if (self.builtin_modules) |builtin_modules| return builtin_modules;

        const builtin_modules = try self.allocator.create(eval.BuiltinModules);
        errdefer self.allocator.destroy(builtin_modules);

        builtin_modules.* = try eval.BuiltinModules.init(self.allocator);
        self.builtin_modules = builtin_modules;
        return builtin_modules;
    }

    fn shouldSnapshotBuild(self: *SyntaxChecker, handle: *BuildEnvHandle, absolute_path: []const u8, drained: []BuildEnv.DrainedModuleReports) bool {
        // Check if module was processed - if not, don't snapshot
        if (self.getModuleEnvByPathInEnv(handle, absolute_path) == null) {
            return false;
        }

        // Check for any error-level reports for this file - warnings/info are OK to snapshot
        for (drained) |entry| {
            if (std.mem.eql(u8, entry.abs_path, absolute_path)) {
                for (entry.reports) |report| {
                    if (report.severity.isError()) return false;
                }
            }
        }

        // Module processed with no reports → snapshot
        return true;
    }

    fn storeSnapshotEnv(self: *SyntaxChecker, env_handle: *BuildEnvHandle, absolute_path: []const u8) std.mem.Allocator.Error!void {
        self.logDebug(.completion, "storeSnapshotEnv: path={s}", .{absolute_path});
        if (self.snapshot_envs.fetchRemove(absolute_path)) |removed| {
            self.logDebug(.completion, "storeSnapshotEnv: replacing existing snapshot", .{});
            removed.value.release(owner_snapshot);
            self.allocator.free(removed.key);
        }

        const owned_path = try self.allocator.dupe(u8, absolute_path);
        self.snapshot_envs.put(self.allocator, owned_path, env_handle) catch |err| {
            self.allocator.free(owned_path);
            return err;
        };
        env_handle.retain(owner_snapshot);
        self.logDebug(.completion, "storeSnapshotEnv: stored snapshot count={d}", .{self.snapshot_envs.count()});
    }

    fn clearSnapshots(self: *SyntaxChecker) void {
        // Collect all handles and keys before clearing the map so we can
        // release snapshot ownership without mutating the map mid-iteration.
        const count = self.snapshot_envs.count();
        var envs: std.ArrayListUnmanaged(*BuildEnvHandle) = .empty;
        defer envs.deinit(self.allocator);
        var keys: std.ArrayListUnmanaged([]const u8) = .empty;
        defer keys.deinit(self.allocator);

        // Pre-reserve so the appends below cannot fail. If reserving fails we
        // fall back to releasing each entry as we iterate; this still avoids
        // leaking the handle refcount and key on OOM.
        const reserved = blk: {
            envs.ensureTotalCapacity(self.allocator, count) catch break :blk false;
            keys.ensureTotalCapacity(self.allocator, count) catch break :blk false;
            break :blk true;
        };

        if (!reserved) {
            // OOM path: release/free directly while iterating, then clear.
            var it = self.snapshot_envs.iterator();
            while (it.next()) |entry| {
                entry.value_ptr.*.release(owner_snapshot);
                self.allocator.free(entry.key_ptr.*);
            }
            self.snapshot_envs.clearRetainingCapacity();
            return;
        }

        var it = self.snapshot_envs.iterator();
        while (it.next()) |entry| {
            envs.appendAssumeCapacity(entry.value_ptr.*);
            keys.appendAssumeCapacity(entry.key_ptr.*);
        }

        // Clear the map FIRST so snapshot ownership is only represented by handles.
        self.snapshot_envs.clearRetainingCapacity();

        // Now release all handles (with empty snapshot_envs map)
        for (envs.items) |handle| {
            handle.release(owner_snapshot);
        }

        // Free all keys
        for (keys.items) |key| {
            self.allocator.free(key);
        }
    }

    /// Get the BuildEnv that should be used for module lookups (semantic tokens, etc.).
    /// Prefers the current build_env if it has modules, otherwise falls back to previous_build_env.
    pub fn getModuleLookupEnv(self: *SyntaxChecker) ?*BuildEnv {
        const handle = self.getModuleLookupHandle() orelse return null;
        return handle.envPtr();
    }

    /// The handle owning `getModuleLookupEnv`'s env.
    fn getModuleLookupHandle(self: *SyntaxChecker) ?*BuildEnvHandle {
        // Prefer current build_env if it exists and has modules
        if (self.build_env) |handle| {
            if (handle.envPtr().hasCompiledModules()) {
                return handle;
            }
        }
        // Fall back to previous_build_env
        return self.previous_build_env;
    }

    /// Get the cached snapshot BuildEnv for completions.
    /// Returns the first available snapshot env if any exist.
    pub fn getSnapshotEnv(self: *SyntaxChecker) ?*BuildEnv {
        var it = self.snapshot_envs.iterator();
        if (it.next()) |entry| {
            return entry.value_ptr.*.envPtr();
        }
        return null;
    }

    /// Look up a ModuleEnv by its file path from the cached BuildEnv.
    /// Returns null if no matching module is found.
    pub fn getModuleEnvByPath(self: *SyntaxChecker, path: []const u8) ?*ModuleEnv {
        const handle = self.getModuleLookupHandle() orelse return null;
        return self.getModuleEnvByPathInEnv(handle, path);
    }

    /// Return checked CIR only when a retained build was produced from these
    /// exact document bytes.
    pub const CheckedModule = struct {
        module_env: *ModuleEnv,
        handle: *BuildEnvHandle,

        pub fn deinit(self: CheckedModule) void {
            self.handle.release(owner_semantic_tokens);
        }

        /// The view that converts between the document and its module.
        pub fn view(self: CheckedModule) DocumentView {
            return .{ .module_env = self.module_env, .staged = self.handle.staged_document };
        }
    };

    pub fn getCheckedModuleForDocument(
        self: *SyntaxChecker,
        uri: []const u8,
        text: []const u8,
    ) Allocator.Error!?CheckedModule {
        self.mutex.lockUncancelable(self.std_io);
        defer self.mutex.unlock(self.std_io);

        var document = try self.documentIdentityFromText(uri, text);
        defer document.deinit(self.allocator);

        const handle = self.matchingBuildEnvHandle(document.absolute_path, document.content_hash) orelse return null;
        const module_env = self.getModuleEnvByPathInEnv(handle, document.absolute_path) orelse return null;
        handle.retain(owner_semantic_tokens);
        return .{ .module_env = module_env, .handle = handle };
    }

    /// Look up a ModuleEnv by its file path from a specific BuildEnv.
    /// Whether the document's module was built from a parse with no syntax
    /// errors. A module whose parse recovered past an error has a partial
    /// CIR, which handlers that rewrite the document must not answer from.
    fn documentParsedCleanly(handle: *BuildEnvHandle, path: []const u8) bool {
        const module_state = handle.envPtr().findModuleByPath(handle.modulePath(path)) orelse return false;
        return module_state.moduleEnv() != null and !module_state.has_syntax_errors;
    }

    fn getModuleEnvByPathInEnv(_: *SyntaxChecker, handle: *BuildEnvHandle, path: []const u8) ?*ModuleEnv {
        const module_state = handle.envPtr().findModuleByPath(handle.modulePath(path)) orelse return null;
        return module_state.moduleEnv();
    }

    fn logDebug(self: *SyntaxChecker, kind: enum { build, syntax, completion }, comptime fmt: []const u8, args: anytype) void {
        const enabled = switch (kind) {
            .build => self.debug.build,
            .syntax => self.debug.syntax,
            .completion => self.debug.completion,
        };
        if (!enabled) return;
        var log_file = self.log_file orelse return;
        var buffer: [256]u8 = undefined;
        const msg = std.fmt.bufPrint(&buffer, fmt, args) catch return;
        log_file.writeStreamingAll(self.std_io, msg) catch return;
        log_file.writeStreamingAll(self.std_io, "\n") catch {};
        log_file.sync(self.std_io) catch {};
    }

    /// Range in LSP coordinates
    // LspRange moved to cir_queries.zig
    pub const LspRange = cir_queries.LspRange;

    /// Result of a hover query containing type information
    pub const HoverResult = struct {
        type_str: []u8,
        range: ?LspRange,
    };

    /// Result of a definition query containing location information
    pub const DefinitionResult = struct {
        uri: []const u8,
        range: LspRange,
        origin_selection_range: ?LspRange = null,

        pub fn deinit(self: DefinitionResult, allocator: std.mem.Allocator) void {
            allocator.free(self.uri);
        }
    };

    /// The hover for the name at a position in a document, or null when
    /// there is nothing to show there.
    pub fn getTypeAtPosition(
        self: *SyntaxChecker,
        uri: []const u8,
        override_text: ?[]const u8,
        line: u32,
        character: u32,
    ) QueryError!?HoverResult {
        self.mutex.lockUncancelable(self.std_io);
        defer self.mutex.unlock(self.std_io);

        var build = try self.prepareDocumentBuild(uri, override_text);
        defer build.deinit();

        self.logDebug(.build, "hover: document {s} reused={}", .{ build.absolute_path, build.reused });

        if (!build.build_succeeded) {
            self.logDebug(.build, "hover: build unavailable for {s}", .{build.absolute_path});
            return null;
        }

        const module_env = build.getModuleEnv() orelse return null;
        const target_offset = build.view(module_env).offsetAt(line, character) orelse return null;

        const found = (try hover.at(self.allocator, build.handle, build.lookupContext(build.env, module_env), target_offset)) orelse return null;
        return HoverResult{
            .type_str = found.markdown,
            .range = build.view(module_env).rangeOfRegion(found.region),
        };
    }

    /// Get definition location at a specific position in a document.
    /// Returns the location where the symbol is defined, or null if not found.
    pub fn getDefinitionAtPosition(
        self: *SyntaxChecker,
        uri: []const u8,
        override_text: ?[]const u8,
        line: u32,
        character: u32,
    ) QueryError!?DefinitionResult {
        self.mutex.lockUncancelable(self.std_io);
        defer self.mutex.unlock(self.std_io);

        var build = try self.prepareDocumentBuild(uri, override_text);
        defer build.deinit();

        if (!build.build_succeeded) {
            self.logDebug(.build, "definition: build unavailable for {s}", .{build.absolute_path});
            return null;
        }

        // Get module environment
        const module_env = build.getModuleEnv() orelse return null;

        // Convert LSP position to byte offset
        const target_offset = build.view(module_env).offsetAt(line, character) orelse return null;

        // Find the definition at this position
        var oom: ?Allocator.Error = null;
        var result = self.findDefinitionAtOffset(build.env, module_env, build.modulePath(), target_offset, uri, &oom) orelse {
            if (oom) |e| return e;
            return null;
        };

        // A location in this document is a range of its module. One in text
        // that staging wrote, such as the `echo!` binding, is in no file.
        if (std.mem.eql(u8, result.uri, uri)) {
            result.range = build.view(module_env).rangeOf(result.range) orelse {
                result.deinit(self.allocator);
                return null;
            };
        }
        if (result.origin_selection_range) |origin| result.origin_selection_range = build.view(module_env).rangeOf(origin);

        return result;
    }

    // positionToOffset moved to position.zig

    // regionToRange moved to cir_queries module

    /// Find the definition location for the expression at the given byte offset.
    /// Looks for lookups (e_lookup_local, e_lookup_external) and returns the definition location.
    fn findDefinitionAtOffset(self: *SyntaxChecker, build_env: *BuildEnv, module_env: *ModuleEnv, doc_path: []const u8, target_offset: u32, current_uri: []const u8, oom: *?Allocator.Error) ?DefinitionResult {
        if (cir_queries.findWriteAtOffset(module_env, target_offset)) |write| {
            const range = cir_queries.declarationNameRegion(module_env, write.pattern_idx) orelse return null;
            const uri_copy = noteOom(oom, self.allocator.dupe(u8, current_uri)) orelse return null;
            return DefinitionResult{ .uri = uri_copy, .range = range };
        }

        // A type name in an annotation or a type declaration's header goes to
        // the declaration it names, as hover shows it.
        if (anno_targets.at(.{ .build_env = build_env, .module_env = module_env, .module_path = doc_path }, target_offset)) |found| switch (found) {
            .decl => |decl_target| {
                if (self.declarationLocation(build_env, module_env, current_uri, decl_target.env, decl_target.env.store.getStatementRegion(decl_target.decl), oom)) |result| return result;
            },
            .member => {},
        };

        var best_lookup: ?cir_queries.LookupResult = null;

        // Iterate through all definitions
        const defs_slice = module_env.store.sliceDefs(module_env.all_defs);
        for (defs_slice) |def_idx| {
            const def = module_env.store.getDef(def_idx);
            const expr_idx = def.expr;
            const expr_node_idx: CIR.Node.Idx = @fromBackingInt(@intCast(@backingInt(expr_idx)));
            const expr_region = module_env.store.getRegionAt(expr_node_idx);

            if (cir_queries.regionContainsOffset(expr_region, target_offset)) {
                if (cir_queries.findLookupAtOffset(module_env, target_offset)) |found| {
                    best_lookup = found;
                }
            }
        }

        const file_deps = module_env.file_dependencies.items.items;
        for (file_deps) |dep| {
            if (cir_queries.regionContainsOffset(dep.region(), target_offset)) {
                // The build read the file from its module's source directory.
                // A staged document's module is in a scratch directory, but
                // its source directory is the document's.
                const path_text = module_env.getString(dep.relative_path);
                const source_dir = (build_env.findModuleByPath(doc_path) orelse return null).canonicalSourceDir();
                const target_path = noteOom(oom, std.fs.path.resolve(self.allocator, &.{ source_dir, path_text })) orelse return null;
                defer self.allocator.free(target_path);

                const target_uri = noteOom(oom, self.uriForPath(target_path)) orelse return null;

                const origin_range = cir_queries.regionToRange(module_env, dep.region());

                return DefinitionResult{
                    .uri = target_uri,
                    .range = .{
                        .start_line = 0,
                        .start_col = 0,
                        .end_line = 0,
                        .end_col = 0,
                    },
                    .origin_selection_range = origin_range,
                };
            }
        }

        // Iterate through all statements to check imports
        const statements_slice = module_env.store.sliceStatements(module_env.all_statements);
        for (statements_slice) |stmt_idx| {
            const stmt = module_env.store.getSourceStatement(stmt_idx);

            // Handle import statements specially - navigate to the imported module or exposed item
            if (stmt == .s_import) {
                const import_stmt = stmt.s_import;
                const import_node_idx: CIR.Node.Idx = @fromBackingInt(@intCast(@backingInt(stmt_idx)));
                const import_region = module_env.store.getRegionAt(import_node_idx);

                if (cir_queries.regionContainsOffset(import_region, target_offset)) {
                    const import_name = module_env.getIdentText(import_stmt.module_name_tok);
                    const target_env = build_env.importedModuleEnv(doc_path, import_name) orelse return null;

                    // On an exposed item, go to the declaration import
                    // resolution selected for it.
                    for (module_env.store.sliceExposedItems(import_stmt.exposes)) |exposed_item_idx| {
                        const exposed_node_idx: CIR.Node.Idx = @fromBackingInt(@intCast(@backingInt(exposed_item_idx)));
                        if (cir_queries.regionContainsOffset(module_env.store.getRegionAt(exposed_node_idx), target_offset)) {
                            const target_node = module_env.store.getExposedItem(exposed_item_idx).target orelse return null;
                            return self.declarationLocation(build_env, module_env, current_uri, target_env, declarationNodeRegion(target_env, target_node), oom);
                        }
                    }

                    return self.moduleLocation(build_env, module_env, current_uri, target_env, oom);
                }
            }

            const stmt_parts = module_lookup.getStatementParts(stmt);

            if (stmt_parts.expr) |expr_idx| {
                const expr_node_idx: CIR.Node.Idx = @fromBackingInt(@intCast(@backingInt(expr_idx)));
                const expr_region = module_env.store.getRegionAt(expr_node_idx);

                if (cir_queries.regionContainsOffset(expr_region, target_offset)) {
                    if (cir_queries.findLookupAtOffset(module_env, target_offset)) |found| {
                        best_lookup = found;
                    }
                }
            }

            if (stmt_parts.expr2) |expr_idx| {
                const expr_node_idx: CIR.Node.Idx = @fromBackingInt(@intCast(@backingInt(expr_idx)));
                const expr_region = module_env.store.getRegionAt(expr_node_idx);

                if (cir_queries.regionContainsOffset(expr_region, target_offset)) {
                    if (cir_queries.findLookupAtOffset(module_env, target_offset)) |found| {
                        best_lookup = found;
                    }
                }
            }
        }

        // If we found a lookup expression, resolve it to a definition
        if (best_lookup) |lookup_result| {
            const expr_idx = switch (lookup_result) {
                .expr => |idx| idx,
                .field_access => return null,
            };
            const target = switch (lookup_target.resolve(.{ .build_env = build_env, .module_env = module_env, .module_path = doc_path }, expr_idx)) {
                .target => |target| target,
                .unresolved, .not_a_reference => return null,
            };
            switch (target) {
                .local => |pattern_idx| {
                    // Get the pattern's region - that's where it's defined
                    const pattern_node_idx: CIR.Node.Idx = @fromBackingInt(@intCast(@backingInt(pattern_idx)));
                    const def_region = module_env.store.getRegionAt(pattern_node_idx);
                    const range = cir_queries.regionToRange(module_env, def_region) orelse return null;
                    const uri_copy = noteOom(oom, self.allocator.dupe(u8, current_uri)) orelse return null;
                    return DefinitionResult{
                        .uri = uri_copy,
                        .range = range,
                    };
                },
                .external => |external| {
                    const target_env = external.env;

                    // On the qualifier (`List` in `List.len`), go to the type that
                    // declares the value, or to the module when no type does.
                    const region_text = module_env.getSource(external.region);
                    if (std.mem.findScalarLast(u8, region_text, '.')) |dot_pos| {
                        if (target_offset < external.region.start.offset + @as(u32, @intCast(dot_pos))) {
                            if (owningTypeDeclaration(target_env, external.node)) |owner| {
                                return self.declarationLocation(build_env, module_env, current_uri, target_env, target_env.store.getStatementRegion(owner), oom);
                            }
                            return self.moduleLocation(build_env, module_env, current_uri, target_env, oom);
                        }
                    }

                    return self.declarationLocation(build_env, module_env, current_uri, target_env, declarationNodeRegion(target_env, external.node), oom);
                },
                .associated => |associated| {
                    const def = associated.env.store.getDef(associated.def);
                    return self.declarationLocation(build_env, module_env, current_uri, associated.env, associated.env.store.getPatternRegion(def.pattern), oom);
                },
                .method => |method| {
                    if (!cir_queries.regionContainsOffset(method.name_region, target_offset)) return null;
                    const def = method.env.store.getDef(method.binding.def_idx);
                    return self.declarationLocation(build_env, module_env, current_uri, method.env, method.env.store.getPatternRegion(def.pattern), oom);
                },
            }
        }

        // Check for tag expression or pattern (e.g. `WaitingForInit` in pattern `WaitingForInit =>` or expr `WaitingForInit`)
        if (cir_queries.findTagAtOffset(module_env, target_offset)) |tag_ref| {
            return self.findTagDefinition(build_env, module_env, doc_path, tag_ref, current_uri, oom);
        }

        return null;
    }

    /// The location of `region` in `target_env`'s source file.
    fn declarationLocation(
        self: *SyntaxChecker,
        build_env: *BuildEnv,
        module_env: *ModuleEnv,
        current_uri: []const u8,
        target_env: *ModuleEnv,
        region: Region,
        oom: *?Allocator.Error,
    ) ?DefinitionResult {
        const range = cir_queries.regionToRange(target_env, region) orelse return null;
        const uri = self.moduleSourceUri(build_env, module_env, current_uri, target_env, oom) orelse return null;
        return DefinitionResult{ .uri = uri, .range = range };
    }

    /// The URI of the file holding `target_env`'s source: the open document,
    /// the cached copy of the embedded Builtin source, or the module's file.
    fn moduleSourceUri(
        self: *SyntaxChecker,
        build_env: *BuildEnv,
        module_env: *ModuleEnv,
        current_uri: []const u8,
        target_env: *ModuleEnv,
        oom: *?Allocator.Error,
    ) ?[]u8 {
        if (target_env == module_env) return noteOom(oom, self.allocator.dupe(u8, current_uri));
        if (target_env == build_env.builtin_modules.builtin_module.env) return self.builtinSourceUri(oom);
        const target_hash = target_env.contentIdentityHash() orelse return null;
        const target_mod_state = module_envs.stateForContentIdentity(build_env, target_hash) orelse return null;
        return noteOom(oom, self.uriForPath(target_mod_state.path));
    }

    /// The region of a declaration node: the name a value definition (or a
    /// destructuring binder) binds, or a type declaration statement.
    fn declarationNodeRegion(module_env: *ModuleEnv, decl_node: u32) Region {
        const store = &module_env.store;
        const node_idx: CIR.Node.Idx = @fromBackingInt(@intCast(decl_node));
        const tag = store.nodes.get(node_idx).tag;
        if (tag == .def) return store.getPatternRegion(store.getDef(@fromBackingInt(decl_node)).pattern);
        if (tag == .statement_nominal_decl or tag == .statement_alias_decl) return store.getStatementRegion(@fromBackingInt(decl_node));
        return store.getPatternRegion(@fromBackingInt(decl_node));
    }

    /// The start of `target_env`'s source file.
    fn moduleLocation(
        self: *SyntaxChecker,
        build_env: *BuildEnv,
        module_env: *ModuleEnv,
        current_uri: []const u8,
        target_env: *ModuleEnv,
        oom: *?Allocator.Error,
    ) ?DefinitionResult {
        const uri = self.moduleSourceUri(build_env, module_env, current_uri, target_env, oom) orelse return null;
        return DefinitionResult{ .uri = uri, .range = .{ .start_line = 0, .start_col = 0, .end_line = 0, .end_col = 0 } };
    }

    /// The type declaration whose associated items include the value
    /// definition `value_node`, if any.
    fn owningTypeDeclaration(module_env: *ModuleEnv, value_node: u32) ?CIR.Statement.Idx {
        const store = &module_env.store;
        const node_idx: CIR.Node.Idx = @fromBackingInt(@intCast(value_node));
        if (store.nodes.get(node_idx).tag != .def) return null;
        const def = store.getDef(@fromBackingInt(value_node));
        const ident = module_lookup.extractIdentFromPattern(store, def.pattern) orelse return null;
        for (module_env.method_idents.entries.items) |entry| {
            if (entry.value.eql(ident)) return entry.key.owner;
        }
        return null;
    }

    const TagOriginInfo = struct {
        origin_module: base.ModuleIdentity.Idx,
        source_decl: types.SourceDecl,
    };

    fn resolveTagOrigin(module_env: *ModuleEnv, type_var: types.Var) ?TagOriginInfo {
        const resolved = module_env.types.resolveVar(type_var);
        const content = resolved.desc.content;
        switch (content) {
            .alias => |alias| {
                return .{
                    .origin_module = alias.origin_module,
                    .source_decl = alias.source_decl,
                };
            },
            .structure => |flat| switch (flat) {
                .nominal_type => |nominal| {
                    return .{
                        .origin_module = nominal.origin_module,
                        .source_decl = nominal.source.sourceDecl(),
                    };
                },
                .fn_pure,
                .fn_effectful,
                .fn_unbound,
                .record,
                .tuple,
                .empty_record,
                .tag_union,
                .empty_tag_union,
                => return null,
            },
            .flex,
            .rigid,
            .field_presence,
            .err,
            => return null,
        }
    }

    fn findTagInTypeAnno(store: *const can.NodeStore, common: *const base.CommonEnv, type_anno_idx: CIR.TypeAnno.Idx, tag_name: []const u8) ?Region {
        const type_anno = store.getTypeAnno(type_anno_idx);
        switch (type_anno) {
            .tag_union => |tu| {
                const tags_slice = store.sliceTypeAnnos(tu.tags);
                for (tags_slice) |tag_idx| {
                    const tag = store.getTypeAnno(tag_idx);
                    if (tag == .tag) {
                        const name = common.idents.getText(tag.tag.name);
                        if (std.mem.eql(u8, name, tag_name)) {
                            return store.getTypeAnnoRegion(tag_idx);
                        }
                    }
                }
                if (tu.ext) |ext_idx| {
                    if (findTagInTypeAnno(store, common, ext_idx, tag_name)) |r| return r;
                }
            },
            .tag => |t| {
                const name = common.idents.getText(t.name);
                if (std.mem.eql(u8, name, tag_name)) {
                    return store.getTypeAnnoRegion(type_anno_idx);
                }
            },
            .apply,
            .rigid_var,
            .rigid_var_lookup,
            .underscore,
            .lookup,
            .tuple,
            .record,
            .@"fn",
            .parens,
            .malformed,
            => {},
        }
        return null;
    }

    fn findTagInModuleEnv(mod_env: *ModuleEnv, tag_name: []const u8) ?Region {
        const statements_slice = mod_env.store.sliceStatements(mod_env.all_statements);
        for (statements_slice) |stmt_idx| {
            const stmt = mod_env.store.getSourceStatement(stmt_idx);
            const maybe_anno = if (module_lookup.typeDeclParts(stmt)) |parts| parts.anno else null;
            if (maybe_anno) |anno_idx| {
                if (findTagInTypeAnno(&mod_env.store, &mod_env.common, anno_idx, tag_name)) |r| {
                    return r;
                }
            }
        }
        return null;
    }

    /// Helper function to find a tag declaration (e.g., `WaitingForInit` in `LoopState : [WaitingForInit, ...]`)
    fn findTagDefinition(
        self: *SyntaxChecker,
        build_env: *BuildEnv,
        module_env: *ModuleEnv,
        doc_path: []const u8,
        tag_ref: cir_queries.TagRef,
        current_uri: []const u8,
        oom: *?Allocator.Error,
    ) ?DefinitionResult {
        const tag_name = tag_ref.name;

        // 1. If the tag reference carries an explicit external nominal import identity,
        // navigate directly to that imported module and declaration.
        if (tag_ref.nominal_external) |nom_ext| {
            const import_idx_int = @backingInt(nom_ext.module_idx);
            if (import_idx_int < module_env.imports.imports.len()) {
                const string_idx = module_env.imports.imports.items.items[import_idx_int];
                const module_name = module_env.common.getString(string_idx);
                const env = build_env;
                const importing_pkg = env.findPackageForModulePath(doc_path);
                const mod_state_opt = if (std.mem.find(u8, module_name, ".") != null)
                    env.findModuleByQualifiedNameInPackage(importing_pkg, module_name)
                else
                    env.findModuleByNameInPackage(importing_pkg, module_name);
                if (mod_state_opt) |mod_state| {
                    if (mod_state.moduleEnv()) |target_mod_env| {
                        const target_node_idx: CIR.Node.Idx = @fromBackingInt(@intCast(nom_ext.target_node_idx));
                        const node_tag = target_mod_env.store.nodes.get(target_node_idx).tag;
                        if (node_tag == .statement_nominal_decl or node_tag == .statement_alias_decl) {
                            const stmt = target_mod_env.store.getSourceStatement(@fromBackingInt(@backingInt(target_node_idx)));
                            const maybe_anno = if (module_lookup.typeDeclParts(stmt)) |parts| parts.anno else null;
                            if (maybe_anno) |anno_idx| {
                                if (findTagInTypeAnno(&target_mod_env.store, &target_mod_env.common, anno_idx, tag_name)) |tag_region| {
                                    const range = cir_queries.regionToRange(target_mod_env, tag_region) orelse return null;
                                    const module_uri = noteOom(oom, self.uriForPath(mod_state.path)) orelse return null;
                                    return DefinitionResult{
                                        .uri = module_uri,
                                        .range = range,
                                    };
                                }
                            }
                        }
                        if (findTagInModuleEnv(target_mod_env, tag_name)) |tag_region| {
                            const range = cir_queries.regionToRange(target_mod_env, tag_region) orelse return null;
                            const module_uri = noteOom(oom, self.uriForPath(mod_state.path)) orelse return null;
                            return DefinitionResult{
                                .uri = module_uri,
                                .range = range,
                            };
                        }
                    }
                }
            }
            return null;
        }

        // 2. If the tag reference carries an explicit local nominal declaration identity,
        // navigate directly to that local statement.
        if (tag_ref.nominal_decl) |stmt_idx| {
            const stmt = module_env.store.getSourceStatement(stmt_idx);
            const maybe_anno = if (module_lookup.typeDeclParts(stmt)) |parts| parts.anno else null;
            if (maybe_anno) |anno_idx| {
                if (findTagInTypeAnno(&module_env.store, &module_env.common, anno_idx, tag_name)) |tag_region| {
                    const range = cir_queries.regionToRange(module_env, tag_region) orelse return null;
                    const uri_copy = noteOom(oom, self.allocator.dupe(u8, current_uri)) orelse return null;
                    return DefinitionResult{
                        .uri = uri_copy,
                        .range = range,
                    };
                }
            }
        }

        // 3. If type inference resolved the tag's type (or the matched condition's type for a pattern tag)
        // to a nominal type or alias, use the exact declaring module identity and source declaration locator.
        const origin_info_opt = resolveTagOrigin(module_env, tag_ref.type_var) orelse (if (tag_ref.match_cond_type_var) |cond_var| resolveTagOrigin(module_env, cond_var) else null);
        if (origin_info_opt) |origin_info| {
            if (origin_info.origin_module == module_env.selfModuleIdentity()) {
                // Defined in current module
                if (origin_info.source_decl.toOptional()) |stmt_num| {
                    const stmt = module_env.store.getSourceStatement(@fromBackingInt(stmt_num));
                    const maybe_anno = if (module_lookup.typeDeclParts(stmt)) |parts| parts.anno else null;
                    if (maybe_anno) |anno_idx| {
                        if (findTagInTypeAnno(&module_env.store, &module_env.common, anno_idx, tag_name)) |tag_region| {
                            const range = cir_queries.regionToRange(module_env, tag_region) orelse return null;
                            const uri_copy = noteOom(oom, self.allocator.dupe(u8, current_uri)) orelse return null;
                            return DefinitionResult{
                                .uri = uri_copy,
                                .range = range,
                            };
                        }
                    }
                }
                if (findTagInModuleEnv(module_env, tag_name)) |tag_region| {
                    const range = cir_queries.regionToRange(module_env, tag_region) orelse return null;
                    const uri_copy = noteOom(oom, self.allocator.dupe(u8, current_uri)) orelse return null;
                    return DefinitionResult{
                        .uri = uri_copy,
                        .range = range,
                    };
                }
            } else {
                // Defined in a specific external module
                const origin_hash = module_env.moduleIdentityHash(origin_info.origin_module);
                if (module_envs.stateForContentIdentity(build_env, origin_hash)) |target_mod_state| {
                    if (target_mod_state.moduleEnv()) |target_mod_env| {
                        if (origin_info.source_decl.toOptional()) |stmt_num| {
                            const stmt = target_mod_env.store.getSourceStatement(@fromBackingInt(stmt_num));
                            const maybe_anno = if (module_lookup.typeDeclParts(stmt)) |parts| parts.anno else null;
                            if (maybe_anno) |anno_idx| {
                                if (findTagInTypeAnno(&target_mod_env.store, &target_mod_env.common, anno_idx, tag_name)) |tag_region| {
                                    const range = cir_queries.regionToRange(target_mod_env, tag_region) orelse return null;
                                    const module_uri = noteOom(oom, self.uriForPath(target_mod_state.path)) orelse return null;
                                    return DefinitionResult{
                                        .uri = module_uri,
                                        .range = range,
                                    };
                                }
                            }
                        }
                        if (findTagInModuleEnv(target_mod_env, tag_name)) |tag_region| {
                            const range = cir_queries.regionToRange(target_mod_env, tag_region) orelse return null;
                            const module_uri = noteOom(oom, self.uriForPath(target_mod_state.path)) orelse return null;
                            return DefinitionResult{
                                .uri = module_uri,
                                .range = range,
                            };
                        }
                    }
                }
            }
            return null;
        }

        // 4. If tag has no nominal/alias type origin (e.g. pure open tag), check current module
        if (findTagInModuleEnv(module_env, tag_name)) |tag_region| {
            const range = cir_queries.regionToRange(module_env, tag_region) orelse return null;
            const uri_copy = noteOom(oom, self.allocator.dupe(u8, current_uri)) orelse return null;
            return DefinitionResult{
                .uri = uri_copy,
                .range = range,
            };
        }

        return null;
    }

    /// The URI of the cached copy of the embedded Builtin source, written on
    /// first use so editors can open it.
    fn builtinSourceUri(self: *SyntaxChecker, oom: *?Allocator.Error) ?[]u8 {
        const cache_dir = self.cache_config.getModuleCacheDir(self.allocator) catch |err| switch (err) {
            error.OutOfMemory => {
                oom.* = error.OutOfMemory;
                return null;
            },
            error.NoHomeDirectory => return null,
        };
        const builtin_cache_path = std.fs.path.join(self.allocator, &.{ cache_dir, "Builtin.roc" }) catch |err| {
            self.allocator.free(cache_dir);
            oom.* = err;
            return null;
        };
        self.allocator.free(cache_dir);

        // Write file if it doesn't exist
        if (std.Io.Dir.cwd().access(self.std_io, builtin_cache_path, .{})) |_| {
            // Already exists
        } else |_| {
            // Create parent dirs and write embedded source
            if (std.fs.path.dirname(builtin_cache_path)) |dir| {
                std.Io.Dir.cwd().createDirPath(self.std_io, dir) catch {};
            }
            const file = std.Io.Dir.cwd().createFile(self.std_io, builtin_cache_path, .{}) catch {
                self.allocator.free(builtin_cache_path);
                return null;
            };
            defer file.close(self.std_io);
            file.writeStreamingAll(self.std_io, compiled_builtins.builtin_source) catch {
                self.allocator.free(builtin_cache_path);
                return null;
            };
        }

        const module_uri = self.uriForPath(builtin_cache_path) catch |err| {
            self.allocator.free(builtin_cache_path);
            oom.* = err;
            return null;
        };
        self.allocator.free(builtin_cache_path);

        return module_uri;
    }

    // findLookupAtOffset moved to cir_queries module

    /// Result of finding highlights for a symbol
    pub const HighlightResult = struct {
        regions: []LspRange,

        pub fn deinit(self: HighlightResult, allocator: std.mem.Allocator) void {
            allocator.free(self.regions);
        }
    };

    /// Get all occurrences of the symbol at the given position.
    /// Uses CIR to properly handle scoped variables (shadowing).
    pub fn getHighlightsAtPosition(
        self: *SyntaxChecker,
        uri: []const u8,
        override_text: ?[]const u8,
        line: u32,
        character: u32,
    ) QueryError!?HighlightResult {
        self.mutex.lockUncancelable(self.std_io);
        defer self.mutex.unlock(self.std_io);

        var build = try self.prepareDocumentBuild(uri, override_text);
        defer build.deinit();

        self.logDebug(.build, "highlights: document {s} reused={}", .{ build.absolute_path, build.reused });

        if (!build.build_succeeded) {
            self.logDebug(.build, "highlights: build unavailable for {s}", .{build.absolute_path});
            return null;
        }

        // Get module environment
        const module_env = build.getModuleEnv() orelse return null;

        // Convert LSP position to byte offset
        const target_offset = build.view(module_env).offsetAt(line, character) orelse return null;

        // Resolve the symbol at this position. The cursor may sit on the
        // definition or on any reference to it; both resolve to the pattern
        // that owns the binding.
        const target_pattern = cir_queries.resolveSymbolAtOffset(module_env, target_offset) orelse return null;

        return HighlightResult{
            .regions = try build.view(module_env).documentRanges(self.allocator, try self.collectSymbolRegions(module_env, target_pattern, false)),
        };
    }

    /// Collect every source range that names `target_pattern`: the binding
    /// itself, the name on its type annotation if it has one, and every
    /// reference to it.
    ///
    /// This is the set a rename must rewrite, so highlighting and renaming
    /// share it rather than each deciding what counts as an occurrence.
    /// Caller owns the returned slice.
    fn collectSymbolRegions(
        self: *SyntaxChecker,
        module_env: *ModuleEnv,
        target_pattern: CIR.Pattern.Idx,
        comptime member_only: bool,
    ) Allocator.Error![]LspRange {
        var regions = try cir_queries.collectDeclarationRegions(module_env, target_pattern, self.allocator);
        errdefer regions.deinit(self.allocator);

        var lookup_regions = if (member_only)
            try cir_queries.collectMemberReferences(module_env, target_pattern, self.allocator)
        else
            try cir_queries.collectReferences(module_env, target_pattern, self.allocator);
        defer lookup_regions.deinit(self.allocator);
        try regions.appendSlice(self.allocator, lookup_regions.items);

        return regions.toOwnedSlice(self.allocator);
    }

    /// One inferred type, ready to be shown against the name it belongs to.
    pub const InlayHint = struct {
        line: u32,
        character: u32,
        /// The rendered type, including its leading `: `. Owned by the result.
        label: []u8,
        /// The edit that writes this type into the source, for a client that
        /// lets the reader accept a hint. Null where no annotation can be
        /// written: Roc has no inline `name : Type = value` form, so accepting
        /// a hint has to insert a line above the binding, and not every
        /// binding a hint is drawn on can take one.
        edit: ?AnnotationEdit,
    };

    /// The hints for one requested range.
    pub const InlayHintsResult = struct {
        hints: []InlayHint,

        pub fn deinit(self: InlayHintsResult, allocator: std.mem.Allocator) void {
            for (self.hints) |hint| {
                allocator.free(hint.label);
                if (hint.edit) |edit| allocator.free(edit.new_text);
            }
            allocator.free(self.hints);
        }
    };

    /// The line break generated source is written with.
    ///
    /// It comes from the document the client holds, not from the module: the
    /// compiler rewrites CRLF to LF as it loads a file, so by the time there
    /// are types to read there is no `\r` left to find. Writing a lone `\n`
    /// into a CRLF document would leave mixed endings behind for a formatter,
    /// a diff, or an EOL-strict editor to report.
    ///
    /// A document nobody has open has no text to read, and LF is the answer
    /// the normalized source would give anyway.
    fn documentLineEnding(module_env: *ModuleEnv, override_text: ?[]const u8) []const u8 {
        return pos.lineEnding(override_text orelse module_env.common.source);
    }

    /// An insertion that writes a binding's inferred type above it.
    pub const AnnotationEdit = struct {
        /// Where the text goes. This inserts, so the range is empty.
        range: LspRange,
        /// The line to insert, newline included. Owned by whoever holds it.
        new_text: []u8,
    };

    /// Build the edit that writes `rendered` as `binding`'s annotation, or
    /// null when the binding cannot take one.
    ///
    /// The annotation is a line of its own above the binding, so the binding
    /// has to open its line. Anything else in front of it - a block written on
    /// a single line, for one - would be split across the inserted line break.
    ///
    /// The caller has already established that `binding` is what its line
    /// declares; a lambda parameter is not, and its line belongs to the
    /// parameter list.
    fn annotationInsertion(
        self: *SyntaxChecker,
        module_env: *ModuleEnv,
        binding: cir_queries.UnannotatedBinding,
        rendered: []const u8,
        eol: []const u8,
    ) Allocator.Error!?AnnotationEdit {
        const line_starts = module_env.getLineStartsAll();
        if (binding.range.start_line >= line_starts.len) return null;
        const line_start = line_starts[binding.range.start_line];
        if (line_start > binding.region.start.offset) return null;

        const indent = module_env.common.source[line_start..binding.region.start.offset];
        for (indent) |byte| {
            if (byte != ' ' and byte != '\t') return null;
        }

        // The collected binding is spelled exactly its name, so the source
        // under it is the name to write the annotation for.
        const name = module_env.common.source[binding.region.start.offset..binding.region.end.offset];

        return AnnotationEdit{
            .range = .{
                .start_line = binding.range.start_line,
                .start_col = 0,
                .end_line = binding.range.start_line,
                .end_col = 0,
            },
            .new_text = try std.fmt.allocPrint(self.allocator, "{s}{s} : {s}{s}", .{ indent, name, rendered, eol }),
        };
    }

    /// Render the inferred type of every unannotated binding in a line range.
    ///
    /// Roc infers most types, and an annotation may leave parts of one to
    /// inference with `_`, so the type a binding actually has is often written
    /// nowhere in the file. These hints put it next to the name.
    ///
    /// Bindings that carry a written annotation are skipped: their type is
    /// already on screen, and repeating it would only add noise.
    pub fn getInlayHints(
        self: *SyntaxChecker,
        uri: []const u8,
        override_text: ?[]const u8,
        start_line: u32,
        end_line: u32,
    ) QueryError!?InlayHintsResult {
        self.mutex.lockUncancelable(self.std_io);
        defer self.mutex.unlock(self.std_io);

        var build = try self.prepareDocumentBuild(uri, override_text);
        defer build.deinit();

        self.logDebug(.build, "inlayHint: document {s} reused={}", .{ build.absolute_path, build.reused });

        if (!build.build_succeeded) {
            self.logDebug(.build, "inlayHint: build unavailable for {s}", .{build.absolute_path});
            return null;
        }

        const module_env = build.getModuleEnv() orelse return null;

        // The request names whole lines; widen to the byte span they cover.
        const start_offset = build.view(module_env).offsetAt(start_line, 0) orelse return null;
        // The span ends where the line after `end_line` starts, or at the end
        // of the document. `end_line` is whatever the client sent, so the
        // next line saturates rather than overflows.
        const end_offset = build.view(module_env).offsetAtClamped(end_line +| 1, 0) orelse return null;

        var bindings = try cir_queries.collectUnannotatedBindings(module_env, start_offset, end_offset, self.allocator);
        defer bindings.deinit(self.allocator);

        const eol = documentLineEnding(module_env, override_text);

        var hints: std.ArrayList(InlayHint) = .empty;
        errdefer {
            for (hints.items) |hint| {
                self.allocator.free(hint.label);
                if (hint.edit) |edit| self.allocator.free(edit.new_text);
            }
            hints.deinit(self.allocator);
        }

        var type_writer = try module_env.initTypeWriter();
        defer type_writer.deinit();

        for (bindings.items) |binding| {
            // A binding that staging wrote, such as `echo!`, is not in the
            // document.
            const hint_range = build.view(module_env).rangeOf(binding.range) orelse continue;

            type_writer.reset();
            type_writer.write(ModuleEnv.varFrom(binding.pattern), .one_line) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => continue,
            };

            const rendered = type_writer.get();
            if (rendered.len == 0) continue;

            // The label is cut to keep the line readable; the edit writes the
            // type in full, because a cut one would not compile. Only a
            // binding a definition or a statement declares can carry the edit:
            // an annotation written above anything else lands where it does
            // not belong, in a lambda's parameter list most of all.
            var edit = if (binding.is_declaration)
                try self.annotationInsertion(module_env, binding, rendered, eol)
            else
                null;
            if (edit) |*insertion| {
                if (build.view(module_env).rangeOf(insertion.range)) |range| {
                    insertion.range = range;
                } else {
                    self.allocator.free(insertion.new_text);
                    edit = null;
                }
            }
            errdefer if (edit) |unused| self.allocator.free(unused.new_text);

            const shown = truncateTypeLabel(rendered);
            const label = if (shown.len < rendered.len)
                try std.fmt.allocPrint(self.allocator, ": {s}…", .{shown})
            else
                try std.fmt.allocPrint(self.allocator, ": {s}", .{shown});
            errdefer self.allocator.free(label);

            try hints.append(self.allocator, .{
                .line = hint_range.end_line,
                .character = hint_range.end_col,
                .label = label,
                .edit = edit,
            });
        }

        return InlayHintsResult{
            .hints = try hints.toOwnedSlice(self.allocator),
        };
    }

    /// One edit the editor may offer, ready to be sent as a `CodeAction`.
    pub const CodeAction = struct {
        /// What the editor shows in its menu. Owned by the result.
        title: []u8,
        /// The LSP `CodeActionKind` this belongs under.
        kind: []const u8,
        /// Where the text goes. Both actions insert, so this range is empty.
        range: LspRange,
        /// The source to insert there. Owned by the result.
        new_text: []u8,
    };

    /// The actions offered for one requested range.
    pub const CodeActionsResult = struct {
        actions: []CodeAction,

        pub fn deinit(self: CodeActionsResult, allocator: std.mem.Allocator) void {
            for (self.actions) |action| {
                allocator.free(action.title);
                allocator.free(action.new_text);
            }
            allocator.free(self.actions);
        }
    };

    /// The `CodeActionKind` both offered actions belong to.
    const refactor_rewrite_kind = "refactor.rewrite";

    /// Offer the edits that apply to a requested range.
    ///
    /// Two are offered today, both written from the checked types: an
    /// annotation for a binding that infers its type, and an `expect` that
    /// calls a top-level function. Both need types, so a document that does
    /// not build offers nothing.
    pub fn getCodeActions(
        self: *SyntaxChecker,
        uri: []const u8,
        override_text: ?[]const u8,
        start_line: u32,
        start_character: u32,
        end_line: u32,
        end_character: u32,
    ) QueryError!?CodeActionsResult {
        self.mutex.lockUncancelable(self.std_io);
        defer self.mutex.unlock(self.std_io);

        var build = try self.prepareDocumentBuild(uri, override_text);
        defer build.deinit();

        self.logDebug(.build, "codeAction: document {s} reused={}", .{ build.absolute_path, build.reused });

        if (!build.build_succeeded) {
            self.logDebug(.build, "codeAction: build unavailable for {s}", .{build.absolute_path});
            return null;
        }

        const module_env = build.getModuleEnv() orelse return null;

        // A selection reaching the last line ends one line past the document,
        // and some clients spell "the whole line" with a character far past
        // its length. Either would reject the request outright, answering that
        // nothing may be done here for a range that covers a whole function.
        const start_offset = build.view(module_env).offsetAtClamped(start_line, start_character) orelse return null;
        const end_offset = build.view(module_env).offsetAtClamped(end_line, end_character) orelse return null;
        if (end_offset < start_offset) return null;

        var actions: std.ArrayList(CodeAction) = .empty;
        errdefer {
            for (actions.items) |action| {
                self.allocator.free(action.title);
                self.allocator.free(action.new_text);
            }
            actions.deinit(self.allocator);
        }

        const eol = documentLineEnding(module_env, override_text);
        try self.appendAnnotationActions(module_env, start_offset, end_offset, eol, &actions);
        try self.appendExpectTestActions(module_env, start_offset, end_offset, eol, &actions);

        // Each action edits the document, so its range must be in the
        // document's own text, not in text that staging wrote.
        var kept: usize = 0;
        for (actions.items) |action| {
            if (build.view(module_env).rangeOf(action.range)) |range| {
                actions.items[kept] = action;
                actions.items[kept].range = range;
                kept += 1;
            } else {
                self.allocator.free(action.title);
                self.allocator.free(action.new_text);
            }
        }
        actions.shrinkRetainingCapacity(kept);

        return CodeActionsResult{
            .actions = try actions.toOwnedSlice(self.allocator),
        };
    }

    /// Add one action per binding in the range that can take an annotation,
    /// in source order.
    ///
    /// A range covering several bindings has no one right answer, and the
    /// protocol does not ask for one: `textDocument/codeAction` answers with a
    /// menu. Every title names its binding, so the reader picks the intended
    /// one instead of a rule guessing at it. Earlier rules did guess -- first
    /// by the shortest name, then by the last position -- and each picked the
    /// wrong binding for some arrangement of the same selection.
    ///
    /// A cursor, which is how the request usually arrives, touches one name and
    /// so still produces one action.
    fn appendAnnotationActions(
        self: *SyntaxChecker,
        module_env: *ModuleEnv,
        start_offset: u32,
        end_offset: u32,
        eol: []const u8,
        actions: *std.ArrayList(CodeAction),
    ) Allocator.Error!void {
        var bindings = try cir_queries.collectUnannotatedBindings(module_env, start_offset, end_offset, self.allocator);
        defer bindings.deinit(self.allocator);
        if (bindings.items.len == 0) return;

        // The walk finds bindings in traversal order; the menu reads better in
        // the order the file writes them.
        std.mem.sort(cir_queries.UnannotatedBinding, bindings.items, {}, bindingPrecedes);

        var type_writer = try module_env.initTypeWriter();
        defer type_writer.deinit();

        for (bindings.items) |target| {
            // A lambda parameter and a destructured field are bindings too,
            // and an annotation belongs to neither: it is a line of its own
            // above what that line declares.
            if (!target.is_declaration) continue;

            type_writer.reset();
            type_writer.write(ModuleEnv.varFrom(target.pattern), .one_line) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => continue,
            };

            const rendered = type_writer.get();
            if (rendered.len == 0) continue;

            const edit = try self.annotationInsertion(module_env, target, rendered, eol) orelse continue;
            errdefer self.allocator.free(edit.new_text);

            const name = module_env.common.source[target.region.start.offset..target.region.end.offset];
            const title = try std.fmt.allocPrint(self.allocator, "Annotate '{s}' with its inferred type", .{name});
            errdefer self.allocator.free(title);

            try actions.append(self.allocator, .{
                .title = title,
                .kind = refactor_rewrite_kind,
                .range = edit.range,
                .new_text = edit.new_text,
            });
        }
    }

    /// Order two bindings by where their names are written.
    fn bindingPrecedes(_: void, left: cir_queries.UnannotatedBinding, right: cir_queries.UnannotatedBinding) bool {
        return left.region.start.offset < right.region.start.offset;
    }

    /// Add one action per top-level function in the range that a test can be
    /// written for, in source order.
    ///
    /// A range covering several functions has no one right answer, for the
    /// same reason an annotation over several bindings does not: nothing about
    /// the range says which function was meant. Every function the range
    /// reaches is offered, named, and the reader picks.
    ///
    /// A cursor, which is how the request usually arrives, touches one
    /// function and so still produces at most one action.
    fn appendExpectTestActions(
        self: *SyntaxChecker,
        module_env: *ModuleEnv,
        start_offset: u32,
        end_offset: u32,
        eol: []const u8,
        actions: *std.ArrayList(CodeAction),
    ) Allocator.Error!void {
        var definitions = try cir_queries.collectTopLevelDefinitionsInRange(module_env, start_offset, end_offset, self.allocator);
        defer definitions.deinit(self.allocator);

        for (definitions.items) |definition| {
            const new_text = try code_action.renderExpectTest(
                self.allocator,
                module_env,
                definition.name,
                ModuleEnv.varFrom(definition.pattern),
                eol,
            ) orelse continue;
            errdefer self.allocator.free(new_text);

            const title = try std.fmt.allocPrint(self.allocator, "Generate an expect test for '{s}'", .{definition.name});
            errdefer self.allocator.free(title);

            try actions.append(self.allocator, .{
                .title = title,
                .kind = refactor_rewrite_kind,
                .range = .{
                    .start_line = definition.end.line,
                    .start_col = definition.end.character,
                    .end_line = definition.end.line,
                    .end_col = definition.end.character,
                },
                .new_text = new_text,
            });
        }
    }

    /// Every place a symbol is written, split the way LSP asks for it.
    pub const ReferencesResult = struct {
        regions: []LspRange,

        pub fn deinit(self: ReferencesResult, allocator: std.mem.Allocator) void {
            allocator.free(self.regions);
        }
    };

    /// Find every occurrence of the symbol at the given position.
    ///
    /// Unlike rename, this reports rather than rewrites, so it is not limited
    /// to plain `assign` bindings: any pattern the cursor resolves to can have
    /// its uses listed.
    ///
    /// When `include_declaration` is false the binding site and its annotation
    /// name are left out, keeping the places the symbol is read or reassigned.
    pub fn getReferencesAtPosition(
        self: *SyntaxChecker,
        uri: []const u8,
        override_text: ?[]const u8,
        line: u32,
        character: u32,
        include_declaration: bool,
    ) QueryError!?ReferencesResult {
        self.mutex.lockUncancelable(self.std_io);
        defer self.mutex.unlock(self.std_io);

        var build = try self.prepareDocumentBuild(uri, override_text);
        defer build.deinit();

        self.logDebug(.build, "references: document {s} reused={}", .{ build.absolute_path, build.reused });

        if (!build.build_succeeded) {
            self.logDebug(.build, "references: build unavailable for {s}", .{build.absolute_path});
            return null;
        }

        const module_env = build.getModuleEnv() orelse return null;
        const target_offset = build.view(module_env).offsetAt(line, character) orelse return null;
        const target_pattern = cir_queries.resolveSymbolAtOffset(module_env, target_offset) orelse return null;

        var regions: std.ArrayList(LspRange) = .empty;
        errdefer regions.deinit(self.allocator);

        if (include_declaration) {
            var declarations = try cir_queries.collectDeclarationRegions(module_env, target_pattern, self.allocator);
            defer declarations.deinit(self.allocator);
            try regions.appendSlice(self.allocator, declarations.items);
        }

        var lookups = try cir_queries.collectReferences(module_env, target_pattern, self.allocator);
        defer lookups.deinit(self.allocator);
        try regions.appendSlice(self.allocator, lookups.items);

        return ReferencesResult{
            .regions = try build.view(module_env).documentRanges(self.allocator, try regions.toOwnedSlice(self.allocator)),
        };
    }

    /// Why a rename request could not be answered with edits.
    pub const RenameRejection = union(enum) {
        /// The position does not name a binding this server can rename.
        not_a_local_binding,
        /// The requested new name is not usable in place of the old one.
        bad_new_name: rename_rules.Rejection,
        /// Another binding of the requested name is live where the renamed one
        /// is, so the rewrite would capture or shadow it.
        name_already_in_scope,
        /// The renamed binding's extent could not be determined, so the rename
        /// could not be checked for capture at all.
        scope_unavailable,
        /// The binding's own declaration could not be pinned to exactly its
        /// name, so rewriting it would take neighbouring source with it.
        declaration_not_isolated,
    };

    /// The edits a rename produces, all within the requested document.
    pub const RenameResult = struct {
        regions: []LspRange,
        /// The name being replaced, owned by this result.
        old_name: []u8,

        pub fn deinit(self: RenameResult, allocator: std.mem.Allocator) void {
            allocator.free(self.regions);
            allocator.free(self.old_name);
        }
    };

    /// A rename request either produces edits or is refused with a reason.
    pub const RenameOutcome = union(enum) {
        edits: RenameResult,
        rejected: RenameRejection,
    };

    /// What the editor needs to open its rename prompt.
    pub const PrepareRenameResult = struct {
        /// The occurrence under the cursor, which the editor highlights.
        range: LspRange,
        /// The current name, pre-filled into the prompt. Owned by this result.
        placeholder: []u8,

        pub fn deinit(self: PrepareRenameResult, allocator: std.mem.Allocator) void {
            allocator.free(self.placeholder);
        }
    };

    /// Report whether the symbol at the given position can be renamed, and
    /// under what name the editor should prompt.
    ///
    /// Returns null when there is nothing renameable there, which the editor
    /// shows by refusing to open its rename prompt at all.
    pub fn prepareRenameAtPosition(
        self: *SyntaxChecker,
        uri: []const u8,
        override_text: ?[]const u8,
        line: u32,
        character: u32,
    ) QueryError!?PrepareRenameResult {
        self.mutex.lockUncancelable(self.std_io);
        defer self.mutex.unlock(self.std_io);

        var build = try self.prepareDocumentBuild(uri, override_text);
        defer build.deinit();

        self.logDebug(.build, "prepareRename: document {s} reused={}", .{ build.absolute_path, build.reused });

        // Rename must never be answered from a partial build: rewriting every
        // occurrence but one silently breaks the program, so refusing is the
        // only honest answer when the CIR is unavailable.
        if (!build.build_succeeded) {
            self.logDebug(.build, "prepareRename: build unavailable for {s}", .{build.absolute_path});
            return null;
        }

        const module_env = build.getModuleEnv() orelse return null;
        const target_offset = build.view(module_env).offsetAt(line, character) orelse return null;
        const target = rename_rules.targetAt(module_env, target_offset) orelse return null;
        if (cir_queries.declarationNameRegion(module_env, target.pattern) == null) return null;

        const regions = try self.collectSymbolRegions(module_env, target.pattern, true);
        defer self.allocator.free(regions);

        // An occurrence in text that staging wrote, such as the `echo!`
        // binding, is not in the document and cannot be rewritten.
        if (!build.view(module_env).allInDocument(regions)) return null;
        for (regions) |*region| region.* = build.view(module_env).rangeOf(region.*).?;

        // Prompt on the occurrence the cursor is actually in, not on the
        // definition, so the editor highlights what the user clicked.
        const cursor_range = rename_rules.rangeContaining(regions, line, character) orelse return null;

        const name = module_lookup.declaredName(module_env, target.ident);
        return PrepareRenameResult{
            .range = cursor_range,
            .placeholder = try self.allocator.dupe(u8, name),
        };
    }

    /// Produce the edits that rename the symbol at the given position.
    ///
    /// Returns null when the document could not be built; a built document
    /// with nothing renameable at that position is reported as a rejection
    /// instead, so the editor can say why.
    pub fn getRenameEditsAtPosition(
        self: *SyntaxChecker,
        uri: []const u8,
        override_text: ?[]const u8,
        line: u32,
        character: u32,
        new_name: []const u8,
    ) QueryError!?RenameOutcome {
        self.mutex.lockUncancelable(self.std_io);
        defer self.mutex.unlock(self.std_io);

        var build = try self.prepareDocumentBuild(uri, override_text);
        defer build.deinit();

        self.logDebug(.build, "rename: document {s} reused={}", .{ build.absolute_path, build.reused });

        if (!build.build_succeeded) {
            self.logDebug(.build, "rename: build unavailable for {s}", .{build.absolute_path});
            return null;
        }

        const module_env = build.getModuleEnv() orelse return null;
        const target_offset = build.view(module_env).offsetAt(line, character) orelse
            return RenameOutcome{ .rejected = .not_a_local_binding };

        const target = rename_rules.targetAt(module_env, target_offset) orelse
            return RenameOutcome{ .rejected = .not_a_local_binding };

        // Renaming the uses while leaving the declaration behind is exactly the
        // partial rewrite this must not produce.
        if (cir_queries.declarationNameRegion(module_env, target.pattern) == null) {
            return RenameOutcome{ .rejected = .declaration_not_isolated };
        }

        // An associated item binds its qualified name, but only its member
        // is written at the declaration, so only that is renamed.
        const old_name = module_lookup.declaredName(module_env, target.ident);
        if (try rename_rules.checkNewName(self.allocator, old_name, new_name)) |rejection| {
            return RenameOutcome{ .rejected = .{ .bad_new_name = rejection } };
        }

        switch (rename_rules.checkNewNameAgainstScope(try build.handle.scopeBindings(module_env), module_env, target, new_name)) {
            .clear => {},
            .taken => return RenameOutcome{ .rejected = .name_already_in_scope },
            .scope_unavailable => return RenameOutcome{ .rejected = .scope_unavailable },
        }

        const regions = try self.collectSymbolRegions(module_env, target.pattern, true);
        errdefer self.allocator.free(regions);

        // Renaming every occurrence but one in text that staging wrote, such
        // as the `echo!` binding, is the partial rewrite this must not make.
        if (!build.view(module_env).allInDocument(regions)) {
            self.allocator.free(regions);
            return RenameOutcome{ .rejected = .declaration_not_isolated };
        }
        for (regions) |*region| region.* = build.view(module_env).rangeOf(region.*).?;

        return RenameOutcome{ .edits = .{
            .regions = regions,
            .old_name = try self.allocator.dupe(u8, old_name),
        } };
    }

    /// Find the pattern_idx at the given offset.
    /// Returns the pattern being defined or referenced at that position.
    pub fn getDocumentSymbols(
        self: *SyntaxChecker,
        allocator: std.mem.Allocator,
        uri: []const u8,
        source: []const u8,
    ) QueryError![]document_symbol_handler.SymbolInformation {
        const SymbolInformation = document_symbol_handler.SymbolInformation;

        self.mutex.lockUncancelable(self.std_io);
        defer self.mutex.unlock(self.std_io);

        var build = try self.prepareDocumentBuild(uri, source);
        defer build.deinit();

        self.logDebug(.build, "symbols: document {s} reused={}", .{ build.absolute_path, build.reused });

        if (!build.build_succeeded) {
            self.logDebug(.build, "symbols: build unavailable for {s}", .{build.absolute_path});
            return &[_]SymbolInformation{};
        }

        const module_env = build.getModuleEnv() orelse return &[_]SymbolInformation{};

        // Symbols are found in the module's source and their ranges moved to
        // the document.
        const view = build.view(module_env);
        const module_source = view.moduleSource(source);

        // Build line offset table
        const line_offsets = try pos.LineOffsets.init(allocator, module_source);
        defer line_offsets.deinit();

        var symbols: std.ArrayList(SymbolInformation) = .empty;
        errdefer {
            for (symbols.items) |*sym| {
                allocator.free(sym.name);
            }
            symbols.deinit(allocator);
        }

        // Check top-level definitions (modules/apps store functions here)
        const defs_slice = module_env.store.sliceDefs(module_env.all_defs);
        self.logDebug(.build, "symbols: all_defs.len={}, all_statements.len={}", .{
            defs_slice.len,
            module_env.store.sliceStatements(module_env.all_statements).len,
        });
        for (defs_slice) |def_idx| {
            const def = module_env.store.getDef(def_idx);
            if (extractSymbolFromDecl(module_env, def.pattern, def.expr, module_source, uri, &line_offsets)) |symbol| {
                self.logDebug(.build, "symbols: found def symbol '{s}'", .{symbol.name});
                try appendOwnedSymbol(allocator, &symbols, symbol);
            }
        }

        // Also check top-level statements (some module types use these)
        const local_statements_slice = module_env.store.sliceStatements(module_env.all_statements);
        for (local_statements_slice) |stmt_idx| {
            const stmt = module_env.store.getSourceStatement(stmt_idx);
            const stmt_tag = std.meta.activeTag(stmt);
            if (stmt_tag == .s_alias_decl) {
                if (extractSymbolFromTypeDecl(module_env, stmt.s_alias_decl.header, stmt_idx, uri, &line_offsets, .class)) |symbol| {
                    self.logDebug(.build, "symbols: found alias symbol '{s}'", .{symbol.name});
                    try appendOwnedSymbol(allocator, &symbols, symbol);
                }
                continue;
            }
            if (stmt_tag == .s_nominal_decl) {
                if (extractSymbolFromTypeDecl(module_env, stmt.s_nominal_decl.header, stmt_idx, uri, &line_offsets, .@"struct")) |symbol| {
                    self.logDebug(.build, "symbols: found nominal symbol '{s}'", .{symbol.name});
                    try appendOwnedSymbol(allocator, &symbols, symbol);
                }
                continue;
            }
            if (stmt_tag == .s_where_alias_decl) {
                if (extractSymbolFromTypeDecl(module_env, stmt.s_where_alias_decl.header, stmt_idx, uri, &line_offsets, .interface)) |symbol| {
                    self.logDebug(.build, "symbols: found where alias symbol '{s}'", .{symbol.name});
                    try appendOwnedSymbol(allocator, &symbols, symbol);
                }
                continue;
            }

            const stmt_parts = module_lookup.getStatementParts(stmt);

            if (stmt_parts.pattern) |pattern_idx| {
                if (stmt_parts.expr) |expr_idx| {
                    if (extractSymbolFromDecl(module_env, pattern_idx, expr_idx, module_source, uri, &line_offsets)) |symbol| {
                        self.logDebug(.build, "symbols: found stmt symbol '{s}'", .{symbol.name});
                        try appendOwnedSymbol(allocator, &symbols, symbol);
                    }
                } else if (extractSymbolFromPattern(module_env, pattern_idx, uri, &line_offsets, .variable)) |symbol| {
                    self.logDebug(.build, "symbols: found pattern symbol '{s}'", .{symbol.name});
                    try appendOwnedSymbol(allocator, &symbols, symbol);
                }
            }
        }
        // A symbol that staging wrote, such as `echo!`, is not in the
        // document.
        var kept: usize = 0;
        for (symbols.items) |symbol| {
            const range = symbol.location.range;
            const start = view.positionOf(range.start.line, range.start.character);
            const end = view.positionOf(range.end.line, range.end.character);
            if (start == null or end == null) {
                allocator.free(symbol.name);
                continue;
            }
            symbols.items[kept] = symbol;
            symbols.items[kept].location.range = .{
                .start = .{ .line = start.?.line, .character = start.?.character },
                .end = .{ .line = end.?.line, .character = end.?.character },
            };
            kept += 1;
        }
        symbols.shrinkRetainingCapacity(kept);
        self.logDebug(.build, "symbols: returning {} symbols", .{symbols.items.len});
        return symbols.toOwnedSlice(allocator);
    }

    // CompletionContext moved to completion/context.zig
    pub const CompletionContext = completion_context.CompletionContext;

    // detectCompletionContext and computeOffset moved to completion/context.zig

    /// Resolve a local binding's type var for chained access completion.
    fn resolveLocalBindingTypeVar(builder: *completion_builder.CompletionBuilder, module_env: *ModuleEnv, name: []const u8, name_start: u32, oom: *?Allocator.Error) ?types.Var {
        const bindings = noteOom(oom, builder.scopeBindings(module_env)) orelse return null;

        for (bindings) |binding| {
            const binding_name = module_env.getIdentText(binding.ident);
            if (!scope_map.ScopeMap.isVisibleAt(binding, name_start)) continue;
            if (std.mem.eql(u8, binding_name, name)) {
                return ModuleEnv.varFrom(binding.pattern_idx);
            }
        }

        if (module_lookup.findDefinitionByName(module_env, name)) |def_info| {
            return ModuleEnv.varFrom(def_info.pattern_idx);
        }

        return null;
    }

    /// The module env whose members follow `qualifier.` in `module_env`, the
    /// module at `doc_path`. A builtin type's members are in the Builtin
    /// module.
    fn findModuleEnvForCompletion(module_lookup_env: *BuildEnv, module_env_opt: ?*ModuleEnv, doc_path: []const u8, qualifier: []const u8) ?*ModuleEnv {
        if (completion_builtins.isBuiltinType(qualifier)) return module_envs.builtin(module_lookup_env);
        const module_env = module_env_opt orelse return null;
        return module_envs.forQualifier(module_lookup_env, module_env, doc_path, qualifier);
    }

    /// Resolve the type variable for a dotted access chain (e.g., myrec.subrec).
    fn resolveAccessChainTypeVar(
        self: *SyntaxChecker,
        builder: *completion_builder.CompletionBuilder,
        module_env: *ModuleEnv,
        module_lookup_env: *BuildEnv,
        doc_path: []const u8,
        access_chain: []const u8,
        chain_start: u32,
        oom: *?Allocator.Error,
    ) ?struct { module_env: *ModuleEnv, type_var: types.Var } {
        var idx: usize = 0;
        const first = nextChainSegment(access_chain, idx) orelse return null;
        idx = first.next;

        if (first.segment.len == 0) return null;

        if (std.ascii.isUpper(first.segment[0])) {
            const resolved_env = findModuleEnvForCompletion(module_lookup_env, module_env, doc_path, first.segment) orelse module_env;
            const member = nextChainSegment(access_chain, idx) orelse return null;
            idx = member.next;

            // NOTE: Nested nominal/module members are often stored as qualified
            // identifiers (e.g. `MyType.Sub`). Prefer exact lookup first, then
            // try the qualified path and finally unqualified suffix matching.
            const def_info = findDefinitionForNamespaceMember(
                self.allocator,
                resolved_env,
                first.segment,
                member.segment,
                oom,
            ) orelse return null;
            var type_var = ModuleEnv.varFrom(def_info.pattern_idx);
            var namespace_prefix = std.ArrayList(u8).empty;
            defer namespace_prefix.deinit(self.allocator);
            noteOom(oom, namespace_prefix.appendSlice(self.allocator, first.segment)) orelse return null;
            noteOom(oom, namespace_prefix.append(self.allocator, '.')) orelse return null;
            noteOom(oom, namespace_prefix.appendSlice(self.allocator, member.segment)) orelse return null;

            while (nextChainSegment(access_chain, idx)) |segment| {
                idx = segment.next;

                // Prefer namespace/member traversal for uppercase segments before
                // falling back to structural field traversal.
                if (findDefinitionByQualifiedPrefix(self.allocator, resolved_env, namespace_prefix.items, segment.segment, oom)) |next_def| {
                    type_var = ModuleEnv.varFrom(next_def.pattern_idx);
                    noteOom(oom, namespace_prefix.append(self.allocator, '.')) orelse return null;
                    noteOom(oom, namespace_prefix.appendSlice(self.allocator, segment.segment)) orelse return null;
                    continue;
                }
                if (oom.* != null) return null;

                const next_var = (noteOom(oom, builder.getFieldTypeVarFromTypeVar(resolved_env, type_var, segment.segment)) orelse return null) orelse return null;
                type_var = next_var;

                noteOom(oom, namespace_prefix.append(self.allocator, '.')) orelse return null;
                noteOom(oom, namespace_prefix.appendSlice(self.allocator, segment.segment)) orelse return null;
            }

            return .{ .module_env = resolved_env, .type_var = type_var };
        }

        var type_var = resolveLocalBindingTypeVar(builder, module_env, first.segment, chain_start, oom) orelse return null;
        while (nextChainSegment(access_chain, idx)) |segment| {
            idx = segment.next;
            const next_var = (noteOom(oom, builder.getFieldTypeVarFromTypeVar(module_env, type_var, segment.segment)) orelse return null) orelse return null;
            type_var = next_var;
        }

        return .{ .module_env = module_env, .type_var = type_var };
    }

    /// Resolve a namespace member definition with progressively broader matching.
    ///
    /// This is tailored for completion on nested nominal/module namespaces where
    /// definitions may be stored either as unqualified names (`Sub`) or as
    /// qualified names (`MyType.Sub`).
    fn findDefinitionForNamespaceMember(
        allocator: Allocator,
        module_env: *ModuleEnv,
        namespace_prefix: []const u8,
        member_name: []const u8,
        oom: *?Allocator.Error,
    ) ?module_lookup.DefinitionInfo {
        if (module_lookup.findDefinitionByName(module_env, member_name)) |def_info| {
            return def_info;
        }

        return findDefinitionByQualifiedPrefix(allocator, module_env, namespace_prefix, member_name, oom);
    }

    /// Find a definition by building `prefix.member` and doing exact lookup.
    fn findDefinitionByQualifiedPrefix(
        allocator: Allocator,
        module_env: *ModuleEnv,
        prefix: []const u8,
        member_name: []const u8,
        oom: *?Allocator.Error,
    ) ?module_lookup.DefinitionInfo {
        const qualified = noteOom(oom, std.fmt.allocPrint(allocator, "{s}.{s}", .{ prefix, member_name })) orelse return null;
        defer allocator.free(qualified);
        return module_lookup.findDefinitionByName(module_env, qualified);
    }

    /// Get the next segment in a dotted access chain.
    fn nextChainSegment(chain: []const u8, start: usize) ?struct { segment: []const u8, next: usize } {
        if (start >= chain.len) return null;
        const dot_idx = std.mem.findScalarPos(u8, chain, start, '.') orelse chain.len;
        const segment = chain[start..dot_idx];
        const next = if (dot_idx < chain.len) dot_idx + 1 else chain.len;
        return .{ .segment = segment, .next = next };
    }

    /// Get the last segment in a dotted access chain.
    fn lastChainSegment(chain: []const u8) []const u8 {
        const dot_idx = std.mem.findScalarLast(u8, chain, '.') orelse return chain;
        if (dot_idx + 1 >= chain.len) return chain;
        return chain[dot_idx + 1 ..];
    }

    /// Extract the return type from a type variable.
    /// If the type is a function, returns its return type.
    /// Otherwise returns the type as-is (e.g., for tag constructors that are already the result type).
    fn extractReturnType(module_env: *ModuleEnv, type_var: types.Var) types.Var {
        const type_store = &module_env.types;
        var resolved = type_store.resolveVar(type_var);
        var content = resolved.desc.content;

        // Unwrap aliases first
        var steps: usize = 0;
        while (steps < 8) : (steps += 1) {
            if (std.meta.activeTag(content) != .alias) break;
            const backing_var = type_store.getAliasBackingVar(content.alias);
            resolved = type_store.resolveVar(backing_var);
            content = resolved.desc.content;
        }

        // If it's a function, return the return type
        if (content.unwrapFunc()) |func| {
            return func.ret;
        }

        // Otherwise return as-is (tag constructors, etc.)
        return type_var;
    }

    /// Get completion suggestions at a specific position in a document.
    /// Returns completions from the current module's exposed items and imports.
    /// If the build fails, still provides basic completions (builtin modules, types).
    pub fn getCompletionsAtPosition(
        self: *SyntaxChecker,
        uri: []const u8,
        override_text: ?[]const u8,
        line: u32,
        character: u32,
    ) QueryError!?completion_handler.CompletionResult {
        self.mutex.lockUncancelable(self.std_io);
        defer self.mutex.unlock(self.std_io);

        var build = try self.prepareDocumentBuild(uri, override_text);
        defer build.deinit();

        const env = build.env;

        self.logDebug(.completion, "completion: document {s} reused={}", .{ build.absolute_path, build.reused });
        self.logDebug(.completion, "completion: build_succeeded={}", .{build.build_succeeded});

        const build_has_reports = build.has_reports;

        // Detect completion context from source
        const source = override_text orelse "";
        const context = completion_context.detectCompletionContext(source, line, character);

        // Compute cursor offset for scope-based completions
        const cursor_offset = completion_context.computeOffset(source, line, character);

        // Collect completions based on context. The items and their strings
        // live in one arena that the result owns.
        var arena = base.SingleThreadArena.init(self.allocator);
        errdefer arena.deinit();
        var items: std.ArrayList(completion_handler.CompletionItem) = .empty;

        // Try to get the module environment for richer completions
        // ALWAYS try snapshot first for completion - typing usually produces incomplete code
        var used_snapshot = false;
        // Track which BuildEnv backs the chosen module_env_opt so module member
        // lookups stay consistent with snapshot/previous envs.
        var module_lookup_env: *BuildEnv = env;
        // The handle owning `module_env_opt`, which holds its scope map.
        var module_handle: *BuildEnvHandle = build.handle;
        const module_env_opt: ?*ModuleEnv = blk: {
            if (!build_has_reports) {
                if (build.getModuleEnv()) |module_env| {
                    break :blk module_env;
                }
            }

            if (self.snapshot_envs.get(build.absolute_path)) |snapshot_handle| {
                const snapshot_module_env = self.getModuleEnvByPathInEnv(snapshot_handle, build.absolute_path);
                if (snapshot_module_env) |module_env| {
                    used_snapshot = true;
                    module_lookup_env = snapshot_handle.envPtr();
                    module_handle = snapshot_handle;
                    break :blk module_env;
                }
            }

            // Fall back to previous build env if snapshot not available
            if (self.previous_build_env) |previous_handle| {
                const prev_module_env = self.getModuleEnvByPathInEnv(previous_handle, build.absolute_path);
                if (prev_module_env) |module_env| {
                    used_snapshot = true;
                    module_lookup_env = previous_handle.envPtr();
                    module_handle = previous_handle;
                    break :blk module_env;
                }
            }

            // Without a snapshot, the current build serves. A document with
            // errors still has a checked module, as hover relies on.
            if (self.getModuleLookupHandle()) |lookup_handle| {
                if (self.getModuleEnvByPathInEnv(lookup_handle, build.absolute_path)) |module_env| {
                    module_lookup_env = env;
                    module_handle = lookup_handle;
                    break :blk module_env;
                }
            }

            module_lookup_env = env;
            break :blk build.getModuleEnv();
        };

        self.logDebug(.completion, "completion: context={any}, module_env_opt={any}, build_succeeded={}, used_snapshot={}", .{ context, module_env_opt != null, build.build_succeeded, used_snapshot });

        // Offsets and the path move into the module. A cursor in a header
        // that staging rewrote has nothing in the module.
        const module_path = module_handle.modulePath(build.absolute_path);
        const module_context: CompletionContext, const module_cursor: u32 = document_view.completionContext(module_handle.staged_document, context, cursor_offset) orelse
            return .{ .items = &.{}, .is_incomplete = false, .arena = arena };

        // Initialize CompletionBuilder for deduplication and organized completion item building
        // Provide the builtin module env so completion can resolve builtin method data.
        var builder = completion_builder.CompletionBuilder.initWithDebug(self.allocator, arena.allocator(), self.std_io, &items, env.builtin_modules.builtin_module.env, module_handle, self.debug, self.log_file);
        defer builder.deinit();
        if (module_env_opt) |module_env| builder.setRequester(module_env);

        switch (module_context) {
            .after_module_dot => |module_name| {
                self.logDebug(.completion, "completion: after_module_dot for '{s}'", .{module_name});
                const imported_env = findModuleEnvForCompletion(module_lookup_env, module_env_opt, module_path, module_name);
                // Get completions from the specified module
                try builder.addModuleMemberCompletions(module_lookup_env, module_name, imported_env, module_env_opt);

                // Always add tag completions for nominal types, not just as fallback.
                // This handles e.g. `Record.` where Record is both a module and a nominal type.
                if (module_env_opt) |module_env| {
                    const added = try builder.addTagCompletionsForNominalType(module_env, module_name, null);
                    if (added) {} else {}
                }
            },
            .after_value_dot => |value_dot| {
                self.logDebug(.completion, "completion: after_value_dot for '{s}' at offset {d}", .{ value_dot.access_chain, value_dot.receiver_segment_start });
                if (module_env_opt) |module_env| {
                    var chain_resolved = false;
                    var chain_oom: ?Allocator.Error = null;
                    if (resolveAccessChainTypeVar(self, &builder, module_env, module_lookup_env, module_path, value_dot.access_chain, value_dot.chain_start, &chain_oom)) |resolved| {
                        chain_resolved = true;
                        try builder.addFieldsFromTypeVar(resolved.module_env, resolved.type_var);
                        try builder.addTupleIndexCompletions(resolved.module_env, resolved.type_var);
                        try builder.addMethodsFromTypeVar(resolved.module_env, resolved.type_var);
                    }
                    if (chain_oom) |err| return err;

                    // When the chain starts with an uppercase identifier and
                    // type-based traversal fails, try namespace-style member
                    // completion from qualified definition names.
                    var namespace_resolved = false;
                    if (!chain_resolved and value_dot.access_chain.len > 0 and std.ascii.isUpper(value_dot.access_chain[0])) {
                        namespace_resolved = try builder.addNamespaceMemberCompletions(module_env, value_dot.access_chain);
                    }

                    if (!chain_resolved and !namespace_resolved) {
                        const variable_name = lastChainSegment(value_dot.access_chain);
                        const variable_start = value_dot.receiver_segment_start;

                        // A prior complete snapshot may have a field-access node at
                        // this position. Its receiver type remains useful for this
                        // incomplete value-dot prefix; it does not select field or
                        // method semantics. Otherwise, query the preceding expression.
                        var resolved_type_var: ?types.Var = null;
                        if (cir_queries.findFieldAccessReceiverTypeVar(module_env, module_cursor)) |type_var| {
                            resolved_type_var = type_var;
                        }
                        if (resolved_type_var == null and value_dot.dot_offset > 0) {
                            if (cir_queries.findExprEndingAt(module_env, value_dot.dot_offset)) |type_at| {
                                resolved_type_var = type_at.type_var;
                            }
                        }
                        // When using snapshot, cursor positions don't correspond to snapshot CIR
                        // So we must look up by name instead of analyzing the dot expression
                        if (used_snapshot or resolved_type_var == null) {
                            self.logDebug(.completion, "completion: using name-based lookup (snapshot={}, or receiver-type lookup failed)", .{used_snapshot});
                            try builder.addRecordFieldCompletions(module_env, variable_name, variable_start);
                            self.logDebug(.completion, "completion: after addRecordFieldCompletions, items={d}", .{items.items.len});
                            try builder.addMethodCompletions(module_env, variable_name, variable_start);
                            self.logDebug(.completion, "completion: after addMethodCompletions, items={d}", .{items.items.len});
                        } else if (resolved_type_var) |type_var| {
                            self.logDebug(.completion, "completion: using CIR-based lookup with type_var={}", .{type_var});
                            try builder.addFieldsFromTypeVar(module_env, type_var);
                            try builder.addTupleIndexCompletions(module_env, type_var);
                            try builder.addMethodsFromTypeVar(module_env, type_var);
                        }
                    }
                } else {
                    self.logDebug(.completion, "completion: NO module_env for value-dot completions", .{});
                }
            },
            .after_receiver_dot => |info| {
                // Use CIR to resolve receiver types for chained calls (e.g., value.func().).
                // This avoids brittle text parsing and keeps completion tied to the AST.
                if (module_env_opt) |module_env| {
                    // A prior complete snapshot may have a field access at this
                    // position. Use only its receiver type for the unfinished
                    // prefix; field and method candidates remain independent.
                    var resolved_type_var: ?types.Var = null;
                    if (cir_queries.findFieldAccessReceiverTypeVar(module_env, module_cursor)) |type_var| {
                        resolved_type_var = type_var;
                    }
                    if (resolved_type_var == null and info.dot_offset > 0) {
                        if (cir_queries.findExprEndingAt(module_env, info.dot_offset)) |type_at| {
                            resolved_type_var = type_at.type_var;
                        }
                    }

                    if (used_snapshot or resolved_type_var == null) {
                        // CIR-based lookup failed or used snapshot (offsets don't match).
                        // Fall back to resolving the call chain textually.
                        if (info.call_chain) |call_chain| {
                            self.logDebug(.completion, "completion: after_receiver_dot fallback using call_chain='{s}'", .{call_chain});
                            var chain_oom: ?Allocator.Error = null;
                            if (resolveAccessChainTypeVar(self, &builder, module_env, module_lookup_env, module_path, call_chain, info.chain_start, &chain_oom)) |resolved| {
                                const ret_type = extractReturnType(resolved.module_env, resolved.type_var);
                                try builder.addFieldsFromTypeVar(resolved.module_env, ret_type);
                                try builder.addTupleIndexCompletions(resolved.module_env, ret_type);
                                try builder.addMethodsFromTypeVar(resolved.module_env, ret_type);
                            }
                            if (chain_oom) |err| return err;
                        } else if (resolved_type_var) |type_var| {
                            try builder.addFieldsFromTypeVar(module_env, type_var);
                            try builder.addTupleIndexCompletions(module_env, type_var);
                            try builder.addMethodsFromTypeVar(module_env, type_var);
                        } else {
                            self.logDebug(.completion, "completion: after_receiver_dot no CIR receiver type found and no call_chain", .{});
                        }
                    } else if (resolved_type_var) |type_var| {
                        self.logDebug(.completion, "completion: after_receiver_dot using CIR type_var={}", .{type_var});
                        try builder.addFieldsFromTypeVar(module_env, type_var);
                        try builder.addTupleIndexCompletions(module_env, type_var);
                        try builder.addMethodsFromTypeVar(module_env, type_var);
                    }
                } else {
                    self.logDebug(.completion, "completion: NO module_env for receiver dot completions", .{});
                }
            },
            .after_colon => {
                // Type annotation context - add type names
                if (module_env_opt) |module_env| {
                    try builder.addTypeCompletions(module_env);
                    try builder.addModuleNameCompletions(module_env);
                }
                try builder.addTypeCompletionsFromEnv(env);
                try builder.addModuleNameCompletionsFromEnv(env);
            },
            .expression => {
                // General expression context - add local definitions + module names + structural tags + nominal types
                if (module_env_opt) |module_env| {
                    try builder.addLocalCompletions(module_env, module_cursor);
                    try builder.addModuleNameCompletions(module_env);
                    try builder.addAmbientTagCompletions(module_env);
                    try builder.addTypeCompletions(module_env);
                }
                try builder.addModuleNameCompletionsFromEnv(env);
            },
        }

        // Keep completion payloads bounded so request/response processing
        // remains robust even when environments expose very large symbol sets.
        const max_completion_items: usize = 512;
        if (items.items.len > max_completion_items) {
            items.items.len = max_completion_items;
        }

        return .{
            .items = items.items,
            .is_incomplete = false,
            .arena = arena,
        };
    }
};

const completion_handler = @import("handlers/completion.zig");
const document_symbol_handler = @import("handlers/document_symbol.zig");
const pos = @import("position.zig");

// Position utilities moved to position.zig

fn appendOwnedSymbol(
    allocator: Allocator,
    symbols: *std.ArrayList(document_symbol_handler.SymbolInformation),
    symbol: document_symbol_handler.SymbolInformation,
) Allocator.Error!void {
    const owned_name = try allocator.dupe(u8, symbol.name);
    try symbols.append(allocator, .{
        .name = owned_name,
        .kind = symbol.kind,
        .location = .{
            .uri = symbol.location.uri,
            .range = symbol.location.range,
        },
    });
}

fn symbolFromRegion(
    name: []const u8,
    kind: document_symbol_handler.SymbolKind,
    uri: []const u8,
    region: Region,
    line_offsets: *const pos.LineOffsets,
) document_symbol_handler.SymbolInformation {
    return .{
        .name = name,
        .kind = kind,
        .location = .{
            .uri = uri,
            .range = .{
                .start = pos.offsetToPosition(region.start.offset, line_offsets),
                .end = pos.offsetToPosition(region.end.offset, line_offsets),
            },
        },
    };
}

fn extractSymbolFromPattern(
    module_env: *ModuleEnv,
    pattern_idx: CIR.Pattern.Idx,
    uri: []const u8,
    line_offsets: *const pos.LineOffsets,
    kind: document_symbol_handler.SymbolKind,
) ?document_symbol_handler.SymbolInformation {
    const ident_idx = module_lookup.extractIdentFromPattern(&module_env.store, pattern_idx) orelse return null;
    const name = module_env.getIdentText(ident_idx);
    if (name.len == 0) return null;

    return symbolFromRegion(
        name,
        kind,
        uri,
        module_env.store.getPatternRegion(pattern_idx),
        line_offsets,
    );
}

fn extractSymbolFromTypeDecl(
    module_env: *ModuleEnv,
    header_idx: CIR.TypeHeader.Idx,
    stmt_idx: CIR.Statement.Idx,
    uri: []const u8,
    line_offsets: *const pos.LineOffsets,
    kind: document_symbol_handler.SymbolKind,
) ?document_symbol_handler.SymbolInformation {
    const header = module_env.store.getTypeHeader(header_idx);
    const name = module_env.getIdentText(header.relative_name);
    if (name.len == 0) return null;

    return symbolFromRegion(
        name,
        kind,
        uri,
        module_env.store.getStatementRegion(stmt_idx),
        line_offsets,
    );
}

fn extractSymbolFromDecl(
    module_env: *ModuleEnv,
    pattern_idx: CIR.Pattern.Idx,
    expr_idx: CIR.Expr.Idx,
    _: []const u8,
    uri: []const u8,
    line_offsets: *const pos.LineOffsets,
) ?document_symbol_handler.SymbolInformation {
    // Check if RHS is a function
    const expr = module_env.store.getSourceExpr(expr_idx);
    const expr_tag = std.meta.activeTag(expr);
    const is_function = expr_tag == .e_closure or expr_tag == .e_lambda or expr_tag == .e_hosted_lambda;

    return extractSymbolFromPattern(
        module_env,
        pattern_idx,
        uri,
        line_offsets,
        if (is_function) .function else .variable,
    );
}

/// How much of a rendered type an inlay hint shows.
///
/// A hint is drawn inside the line it annotates, so a long one pushes the code
/// off screen. Roc's inferred types can be far longer than the code they
/// describe—a generic function carries its whole `where` clause—so the
/// label is cut and hovering the same name gives the type in full.
const max_inlay_label_bytes = 56;

/// Cut a rendered type to `max_inlay_label_bytes`, never mid-codepoint.
fn truncateTypeLabel(rendered: []const u8) []const u8 {
    if (rendered.len <= max_inlay_label_bytes) return rendered;

    var end: usize = max_inlay_label_bytes;
    // Back off any UTF-8 continuation bytes so the cut lands on a boundary.
    while (end > 0 and (rendered[end] & 0xC0) == 0x80) : (end -= 1) {}
    return rendered[0..end];
}
