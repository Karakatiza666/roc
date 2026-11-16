//! Build session management for LSP operations.
//!
//! This module encapsulates the repeated pattern of:
//! - Converting URIs to paths
//! - Creating a BuildEnv
//! - Setting up file overrides
//! - Building and draining reports
//! - Finding the module environment
//!
//! This eliminates ~40 lines of duplication across 6 functions in syntax.zig.

const std = @import("std");
const compile = @import("compile");
const can = @import("can");
const uri_util = @import("uri.zig");
const BuildEnvHandle = @import("build_env_handle.zig").BuildEnvHandle;
const StagedDocument = @import("staged_document.zig").StagedDocument;

const BuildEnv = compile.BuildEnv;
const CoreCtx = compile.CoreCtx;
const ModuleEnv = can.ModuleEnv;
const Allocator = std.mem.Allocator;

/// A single build session with automatic cleanup.
/// Encapsulates URI conversion, BuildEnv setup, building, and module lookup.
pub const BuildSession = struct {
    /// Errors that can occur while starting a build session.
    pub const InitError = Allocator.Error || std.Io.Dir.RealPathFileAllocError || StagedDocument.Error;

    allocator: Allocator,
    /// Borrowed pointer to the BuildEnv for this build. Ownership stays with the
    /// caller (typically SyntaxChecker via BuildEnvHandle); deinit does NOT free it.
    env: *BuildEnv,
    /// The handle that holds `env`.
    handle: *BuildEnvHandle,
    absolute_path: [:0]const u8,
    build_succeeded: bool,
    drained_reports: ?[]BuildEnv.DrainedModuleReports = null,

    /// Module environment from successful build (null if build failed)
    cached_module_env: ?*ModuleEnv = null,

    /// Whether we've cached the module env yet
    module_env_cached: bool = false,

    /// Initialize a build session for the given URI.
    /// This handles:
    /// - URI to path conversion
    /// - File override setup
    /// - Default-platform staging, as `roc check` stages the same file
    /// - Building (with owning main.roc / workspace package aliases when needed)
    /// - Report draining
    pub fn init(
        allocator: Allocator,
        std_io: std.Io,
        handle: *BuildEnvHandle,
        uri: []const u8,
        override_text: ?[]const u8,
        workspace_root: ?[]const u8,
        cache_config: compile.CacheConfig,
    ) InitError!BuildSession {
        const env = handle.envPtr();
        // Convert URI to path
        const path = try uri_util.uriToPath(allocator, uri);
        defer allocator.free(path);

        const absolute_path: [:0]u8 = std.Io.Dir.cwd().realPathFileAlloc(std_io, path, allocator) catch
            try allocator.dupeSentinel(u8, path, 0);
        errdefer allocator.free(absolute_path);

        // A document that runs on the default platform is checked as the app
        // `roc check` stages from it. The staged app is a file of its own, so
        // the override below never applies to it. A document that cannot be
        // read is not staged; its build reports the read failure.
        std.debug.assert(handle.staged_document == null);
        const document_text: ?[]const u8 = override_text orelse env.filesystem.readFile(absolute_path, allocator) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => null,
        };
        defer if (override_text == null) if (document_text) |text| allocator.free(text);
        if (document_text) |text| {
            if (try StagedDocument.create(allocator, std_io, env.filesystem, cache_config, absolute_path, text)) |staged| {
                handle.staged_document = staged;
                staged.configure(env);
            }
        }
        const build_path: []const u8 = if (handle.staged_document) |staged| staged.staged_path else absolute_path;

        // Set up file override if override text provided.
        // SAFETY: override lives on the stack and its address is stored in env.filesystem.
        // This is safe because env.buildResolvingMain() is synchronous and we restore the Io before returning.
        var override: CoreCtx.ReadFileOverride = undefined;
        const saved_io = env.filesystem;
        if (override_text) |text| {
            override = .{ .path = absolute_path, .content = text, .base = env.filesystem };
            env.filesystem = override.io();
        }
        errdefer if (override_text != null) {
            env.filesystem = saved_io;
        };

        const preferred_main = try preferredMainFromWorkspace(allocator, std_io, env.filesystem, workspace_root);
        defer if (preferred_main) |main_path| allocator.free(main_path);

        // Build. A canceled build has no result to report.
        const build_succeeded = blk: {
            env.buildResolvingMain(build_path, preferred_main) catch |err| switch (err) {
                error.Canceled => return error.Canceled,
                else => break :blk false,
            };
            break :blk true;
        };

        // Restore the original Io now that the build is complete.
        if (override_text != null) {
            env.filesystem = saved_io;
        }

        // Drain reports regardless of build success to capture parse errors
        // Parse errors are emitted to the sink even when build fails
        const drained_reports = try env.drainReports();

        return BuildSession{
            .allocator = allocator,
            .env = env,
            .handle = handle,
            .absolute_path = absolute_path,
            .build_succeeded = build_succeeded,
            .drained_reports = drained_reports,
        };
    }

    /// If the LSP workspace root contains `main.roc`, prefer it as the package-alias root.
    /// The workspace directory is resolved the same way as the checked file's
    /// own path, so a checked file inside a symlinked workspace directory is
    /// inside that package. The final `main.roc` component is kept as written:
    /// the package's source root is the workspace directory even when
    /// `main.roc` itself links to a file elsewhere.
    fn preferredMainFromWorkspace(
        allocator: Allocator,
        std_io: std.Io,
        filesystem: CoreCtx,
        workspace_root: ?[]const u8,
    ) InitError!?[]const u8 {
        const root = workspace_root orelse return null;
        const candidate = try std.fs.path.join(allocator, &.{ root, "main.roc" });
        defer allocator.free(candidate);
        if (!filesystem.fileExists(candidate)) return null;

        const resolved_root = try std.Io.Dir.cwd().realPathFileAlloc(std_io, root, allocator);
        defer allocator.free(resolved_root);
        return try std.fs.path.join(allocator, &.{ resolved_root, "main.roc" });
    }

    /// Clean up the build session and free allocated memory.
    pub fn deinit(self: *BuildSession) void {
        // Free drained reports
        if (self.drained_reports) |drained| {
            self.freeDrainedReports(drained);
        }

        // Free absolute path
        self.allocator.free(self.absolute_path);
    }

    /// Get the module environment from the current build.
    /// Returns null if the build failed or no module was found.
    pub fn getModuleEnv(self: *BuildSession) ?*ModuleEnv {
        if (self.module_env_cached) {
            return self.cached_module_env;
        }

        self.module_env_cached = true;

        if (!self.build_succeeded) {
            return null;
        }

        if (self.env.findModuleByPath(self.handle.modulePath(self.absolute_path))) |module_state| {
            if (module_state.moduleEnv()) |mod_env| {
                self.cached_module_env = mod_env;
                return mod_env;
            }
        }

        // Fallback: try to get the discovered root module by its package identity.
        if (self.env.discovered_pkg_name) |root_pkg_name| {
            if (self.env.rootModule(root_pkg_name)) |root| {
                if (root.moduleEnv()) |root_env| {
                    self.cached_module_env = root_env;
                    return root_env;
                }
            }
        }

        // Fallback: try to get a root module from any coordinator package.
        const coord = self.env.coordinator orelse return null;
        var pkg_it = coord.packages.iterator();
        while (pkg_it.next()) |entry| {
            const pkg = entry.value_ptr.*;
            const root_id = pkg.root_module_id orelse continue;
            const root = pkg.getModule(root_id) orelse continue;
            if (root.moduleEnv()) |root_env| {
                self.cached_module_env = root_env;
                return root_env;
            }
        }

        return null;
    }

    /// Free drained reports with their contained data.
    fn freeDrainedReports(self: *BuildSession, drained: []BuildEnv.DrainedModuleReports) void {
        for (drained) |*entry| {
            self.allocator.free(entry.abs_path);
            // Free the reports themselves
            for (entry.reports) |*report| {
                @constCast(report).deinit();
            }
            self.allocator.free(entry.reports);
        }
        self.allocator.free(drained);
    }
};
