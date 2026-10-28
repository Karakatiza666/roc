//! The reifier over a real checked module: a function written in Roc becomes
//! its normal form, which each test reads as the site's dump
//! (`reify.dump.dumpSite`): the rows the site reaches, root first, with the
//! nodes the emitter keeps.

const std = @import("std");
const base = @import("base");
const build_options = @import("build_options");
const can = @import("can");
const check = @import("check");
const reify = @import("reify");
const collections = @import("collections");
const eval = @import("eval");
const roc_target = @import("roc_target");

const Coordinator = @import("../coordinator.zig").Coordinator;
const CoreCtx = @import("ctx").CoreCtx;

const Allocator = std.mem.Allocator;
const CodeReifier = check.CodeReifier;
const ConstStore = check.ConstStore.ConstStore;
const ConstNodeId = check.ConstStore.ConstNodeId;
const CheckedExprId = check.CheckedArtifact.CheckedExprId;
const ModuleEnv = can.ModuleEnv;

/// The walk refused the body; `Staged.root` has already printed what it named.
const RejectedError = error{StagedBodyRejected};

/// Everything compiling one app end to end can fail with. Spelled out because
/// an inferred error set hides what a test can go wrong on.
const StagedError = std.mem.Allocator.Error ||
    RejectedError ||
    Coordinator.AppDiscoveryError ||
    @import("../coordinator.zig").CoordinatorError ||
    eval.BuiltinModules.InitError ||
    std.Io.Dir.CreateDirPathError ||
    std.Io.Dir.RealPathFileAllocError ||
    std.Io.Dir.WriteFileError ||
    std.Thread.SpawnError ||
    error{
        DownloadFailed,
        ExpectedPlatformString,
        FileError,
        Internal,
        InvalidDependency,
        InvalidNullByteInPath,
        InvalidUrl,
        NoCacheDir,
        NoPackageSource,
        PathOutsideWorkspace,
        StagedFixtureDidNotCheck,
        StagedLambdaNotFound,
        StagedSiteDoesNotVerify,
        UnsupportedHeader,
        UnsupportedTarget,
        WriteFailed,
    };

var shared_test_builtins: ?eval.BuiltinModules = null;
var shared_test_builtins_mutex: std.Io.Mutex = .init;

fn sharedBuiltinModules() eval.BuiltinModules.InitError!*eval.BuiltinModules {
    shared_test_builtins_mutex.lockUncancelable(std.testing.io);
    defer shared_test_builtins_mutex.unlock(std.testing.io);

    if (shared_test_builtins == null) {
        shared_test_builtins = try eval.BuiltinModules.init(std.heap.page_allocator);
    }

    return &shared_test_builtins.?;
}

const reify_fuzz = @import("../reify_fuzz.zig");
const platform_main = reify_fuzz.platform_main;
const platform_echo = reify_fuzz.platform_echo;
const StagedLookup = reify_fuzz.Lookup;
const stagedLambda = reify_fuzz.lambdaByParam;
const stagedTemplate = reify_fuzz.templateOf;

/// One app whose `wobble` function carries the body under test, compiled the
/// way `roc build` compiles it and then walked by the reifier.
///
/// Heap-allocated because the coordinator and the reifier both keep pointers
/// into fields that sit beside them here.
const Staged = struct {
    gpa: Allocator,
    tmp: std.testing.TmpDir,
    arena_impl: collections.SingleThreadArena,
    coord: Coordinator,
    store: ConstStore,
    walk: CodeReifier.Walk,
    /// Borrowed by `walk`, so it lives beside it rather than in the call that
    /// built the walk.
    foreign: StagedLookup,
    reifier: *CodeReifier.Reifier,
    env: *const ModuleEnv,
    outcome: CodeReifier.Outcome,
    /// The site's dump, or empty where the walk refused the body.
    dump: std.ArrayList(u8) = .empty,

    /// `wobble_source` declares and defines `wobble`; `main!` only has to call
    /// it, so every fixture shares one caller.
    fn create(gpa: Allocator, wobble_source: []const u8) StagedError!*Staged {
        return createRunning(gpa, wobble_source, "_staged = wobble({ time: 1.0.F32, uv: 2.0.F32 })");
    }

    /// `main_statement` is what `main!` does with `wobble`. A fixture whose
    /// parameter the app cannot build, a `Hasher` among them, leaves `wobble`
    /// uncalled: the module still checks it, which is all the walk needs.
    fn createRunning(
        gpa: Allocator,
        wobble_source: []const u8,
        main_statement: []const u8,
    ) StagedError!*Staged {
        return createNamed(gpa, wobble_source, main_statement, "input");
    }

    /// The site is the lambda whose one parameter is named `param`.
    fn createNamed(
        gpa: Allocator,
        wobble_source: []const u8,
        main_statement: []const u8,
        param: []const u8,
    ) StagedError!*Staged {
        return createSite(gpa, wobble_source, main_statement, param, null);
    }

    /// `createNamed`, beside a package `lib` holding `lib_source`.
    fn createSite(
        gpa: Allocator,
        wobble_source: []const u8,
        main_statement: []const u8,
        param: []const u8,
        lib_source: ?[]const u8,
    ) StagedError!*Staged {
        return createWalked(gpa, wobble_source, main_statement, param, lib_source, .named);
    }

    /// `createSite` for a fixture whose `main_statement` passes `wobble` to
    /// a translator: the site is walked with the cut the translator's type
    /// declares (I14), as publication walks it.
    fn createTranslated(
        gpa: Allocator,
        wobble_source: []const u8,
        main_statement: []const u8,
        lib_source: ?[]const u8,
    ) StagedError!*Staged {
        return createWalked(gpa, wobble_source, main_statement, "input", lib_source, .translated);
    }

    /// The lambda whose one parameter is named `input`, walked as a lambda
    /// written at a `Code` position inside a block: at its own type, reading
    /// the block around it. With `binds_inputs`, the site's translator
    /// returns a `Code.Bound`, so a run-time name the root reads is an input
    /// slot.
    fn createInBlock(gpa: Allocator, wobble_source: []const u8, binds_inputs: bool) StagedError!*Staged {
        return createWalked(gpa, wobble_source, "", "input", null, .{ .in_block = binds_inputs });
    }

    /// `createRunning`, walked for a `Code.Inlined(f)` site: the `inline`
    /// view (V2), which inlines every call of a helper that does not reach
    /// itself.
    fn createInlined(gpa: Allocator, wobble_source: []const u8) StagedError!*Staged {
        return createWalked(gpa, wobble_source, "", "input", null, .inlined);
    }

    /// `createRunning`, walked for a `Code.Outlined(f)` site: the `outline`
    /// view (V3), which makes a row of each computation that repeats.
    fn createOutlined(gpa: Allocator, wobble_source: []const u8) StagedError!*Staged {
        return createWalked(gpa, wobble_source, "", "input", null, .outlined);
    }

    const WalkedAs = union(enum) {
        /// A definition, at the scheme of its template.
        named,
        /// A definition, at the scheme of its template, with the cut of the
        /// translator the app's one translator call names.
        translated,
        /// A definition, at the scheme of its template, in the `inline` view.
        inlined,
        /// A definition, at the scheme of its template, in the `outline` view.
        outlined,
        /// A lambda written at the site; true when it binds inputs.
        in_block: bool,
    };

    fn createWalked(
        gpa: Allocator,
        wobble_source: []const u8,
        main_statement: []const u8,
        param: []const u8,
        lib_source: ?[]const u8,
        walked_as: WalkedAs,
    ) StagedError!*Staged {
        const self = try createCheckedWithPackage(gpa, wobble_source, main_statement, lib_source);
        const artifact = self.coord.appRootCheckedArtifact();

        const lambda = stagedLambda(artifact, self.env, param) orelse return error.StagedLambdaNotFound;

        self.store = ConstStore.init(gpa);
        self.foreign = .{
            .artifact = artifact,
            .builtins = &(try sharedBuiltinModules()).checked_artifact,
            .imports = try self.coord.collectImportedArtifactViews(self.arena_impl.allocator(), artifact),
        };
        self.walk = CodeReifier.Walk.init(gpa, &self.store, self.foreign.lookup());
        self.reifier = try self.walk.reader(.{
            .sources = CodeReifier.Reifier.artifactSources(artifact),
            .env = self.env,
        });
        switch (walked_as) {
            .named => {},
            .translated => {
                // The translator is the call the checker recorded for the
                // fixture's one translated site, found by its region: the
                // source-node map is build-only.
                const translator = for (self.env.store.codeReificationSites()) |site| {
                    if (site.translator != can.NodeStore.CodeReificationSite.no_translator) break site.translator;
                } else return error.StagedLambdaNotFound;
                const region = self.env.store.getRegionAt(@fromBackingInt(translator));
                const call = checkedCallWithRegion(artifact, region) orelse return error.StagedLambdaNotFound;
                try self.walk.useCut(self.reifier, call);
            },
            .inlined => self.walk.view = .inline_,
            .outlined => self.walk.view = .outline,
            .in_block => |binds_inputs| {
                self.walk.beginSite(.graph, binds_inputs, self.reifier);
                self.outcome = try self.reifier.reifyLambda(lambda, .{
                    .scheme = null,
                    .in_block = true,
                    .caller = self.reifier,
                    .fixed = artifact.checked_bodies.expr(lambda).ty,
                    .region = base.Region.zero(),
                });
                try self.dumpSite();
                return self;
            },
        }
        self.outcome = try self.reifier.reifyLambda(lambda, .{
            .scheme = self.reifier.templateScheme(stagedTemplate(artifact, lambda) orelse return error.StagedLambdaNotFound),
            .in_block = false,
            .caller = self.reifier,
            // Every fixture here declares `wobble` at one concrete type, so
            // the only variable its scheme quantifies is the open row of a
            // tag-union result, which no site needs to fix.
            .fixed = null,
            .region = base.Region.zero(),
        });
        try self.dumpSite();
        return self;
    }

    /// The fixture, compiled and checked, with nothing described yet.
    fn createChecked(
        gpa: Allocator,
        wobble_source: []const u8,
        main_statement: []const u8,
    ) StagedError!*Staged {
        return createCheckedWithPackage(gpa, wobble_source, main_statement, null);
    }

    /// The fixture beside a package `lib` whose one module `Lib` holds
    /// `lib_source`, where one is given.
    fn createCheckedWithPackage(
        gpa: Allocator,
        wobble_source: []const u8,
        main_statement: []const u8,
        lib_source: ?[]const u8,
    ) StagedError!*Staged {
        const self = try gpa.create(Staged);
        errdefer gpa.destroy(self);

        self.gpa = gpa;
        self.tmp = std.testing.tmpDir(.{});

        try self.tmp.dir.createDirPath(std.testing.io, ".roc_echo_platform");
        try self.tmp.dir.writeFile(std.testing.io, .{
            .sub_path = ".roc_echo_platform/main.roc",
            .data = platform_main,
        });
        try self.tmp.dir.writeFile(std.testing.io, .{
            .sub_path = ".roc_echo_platform/Echo.roc",
            .data = platform_echo,
        });

        if (lib_source) |lib| {
            try self.tmp.dir.createDirPath(std.testing.io, "lib");
            try self.tmp.dir.writeFile(std.testing.io, .{ .sub_path = "lib/main.roc", .data = "package [Lib] {}\n\nimport /Lib as Lib\n" });
            try self.tmp.dir.writeFile(std.testing.io, .{ .sub_path = "lib/Lib.roc", .data = lib });
        }
        const app_source = try std.fmt.allocPrint(gpa,
            \\app [main!] {{ pf: platform "./.roc_echo_platform/main.roc"{s} }}
            \\
            \\import pf.Echo{s}
            \\
            \\{s}
            \\
            \\main! = |_args| {{
            \\    {s}
            \\    Ok({{}})
            \\}}
            \\
        , .{
            if (lib_source != null) ", lib: \"./lib/main.roc\"" else "",
            if (lib_source != null) "\nimport lib.Lib" else "",
            wobble_source,
            main_statement,
        });
        defer gpa.free(app_source);
        try self.tmp.dir.writeFile(std.testing.io, .{ .sub_path = "main.roc", .data = app_source });

        const app_path = try self.tmp.dir.realPathFileAlloc(std.testing.io, "main.roc", gpa);
        defer gpa.free(app_path);

        self.arena_impl = collections.SingleThreadArena.init(gpa);
        const arena = self.arena_impl.allocator();

        self.coord = try Coordinator.init(
            gpa,
            .single_threaded,
            1,
            roc_target.RocTarget.detectNative(),
            try sharedBuiltinModules(),
            build_options.compiler_compatibility_id,
            null,
            CoreCtx.default(gpa, arena, std.testing.io),
        );
        self.coord.enable_hosted_transform = true;

        try self.coord.start();
        try self.coord.discoverAppFromPath(arena, .{ .entry_path = app_path });
        try self.coord.coordinatorLoop();
        if (self.coord.hasUserErrors()) {
            var reports = self.coord.iterReports();
            while (reports.next()) |entry| {
                std.debug.print("report: {s} in {s}\n", .{ entry.report.title, entry.module_name });
            }
            return error.StagedFixtureDidNotCheck;
        }

        self.env = self.coord.appRootCheckedArtifact().module_env.env();
        self.dump = .empty;
        return self;
    }

    /// A template and one call of it. `wobble` is the template, found by its
    /// own parameter names rather than by the `input` its returned lambda
    /// takes, and each entry of `arg_sources` is the source text of the
    /// argument the call writes in that position.
    ///
    /// The walk runs the way publication runs it, through
    /// `reifyTemplateCall`, so the fold is what the test observes.
    fn createTemplate(
        gpa: Allocator,
        wobble_source: []const u8,
        main_statement: []const u8,
        arg_sources: []const []const u8,
    ) StagedError!*Staged {
        const self = try createChecked(gpa, wobble_source, main_statement);
        const artifact = self.coord.appRootCheckedArtifact();

        const template = templateLambda(artifact, self.env, arg_sources.len) orelse
            return error.StagedLambdaNotFound;

        const args = try gpa.alloc(CheckedExprId, arg_sources.len);
        defer gpa.free(args);
        for (arg_sources, 0..) |text, index| {
            args[index] = checkedExprWithSource(artifact, self.env, text) orelse
                return error.StagedLambdaNotFound;
        }

        self.store = ConstStore.init(gpa);
        self.foreign = .{ .artifact = artifact, .builtins = &(try sharedBuiltinModules()).checked_artifact };
        self.walk = CodeReifier.Walk.init(gpa, &self.store, self.foreign.lookup());
        self.reifier = try self.walk.reader(.{
            .sources = CodeReifier.Reifier.artifactSources(artifact),
            .env = self.env,
        });

        var values = std.ArrayList(CodeReifier.Reifier.TemplateArg).empty;
        defer values.deinit(gpa);
        defer self.reifier.releaseTemplateArgs(values.items);
        if (try self.reifier.reifyConstants(args, &values, gpa)) |rejection| {
            self.outcome = .{ .rejected = rejection };
            return self;
        }
        self.outcome = try self.reifier.reifyTemplateCall(template, values.items, .zero());
        try self.dumpSite();
        return self;
    }

    fn destroy(self: *Staged) void {
        self.dump.deinit(self.gpa);
        self.walk.deinit();
        self.store.deinit();
        self.coord.deinit();
        self.arena_impl.deinit();
        self.tmp.cleanup();
        self.gpa.destroy(self);
    }

    /// Verify the site's IR and keep its dump. A site the verifier reports
    /// on fails the test with the report.
    fn dumpSite(self: *Staged) StagedError!void {
        if (self.outcome != .reified) return;
        const site = self.walk.site.?;
        var report = try reify.verify.verifyAll(self.gpa, &site.store, &site.types);
        defer report.deinit();
        if (!report.ok()) {
            for (report.messages.items) |message| std.debug.print("verifier: {s}\n", .{message});
            return error.StagedSiteDoesNotVerify;
        }
        var out: std.Io.Writer.Allocating = .init(self.gpa);
        defer out.deinit();
        reify.dump.dumpSite(&out.writer, self.gpa, &site.store, &site.types, self.walk.root.?) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.WriteFailed => return error.WriteFailed,
        };
        try self.dump.appendSlice(self.gpa, out.written());
    }

    /// Each node of the site's graph, by row and node, with the source text
    /// of every origin it has, the node's own first and then each call that
    /// reached it: `r0 n2: 'x * 2' < 'step(x)'`.
    fn expectProvenance(self: *Staged, expected: []const u8) (RejectedError || Allocator.Error || error{TestExpectedEqual})!void {
        if (self.outcome != .reified) return self.expectDump("");
        const published = self.walk.published.items;
        const site = published[published.len - 1];
        var out: std.ArrayList(u8) = .empty;
        defer out.deinit(self.gpa);
        const origins = &site.origins;
        for (origins.rows.items, 0..) |row, r| {
            for (0..row.len) |k| {
                const chains = origins.of(@intCast(r), @intCast(k)).?;
                try out.print(self.gpa, "r{d} n{d}:", .{ r, k });
                for (chains, 0..) |chain, c| {
                    try out.appendSlice(self.gpa, if (c == 0) " " else " | ");
                    for (origins.links.items[chain.start..][0..chain.len], 0..) |link, step| {
                        const source = site.sources[link.index()];
                        try out.print(self.gpa, "{s}'{s}'", .{ if (step == 0) "" else " < ", self.env.getSource(source.region) });
                    }
                }
                try out.append(self.gpa, '\n');
            }
        }
        try std.testing.expectEqualStrings(expected, out.items);
    }

    /// The dump of `wobble`'s `input` lambda walked again, at the scheme of
    /// its template, for a site that declares `view`, or null where the
    /// walk refused it. The caller frees the dump.
    fn viewDump(self: *Staged, view: @TypeOf(@as(CodeReifier.Walk, undefined).view)) StagedError!?[]u8 {
        const artifact = self.coord.appRootCheckedArtifact();
        const lambda = stagedLambda(artifact, self.env, "input") orelse return error.StagedLambdaNotFound;
        var store = ConstStore.init(self.gpa);
        defer store.deinit();
        var walk = CodeReifier.Walk.init(self.gpa, &store, self.foreign.lookup());
        defer walk.deinit();
        walk.view = view;
        const reifier = try walk.reader(.{ .sources = CodeReifier.Reifier.artifactSources(artifact), .env = self.env });
        const outcome = try reifier.reifyLambda(lambda, .{
            .scheme = reifier.templateScheme(stagedTemplate(artifact, lambda) orelse return error.StagedLambdaNotFound),
            .in_block = false,
            .caller = reifier,
            .fixed = null,
            .region = base.Region.zero(),
        });
        if (outcome != .reified) return null;
        const site = walk.site.?;
        var report = try reify.verify.verifyAll(self.gpa, &site.store, &site.types);
        defer report.deinit();
        if (!report.ok()) {
            for (report.messages.items) |message| std.debug.print("verifier: {s}\n", .{message});
            return error.StagedSiteDoesNotVerify;
        }
        var out: std.Io.Writer.Allocating = .init(self.gpa);
        errdefer out.deinit();
        reify.dump.dumpSite(&out.writer, self.gpa, &site.store, &site.types, walk.root.?) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.WriteFailed => return error.WriteFailed,
        };
        return try out.toOwnedSlice();
    }

    /// The site's dump, or a test failure naming what the walk refused.
    fn expectDump(self: *Staged, expected: []const u8) (RejectedError || error{TestExpectedEqual})!void {
        switch (self.outcome) {
            .reified => try std.testing.expectEqualStrings(expected, self.dump.items),
            .rejected => |rejection| {
                std.debug.print("reification rejected: {t} {s} at '{s}'\n", .{
                    rejection.kind,
                    rejection.detail,
                    self.env.getSource(rejection.region),
                });
                return error.StagedBodyRejected;
            },
        }
    }

    /// The walk refused the body, naming `detail`.
    fn expectRejected(self: *Staged, detail: []const u8) error{ TestExpectedEqual, TestUnexpectedResult }!void {
        switch (self.outcome) {
            .reified => {
                std.debug.print("reified, where a refusal was expected:\n{s}\n", .{self.dump.items});
                return error.TestUnexpectedResult;
            },
            .rejected => |rejection| try std.testing.expectEqualStrings(detail, rejection.detail),
        }
    }
};

/// The template `wobble` is defined as: a lambda taking `arg_count`
/// compile-time parameters whose body is the lambda a call describes.
fn templateLambda(
    artifact: *const check.CheckedArtifact.CheckedModuleArtifact,
    env: *const ModuleEnv,
    arg_count: usize,
) ?CheckedExprId {
    for (0..artifact.checked_bodies.exprCount()) |raw| {
        const expr_id: CheckedExprId = @fromBackingInt(@intCast(@as(u32, @intCast(raw))));
        const data = artifact.checked_bodies.expr(expr_id).data;
        if (data != .lambda) continue;
        if (data.lambda.args.len != arg_count) continue;
        const pattern = artifact.checked_bodies.pattern(data.lambda.args[0]);
        if (pattern.data != .assign) continue;
        if (std.mem.eql(u8, env.getSource(pattern.source_region), "input")) continue;
        return expr_id;
    }
    return null;
}

/// The checked expression written exactly as `text`, which is how a test names
/// one of a call's arguments: the call itself left the checked body as a
/// description, so nothing points at its arguments any more.
fn checkedExprWithSource(
    artifact: *const check.CheckedArtifact.CheckedModuleArtifact,
    env: *const ModuleEnv,
    text: []const u8,
) ?CheckedExprId {
    for (0..artifact.checked_bodies.exprCount()) |raw| {
        const expr_id: CheckedExprId = @fromBackingInt(@intCast(@as(u32, @intCast(raw))));
        const expr = artifact.checked_bodies.expr(expr_id);
        if (!std.mem.eql(u8, env.getSource(expr.source_region), text)) continue;
        return expr_id;
    }
    return null;
}

/// The checked call, direct or dispatched, written at `region`.
fn checkedCallWithRegion(
    artifact: *const check.CheckedArtifact.CheckedModuleArtifact,
    region: base.Region,
) ?CheckedExprId {
    for (0..artifact.checked_bodies.exprCount()) |raw| {
        const expr_id: CheckedExprId = @fromBackingInt(@intCast(@as(u32, @intCast(raw))));
        const expr = artifact.checked_bodies.expr(expr_id);
        if (!std.meta.eql(expr.source_region, region)) continue;
        switch (expr.data) {
            .call, .dispatch_call => return expr_id,
            else => {},
        }
    }
    return null;
}

/// A nominal whose `from_numeral` and `is_eq` are both written, so a literal
/// pattern against it names both rather than expanding either.
const count_nominal =
    \\Count := { n : U32 }.{
    \\    from_numeral : Numeral -> Try(Count, [InvalidNumeral(Str)])
    \\    from_numeral = |v| match U32.from_numeral(v) {
    \\        Ok(u) => Ok({ n: u })
    \\        Err(e) => Err(e)
    \\    }
    \\    is_eq : Count, Count -> Bool
    \\    is_eq = |a, b| a.n == b.n
    \\}
    \\
;

test "a template call folds its arguments into the description" {
    // The template's own parameter is not a name in the description: the value
    // the call fixed is written where the name was, so the stage reads a
    // literal and never learns the template existed.
    const staged = try Staged.createTemplate(
        std.testing.allocator,
        \\wobble : F32 -> Code({ time : F32, uv : F32 } -> F32)
        \\wobble = |factor| |input| input.uv * factor
    ,
        "_staged = wobble(3.5.F32)",
        &.{"3.5.F32"},
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 1(p0) : F32
        \\  n1 = float 0x40600000 : F32
        \\  n2 = Num.F32.times(n0, n1) : F32
        \\  value n2
        \\
    );
}

test "a checked function body becomes its normal form" {
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| {
        \\    wave = input.uv * 2.0.F32
        \\    wave + input.time
        \\}
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 1(p0) : F32
        \\  n1 = float 0x40000000 : F32
        \\  n2 = Num.F32.times(n0, n1) : F32
        \\  n3 = field 0(p0) : F32
        \\  n4 = Num.F32.plus(n2, n3) : F32
        \\  value n4
        \\
    );
}

test "N10: each node of a site comes from the expression that built it, and an inlined helper's node through its call" {
    const staged = try Staged.create(std.testing.allocator,
        \\step : F32 -> F32
        \\step = |x| x * 3.0.F32
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| step(input.uv) + input.time
    );
    defer staged.destroy();

    try staged.expectProvenance(
        \\r0 n0: 'input.uv'
        \\r0 n1: '3.0.F32' < 'step(input.uv)'
        \\r0 n2: 'x * 3.0.F32' < 'step(input.uv)'
        \\r0 n3: 'input.time'
        \\r0 n4: 'step(input.uv) + input.time'
        \\
    );
}

test "a plain call is a Call of the callee's row, which the site holds once" {
    const staged = try Staged.create(std.testing.allocator,
        \\step : F32 -> F32
        \\step = |x| x + 1.0.F32
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| step(input.uv) + step(step(input.time))
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 1(p0) : F32
        \\  n1 = call r1(n0) : F32
        \\  n2 = field 0(p0) : F32
        \\  n3 = call r1(n2) : F32
        \\  n4 = call r1(n3) : F32
        \\  n5 = Num.F32.plus(n1, n4) : F32
        \\  value n5
        \\row r1 (F32) -> F32
        \\  n0 = float 0x3f800000 : F32
        \\  n1 = Num.F32.plus(p0, n0) : F32
        \\  value n1
        \\
    );
}

test "a call through an alias is a Call of the row of the function it names" {
    // The checker records the lookup an exact alias forwards to, so the alias
    // and the name it forwards to reach one definition and share one row.
    const staged = try Staged.create(std.testing.allocator,
        \\step : F32 -> F32
        \\step = |x| x + 1.0.F32
        \\same : F32 -> F32
        \\same = step
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| same(input.uv) + step(input.time)
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 1(p0) : F32
        \\  n1 = call r1(n0) : F32
        \\  n2 = field 0(p0) : F32
        \\  n3 = call r1(n2) : F32
        \\  n4 = Num.F32.plus(n1, n3) : F32
        \\  value n4
        \\row r1 (F32) -> F32
        \\  n0 = float 0x3f800000 : F32
        \\  n1 = Num.F32.plus(p0, n0) : F32
        \\  value n1
        \\
    );
}

test "a derived == on a scalar is the builtin's is_eq" {
    // `==` desugars to `is_eq`, and every numeric type derives it, so the
    // checker rewrites the call to `structural_eq` before the reifier sees it.
    // A comparison against a constant is the first thing a shader body writes.
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| if input.time == 0.0.F32 input.uv else input.time
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  n1 = float 0x0 : F32
        \\  n2 = Num.F32.is_eq(n0, n1) : Bool
        \\  n4 = switch n2 : F32
        \\    arm 0
        \\      value n0
        \\    arm 1
        \\      n3 = field 1(p0) : F32
        \\      value n3
        \\  value n4
        \\
    );
}

test "a derived != on a scalar is Bool.not of the builtin's is_eq" {
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| if input.time != 0.0.F32 input.uv else input.time
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  n1 = float 0x0 : F32
        \\  n2 = Num.F32.is_eq(n0, n1) : Bool
        \\  n4 = switch n2 : F32
        \\    arm 0
        \\      n3 = field 1(p0) : F32
        \\      value n3
        \\    arm 1
        \\      value n0
        \\  value n4
        \\
    );
}

test "a hand-written is_eq describes its own body" {
    // A written `is_eq` carries a dispatch plan, so it is an ordinary method
    // call. It reads as derived only because the checker groups it with the
    // two forms that are. Its body compares with `<=`, so the description
    // shows the method rather than the backing's equality; the one call of
    // its row is inlined (V1).
    const staged = try Staged.create(std.testing.allocator,
        \\Meters := F32.{
        \\    is_eq : Meters, Meters -> Bool
        \\    is_eq = |Meters.(a), Meters.(b)| a <= b
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input|
        \\    if Meters.(input.time) == Meters.(0.0.F32) input.uv else input.time
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  n1 = float 0x0 : F32
        \\  n2 = Num.F32.is_lte(n0, n1) : Bool
        \\  n4 = switch n2 : F32
        \\    arm 0
        \\      value n0
        \\    arm 1
        \\      n3 = field 1(p0) : F32
        \\      value n3
        \\  value n4
        \\
    );
}

test "a written is_eq reached by != negates its body" {
    // Which of `==` and `!=` the author wrote rides on the dispatch plan when
    // the type writes its own `is_eq`, so a walk that reads only the checked
    // node describes the comparison the body negates: the switch on the
    // method's result has its arms swapped.
    const staged = try Staged.create(std.testing.allocator,
        \\Meters := F32.{
        \\    is_eq : Meters, Meters -> Bool
        \\    is_eq = |Meters.(a), Meters.(b)| a <= b
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input|
        \\    if Meters.(input.time) != Meters.(0.0.F32) input.uv else input.time
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  n1 = float 0x0 : F32
        \\  n2 = Num.F32.is_lte(n0, n1) : Bool
        \\  n4 = switch n2 : F32
        \\    arm 0
        \\      n3 = field 1(p0) : F32
        \\      value n3
        \\    arm 1
        \\      value n0
        \\  value n4
        \\
    );
}

test "a value a body reads twice is one node" {
    // A description names the same few strings over and over: one module name
    // per `Region`, one operator name per arithmetic node, one field name per
    // read of that field. A node id is a shared reference, so the second
    // mention is the first node.
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| input.time + input.uv + input.time
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  n1 = field 1(p0) : F32
        \\  n2 = Num.F32.plus(n0, n1) : F32
        \\  n3 = Num.F32.plus(n2, n0) : F32
        \\  value n3
        \\
    );
}

test "a derived == on a record compares every field" {
    // The recipe is a conjunction over the fields, so the reifier writes one
    // `Field` per operand per field. A `ConstNodeId` is a shared reference, so
    // naming the operand twice costs one id.
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input|
        \\    if input == { time: 0.0.F32, uv: 0.0.F32 } input.uv else input.time
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  n1 = float 0x0 : F32
        \\  n2 = Num.F32.is_eq(n0, n1) : Bool
        \\  n3 = field 1(p0) : F32
        \\  n5 = and(n2) : Bool
        \\    operand
        \\      n4 = Num.F32.is_eq(n3, n1) : Bool
        \\      value n4
        \\  n6 = switch n5 : F32
        \\    arm 0
        \\      value n0
        \\    arm 1
        \\      value n3
        \\  value n6
        \\
    );
}

test "a derived == on a nominal tuple compares every element" {
    // A nominal is transparent in the IR, so the comparison is its backing's:
    // two `Index` reads per element and no unwrapping node between.
    const staged = try Staged.create(std.testing.allocator,
        \\Pair := (F32, F32).{
        \\    is_eq : _
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input|
        \\    if Pair.((input.time, input.uv)) == Pair.((0.0.F32, 1.0.F32)) input.uv else input.time
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  n1 = float 0x0 : F32
        \\  n2 = Num.F32.is_eq(n0, n1) : Bool
        \\  n3 = field 1(p0) : F32
        \\  n6 = and(n2) : Bool
        \\    operand
        \\      n4 = float 0x3f800000 : F32
        \\      n5 = Num.F32.is_eq(n3, n4) : Bool
        \\      value n5
        \\  n7 = switch n6 : F32
        \\    arm 0
        \\      value n0
        \\    arm 1
        \\      value n3
        \\  value n7
        \\
    );
}

test "a derived to_hash threads the hasher through every component" {
    // Threading composes by return value, so the recipe is a nest of calls and
    // needs no binder. The reifier expands it rather than leaving it symbolic
    // because a hash has to agree with what Roc computes for the same value,
    // and the write widths are the compiler's to choose.
    //
    // The receiver is a record because every numeric type writes its own
    // `to_hash`; only an anonymous structural type makes the checker derive one.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : { key : U64, hasher : Hasher } -> Hasher
        \\wobble = |input| { a: input.key, b: 1.0.F32 }.to_hash(input.hasher)
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ hasher : Builtin.Hasher, key : U64 }) -> Builtin.Hasher
        \\  n0 = field 0(p0) : Builtin.Hasher
        \\  n1 = field 1(p0) : U64
        \\  n2 = Hasher.write_u64(n0, n1) : Builtin.Hasher !spec
        \\  n3 = float 0x3f800000 : F32
        \\  n4 = Hasher.write_f32(n2, n3) : Builtin.Hasher !spec
        \\  value n4
        \\
    );
}

test "a derived to_hash the walk cannot expand stays a Derived node" {
    // `List` writes its own `to_hash`, so the compiler dispatches to it rather
    // than walking the list's representation. The reifier cannot see that
    // method, so it describes none of the derivation instead of part of it.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : { keys : List(U64), hasher : Hasher } -> Hasher
        \\wobble = |input| { a: input.keys }.to_hash(input.hasher)
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ hasher : Builtin.Hasher, keys : List(U64) }) -> Builtin.Hasher
        \\  n0 = field 1(p0) : List(U64)
        \\  n1 = record(n0) : { a : List(U64) }
        \\  n2 = field 0(p0) : Builtin.Hasher
        \\  n3 = derived(n1, n2) : Builtin.Hasher !spec
        \\  value n3
        \\
    );
}

test "a derived == through a nominal component that derives its own is_eq expands the backing" {
    // The compiler dispatches to a component nominal's own `is_eq` before it
    // inspects the component's shape. The method registries say which of the
    // two this is, and a nominal that derives `is_eq` compares as its backing
    // does.
    const staged = try Staged.create(std.testing.allocator,
        \\Meters := F32.{
        \\    is_eq : _
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input|
        \\    if { m: Meters.(input.time) } == { m: Meters.(0.0.F32) } input.uv else input.time
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  n1 = float 0x0 : F32
        \\  n2 = Num.F32.is_eq(n0, n1) : Bool
        \\  n4 = switch n2 : F32
        \\    arm 0
        \\      value n0
        \\    arm 1
        \\      n3 = field 1(p0) : F32
        \\      value n3
        \\  value n4
        \\
    );
}

test "a derived == through a nominal component that writes its own is_eq describes the method" {
    // The comparison Roc performs is the method, not the backing, so the
    // description is the method's `<=`, where the backing would compare with
    // `is_eq`. Its row has one call, so V1 inlines it.
    const staged = try Staged.create(std.testing.allocator,
        \\Meters := { m: F32 }.{
        \\    is_eq : Meters, Meters -> Bool
        \\    is_eq = |a, b| a.m <= b.m
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input|
        \\    if { w: Meters.({ m: input.time }) } == { w: Meters.({ m: 0.0.F32 }) } input.uv else input.time
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  n1 = float 0x0 : F32
        \\  n2 = Num.F32.is_lte(n0, n1) : Bool
        \\  n4 = switch n2 : F32
        \\    arm 0
        \\      value n0
        \\    arm 1
        \\      n3 = field 1(p0) : F32
        \\      value n3
        \\  value n4
        \\
    );
}

test "a derived to_hash through a nominal component that writes its own to_hash describes the method" {
    // The same question, asked of the other derivation: a written `to_hash` is
    // the one Roc threads the hasher through, so the recipe is the method's
    // `U64.to_hash`, where the backing would write the field with
    // `Hasher.write_u64`. Its row has one call, so V1 inlines it.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\Meters := { m: U64 }.{
        \\    to_hash : Meters, Hasher -> Hasher
        \\    to_hash = |a, h| a.m.to_hash(h)
        \\}
        \\
        \\wobble : { key : Meters, hasher : Hasher } -> Hasher
        \\wobble = |input| { a: input.key }.to_hash(input.hasher)
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ hasher : Builtin.Hasher, key : Meters }) -> Builtin.Hasher
        \\  n0 = field 1(p0) : Meters
        \\  n1 = unwrap(n0) : { m : U64 }
        \\  n2 = field 0(n1) : U64
        \\  n3 = field 0(p0) : Builtin.Hasher
        \\  n4 = Num.U64.to_hash(n2, n3) : Builtin.Hasher !spec
        \\  value n4
        \\
    );
}

test "a generic method a derivation reaches dispatches on what its receiver fixes" {
    // The method compares its quantified field, so its body forwards the
    // `is_eq` obligation to the call that instantiated it. A derivation is
    // no call and supplies no evidence, but the receiver fixed the field's
    // type, so the target is the method that type declares.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\Boxed(a) := { v : a }.{
        \\    is_eq : Boxed(a), Boxed(a) -> Bool where [a.is_eq : a, a -> Bool]
        \\    is_eq = |x, y| x.v == y.v
        \\}
        \\
        \\wobble : { key : U64, uv : F32 } -> F32
        \\wobble = |input|
        \\    if { w: Boxed.({ v: input.key }) } == { w: Boxed.({ v: 7.U64 }) } input.uv else 0.0.F32
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ key : U64, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : U64
        \\  n3 = switch n0 : F32
        \\    arm 7
        \\      n1 = field 1(p0) : F32
        \\      value n1
        \\    default
        \\      n2 = float 0x0 : F32
        \\      value n2
        \\  value n3
        \\
    );
}

test "an opaque nominal's own method is named, not walked" {
    // The method's body reads the representation the type hides, and a
    // stage is outside the type's module, so the description is the call.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\Sealed :: { x : U64 }.{
        \\    is_eq : Sealed, Sealed -> Bool
        \\    is_eq = |a, b| a.x == b.x
        \\}
        \\
        \\wobble : { a : Sealed, b : Sealed } -> Bool
        \\wobble = |input| { m: input.a } == { m: input.b }
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ a : Sealed, b : Sealed }) -> Bool
        \\  n0 = field 0(p0) : Sealed
        \\  n1 = field 1(p0) : Sealed
        \\  n2 = Sealed.is_eq(n0, n1) : Bool !spec
        \\  value n2
        \\
    );
}

test "a generic nominal component's own is_eq describes at the instantiation its receiver fixes" {
    // A derivation reaches the method with no call site, so no dispatch edge
    // says what the method's quantified variables stand for. The receiver says
    // it: the method's first parameter is the value the derivation compares,
    // and pairing the two binds the scheme by shape. Without that pairing the
    // call keeps its name and the table holds no row for it. The body
    // compares only `tag`, so the description reads `input.k` and never
    // `v`, where a derived `is_eq` would compare both.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\Boxed(a) := { v : a, tag : U64 }.{
        \\    is_eq : Boxed(a), Boxed(a) -> Bool
        \\    is_eq = |x, y| x.tag == y.tag
        \\}
        \\
        \\wobble : { k : U64, time : F32, uv : F32 } -> F32
        \\wobble = |input|
        \\    if { w: Boxed.({ v: input.time, tag: input.k }) } == { w: Boxed.({ v: 0.0.F32, tag: 2.U64 }) } input.uv else input.time
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ k : U64, time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : U64
        \\  n3 = switch n0 : F32
        \\    arm 2
        \\      n1 = field 2(p0) : F32
        \\      value n1
        \\    default
        \\      n2 = field 1(p0) : F32
        \\      value n2
        \\  value n3
        \\
    );
}

test "a derived == through a builtin container calls the builtin's own is_eq" {
    // A builtin container declares `is_eq` the way any nominal does, and the
    // registry keys it by its builtin owner rather than by a declaration, so
    // the comparison is the call rather than a refusal at the type.
    //
    // The name here is the fallback spelling, because this harness reaches no
    // export table. A build reads one, and `test/cli/StagedNominalMethods.roc`
    // pins the export name it hands over.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : { xs : List(U16), ys : List(U16), uv : F32 } -> F32
        \\wobble = |input|
        \\    if { w: input.xs } == { w: input.ys } input.uv else 0.0.F32
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ uv : F32, xs : List(U16), ys : List(U16) }) -> F32
        \\  n0 = field 1(p0) : List(U16)
        \\  n1 = field 2(p0) : List(U16)
        \\  n2 = List.is_eq(n0, n1) : Bool
        \\  n5 = switch n2 : F32
        \\    arm 0
        \\      n3 = float 0x0 : F32
        \\      value n3
        \\    arm 1
        \\      n4 = field 0(p0) : F32
        \\      value n4
        \\  value n5
        \\
    );
}

test "Str.inspect of a builtin container calls the container's own to_inspect" {
    // `Dict` writes an eligible `to_inspect`, so it is the rendering Roc
    // produces and the description is the call, named by the builtin's export
    // name.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : { d : Dict(Str, U64), uv : F32 } -> Str
        \\wobble = |input| Str.inspect(input.d)
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ d : Builtin.Dict(Str, U64), uv : F32 }) -> Str
        \\  n0 = field 0(p0) : Builtin.Dict(Str, U64)
        \\  n1 = Dict.to_inspect(n0) : Str !spec
        \\  value n1
        \\
    );
}

test "Str.inspect of a record holding a builtin container stays a Derived node" {
    // The override applies to the subject alone. A record's rendering is the
    // compiler's default form, so the component's own `to_inspect` stays
    // inside the `Derived` rather than becoming a call beside it.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : { d : Dict(Str, U64), uv : F32 } -> Str
        \\wobble = |input| Str.inspect({ d: input.d })
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ d : Builtin.Dict(Str, U64), uv : F32 }) -> Str
        \\  n0 = field 0(p0) : Builtin.Dict(Str, U64)
        \\  n1 = record(n0) : { d : Builtin.Dict(Str, U64) }
        \\  n2 = derived(n1) : Str !spec
        \\  value n2
        \\
    );
}

test "Str.inspect of a nominal that writes an eligible to_inspect describes it" {
    // The written method is the rendering, so the description is its body.
    // Its row has one call, so V1 inlines it.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\Meters := { m : F32 }.{
        \\    to_inspect : Meters -> Str
        \\    to_inspect = |_| "meters"
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> Str
        \\wobble = |input| Str.inspect(Meters.({ m: input.time }))
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> Str
        \\  n0 = "meters" : Str
        \\  value n0
        \\
    );
}

test "Str.inspect ignores a to_inspect that is not an inspect override" {
    // `Wrap(U64) -> Str` fixes the owner's type argument, so inspection
    // ignores it (design.md "Inspect Overrides") and renders the default
    // form. Asking the registry only whether the method exists would call it.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\Wrap(a) := { v : a }.{
        \\    to_inspect : Wrap(U64) -> Str
        \\    to_inspect = |_| "wrapped"
        \\}
        \\
        \\wobble : { n : U64, uv : F32 } -> Str
        \\wobble = |input| Str.inspect(Wrap.({ v: input.n }))
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ n : U64, uv : F32 }) -> Str
        \\  n0 = field 0(p0) : U64
        \\  n1 = record(n0) : { v : U64 }
        \\  n2 = wrap(n1) : Wrap
        \\  n3 = derived(n2) : Str !spec
        \\  value n3
        \\
    );
}

test "a derived == through an opaque nominal component that derives its own is_eq is refused" {
    // An opaque nominal's `Ty` names it without its backing, so expanding that
    // backing here would describe a representation the description hides
    // everywhere else.
    //
    // The backing is a record, because an opaque over a primitive carries no
    // backing template at all and would refuse for that reason instead.
    const staged = try Staged.create(std.testing.allocator,
        \\Meters :: { m: F32 }.{
        \\    is_eq : _
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input|
        \\    if { w: Meters.({ m: input.time }) } == { w: Meters.({ m: 0.0.F32 }) } input.uv else input.time
    );
    defer staged.destroy();

    try staged.expectRejected("a value of an opaque type");
}

test "a derived == through an opaque nominal component that derives its own is_eq is left to the stage" {
    // An opaque nominal's `Ty` names it without its backing, so expanding that
    // backing here would describe a representation the description hides
    // everywhere else. The comparison is the `Derived` node, over the two
    // operands, of the type they share.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\Meters :: { m: F32 }.{
        \\    is_eq : _
        \\}
        \\
        \\wobble : { a : { w : Meters }, b : { w : Meters }, time : F32, uv : F32 } -> F32
        \\wobble = |input| if input.a == input.b input.uv else input.time
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ a : { w : Meters }, b : { w : Meters }, time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : { w : Meters }
        \\  n1 = field 0(n0) : Meters
        \\  n2 = field 1(p0) : { w : Meters }
        \\  n3 = field 0(n2) : Meters
        \\  n4 = derived(n1, n3) : Bool !spec
        \\  n7 = switch n4 : F32
        \\    arm 0
        \\      n5 = field 2(p0) : F32
        \\      value n5
        \\    arm 1
        \\      n6 = field 3(p0) : F32
        \\      value n6
        \\  value n7
        \\
    );
}

test "a derived == on an empty tag union is left to the stage" {
    // Nothing inhabits the union, so no pair of values reaches the
    // comparison: the compiler derives it over no variants.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : { a : [], b : [], time : F32, uv : F32 } -> F32
        \\wobble = |input| if input.a == input.b input.uv else input.time
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ a : [], b : [], time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : []
        \\  n1 = field 1(p0) : []
        \\  n2 = derived(n0, n1) : Bool !spec
        \\  n5 = switch n2 : F32
        \\    arm 0
        \\      n3 = field 2(p0) : F32
        \\      value n3
        \\    arm 1
        \\      n4 = field 3(p0) : F32
        \\      value n4
        \\  value n5
        \\
    );
}

test "a record literal that unsets an optional field is a Record that lists the fields it sets" {
    const staged = try Staged.create(std.testing.allocator,
        \\Cfg : { a : F32, b ?: F32, c ?: F32 }
        \\
        \\wobble : { time : F32, uv : F32 } -> Cfg
        \\wobble = |input| { a: input.uv, b: _, c: input.time }
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> { a : F32, b ? F32, c ? F32 }
        \\  n0 = field 1(p0) : F32
        \\  n1 = field 0(p0) : F32
        \\  n2 = record set a c(n0, n1) : { a : F32, b ? F32, c ? F32 }
        \\  value n2
        \\
    );
}

test "a tag union whose row nothing closed has the variants the function names" {
    const staged = try Staged.createNamed(std.testing.allocator,
        \\wobble : [Fast, Slow, ..] -> F32
        \\wobble = |mode| match mode {
        \\    Fast => 1.0.F32
        \\    _ => 0.0.F32
        \\}
    , "", "mode");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ([Fast, Slow]) -> F32
        \\  n2 = switch p0 : F32
        \\    arm 0
        \\      n0 = float 0x3f800000 : F32
        \\      value n0
        \\    arm 1
        \\      n1 = float 0x0 : F32
        \\      value n1
        \\  value n2
        \\
    );
}

test "a derived == on a type with one inhabitant is True" {
    // The fold over zero components has no comparison to make, and both
    // operands hold the only value the type has.
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| if {} == {} input.uv else input.time
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 1(p0) : F32
        \\  value n0
        \\
    );
}

test "an effectful staged function is refused" {
    // A stage runs the description during `roc build`, where an effect has
    // nowhere to happen. The lambda's own type is the one place `tyNode` never
    // looks, so the check has to sit on it directly.
    //
    // The body is pure so that nothing else refuses it: an effectful call in
    // the body stops the walk as a statement or a hosted function first, which
    // would leave the signature untested.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble! : { time : F32, uv : F32 } => F32
        \\wobble! = |input| input.time
    , "_staged = wobble!({ time: 1.0.F32, uv: 2.0.F32 })");
    defer staged.destroy();

    try staged.expectRejected("this function's own type is effectful (`=>`)");
}

test "a top-level constant folds into the description where its name stands" {
    // The value is written where the name was, so a translator never learns a
    // name stood between the body and the value. The fold is by value: no
    // capture, no closure environment, and no node beyond the literal.
    const staged = try Staged.create(std.testing.allocator,
        \\threshold = 0.5.F32
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| input.uv * threshold
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 1(p0) : F32
        \\  n1 = float 0x3f000000 : F32
        \\  n2 = Num.F32.times(n0, n1) : F32
        \\  value n2
        \\
    );
}

test "a name as a template argument folds to the value it holds" {
    // `isConstantForm` answers by written form, so a name reached the same
    // refusal a running computation did. It is the same resolution step that
    // a name in a staged body needs.
    const staged = try Staged.createTemplate(
        std.testing.allocator,
        \\factor = 3.5.F32
        \\
        \\wobble : F32 -> Code({ time : F32, uv : F32 } -> F32)
        \\wobble = |f| |input| input.uv * f
    ,
        "_staged = wobble(factor)",
        &.{"factor"},
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 1(p0) : F32
        \\  n1 = float 0x40600000 : F32
        \\  n2 = Num.F32.times(n0, n1) : F32
        \\  value n2
        \\
    );
}

test "a computed top-level value is walked where its name stands, and folds to the value it computes" {
    // The definition names only things the compiler fixes, so it is walked
    // where the name stands, the way a call to a top-level function is. Its
    // float sum is constant folding's (N13j): `0.5 + 1.0` is the `F32` 1.5.
    const staged = try Staged.create(std.testing.allocator,
        \\grow : F32 -> F32
        \\grow = |x| x + 1.0.F32
        \\
        \\threshold = grow(0.5.F32)
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| input.uv * threshold
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 1(p0) : F32
        \\  n1 = float 0x3fc00000 : F32
        \\  n2 = Num.F32.times(n0, n1) : F32
        \\  value n2
        \\
    );
}

test "a top-level value that computes a function is the lambda it holds, with its capture read as a literal" {
    // The compiler evaluates the value after the description is built, so the
    // walk reads the definition where the name stands. `make(2.0)` is the
    // call of a definition that hands back a function, and the use is one
    // `Call` of the lambda's row over the capture and then the argument.
    const staged = try Staged.create(std.testing.allocator,
        \\make : F32 -> (F32 -> F32)
        \\make = |k| |x| x * k
        \\
        \\doubler = make(2.0.F32)
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| doubler(input.uv) + doubler(input.time)
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 1(p0) : F32
        \\  n1 = float 0x40000000 : F32
        \\  n2 = call r1(n0, n1) : F32
        \\  n3 = field 0(p0) : F32
        \\  n4 = call r1(n3, n1) : F32
        \\  n5 = Num.F32.plus(n2, n4) : F32
        \\  value n5
        \\row r1 (F32, F32) -> F32
        \\  n0 = Num.F32.times(p0, p1) : F32
        \\  value n0
        \\
    );
}

test "a top-level value that computes a function, used as a value, is a Closure of the lambda's row" {
    const staged = try Staged.createRunning(
        std.testing.allocator,
        \\make : F32 -> (F32 -> F32)
        \\make = |k| |x| x * k
        \\
        \\doubler = make(2.0.F32)
        \\
        \\wobble : { time : F32, uv : List(F32) } -> List(F32)
        \\wobble = |input| input.uv.map(doubler)
    ,
        "_staged = wobble({ time: 1.0.F32, uv: [2.0.F32] })",
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : List(F32) }) -> List(F32)
        \\  n0 = field 1(p0) : List(F32)
        \\  n1 = float 0x40000000 : F32
        \\  n2 = closure r1(n1) : (F32 -> F32)
        \\  n3 = List.map(n0, n2) : List(F32) !spec
        \\  value n3
        \\row r1 (F32, F32) -> F32
        \\  n0 = Num.F32.times(p1, p0) : F32
        \\  value n0
        \\
    );
}

test "a function a top-level value that computes a function captures is a row too" {
    const staged = try Staged.create(std.testing.allocator,
        \\twice : (F32 -> F32) -> (F32 -> F32)
        \\twice = |f| |x| f(f(x))
        \\
        \\step : F32 -> F32
        \\step = |x| x + 1.0.F32
        \\
        \\quad = twice(step)
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| quad(input.uv) + quad(input.time)
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 1(p0) : F32
        \\  n1 = call r1(n0) : F32
        \\  n2 = field 0(p0) : F32
        \\  n3 = call r1(n2) : F32
        \\  n4 = Num.F32.plus(n1, n3) : F32
        \\  value n4
        \\row r1 (F32) -> F32
        \\  n0 = call r2(p0) : F32
        \\  n1 = call r2(n0) : F32
        \\  value n1
        \\row r2 (F32) -> F32
        \\  n0 = float 0x3f800000 : F32
        \\  n1 = Num.F32.plus(p0, n0) : F32
        \\  value n1
        \\
    );
}

test "a capture of a top-level value that computes a function is refused with the construct that stopped the walk" {
    // The capture is read from its definition, so a capture the walk cannot
    // describe names itself, as it does anywhere else in a described body.
    const staged = try Staged.create(std.testing.allocator,
        \\make : F32 -> (F32 -> F32)
        \\make = |k| |x| x * k
        \\
        \\doubler = make({
        \\    dbg 1.0.F32
        \\    2.0.F32
        \\})
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| doubler(input.uv)
    );
    defer staged.destroy();

    try staged.expectRejected("dbg");
}

test "a top-level value that is another computed function describes as the one it names" {
    const staged = try Staged.create(std.testing.allocator,
        \\make : F32 -> (F32 -> F32)
        \\make = |k| |x| x * k
        \\
        \\doubler = make(2.0.F32)
        \\
        \\renamed = doubler
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| renamed(input.uv)
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 1(p0) : F32
        \\  n1 = float 0x40000000 : F32
        \\  n2 = Num.F32.times(n0, n1) : F32
        \\  value n2
        \\
    );
}

test "N8l M13: a top-level value of another package that computes a function is walked by its definition" {
    // No cut lists it, so its definition is read where the name stands, as a
    // value of the site's own package is.
    const written = try Staged.createSite(std.testing.allocator,
        \\wobble : { a : F32, b : F32 } -> F32
        \\wobble = |input| Lib.doubler(input.a)
    , "", "input",
        \\Lib := {}.{
        \\    make : F32 -> (F32 -> F32)
        \\    make = |k| |x| x * k
        \\
        \\    doubler = make(2.0.F32)
        \\}
    );
    defer written.destroy();
    try written.expectDump(
        \\row r0 ({ a : F32, b : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  n1 = float 0x40000000 : F32
        \\  n2 = Num.F32.times(n0, n1) : F32
        \\  value n2
        \\
    );
}

test "N8l M13: a computed constant of another package folds to its computation" {
    const written = try Staged.createSite(std.testing.allocator,
        \\wobble : { a : F32, b : F32 } -> F32
        \\wobble = |input| input.a * Lib.limit
    , "", "input",
        \\Lib := {}.{
        \\    limit : F32
        \\    limit = 7.0.F32 * 2.0.F32
        \\}
    );
    defer written.destroy();
    try written.expectDump(
        \\row r0 ({ a : F32, b : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  n1 = float 0x41600000 : F32
        \\  n2 = Num.F32.times(n0, n1) : F32
        \\  value n2
        \\
    );
}

test "a default operand describes as the match it desugars to" {
    // `??` canonicalizes to a match with an `Ok` passthrough branch, and the
    // name that branch binds is the compiler's. The walk gives it one of its
    // own rather than refusing the branch.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\pick : Try(F32, [Bad]), F32 -> F32
        \\pick = |t, fallback| t ?? fallback
        \\
        \\wobble : { t : Try(F32, [Bad]), uv : F32 } -> F32
        \\wobble = |input| pick(input.t, input.uv)
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ t : Builtin.Try, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : Builtin.Try
        \\  n1 = unwrap(n0) : [Err([Bad]), Ok(F32)]
        \\  n4 = switch n1 : F32 !spec
        \\    arm 0
        \\      n2 = field 1(p0) : F32
        \\      value n2
        \\    arm 1
        \\      n3 = payload Ok.0(n1) : F32 !spec
        \\      value n3
        \\  value n4
        \\
    );
}

test "an as pattern keeps the name it binds beside the pattern it renames" {
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| match { v: input.time } {
        \\    { v: _ } as whole => whole.v
        \\}
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  value n0
        \\
    );
}

test "a `?` written inside an expression is an exiting switch whose continuation is the expression" {
    // M5: N13r moves the site's match into the arms of the switch below when
    // that switch has no other reader, so the dump shows one switch whose arms
    // hold the match's arms.
    // `?` desugars to the same match `??` does, with the `Err` branch
    // returning early instead of holding a default. The switch exits, and
    // the rest of the expression continues in its join; the exit rules move
    // that join into the `Ok` arm, so both arms end the row with a value.
    // The body's own type has an empty error row, because the checker
    // composes the `?` result from it (design.md "Try Return-Row
    // Composition"), so the `Ok` is built at the function's result. `pick`
    // has one call, so V1 inlines it, and the site's `match` reads the
    // switch the exit rules built.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\pick : Try(F32, [Bad]) -> Try(F32, [Bad])
        \\pick = |t| Ok(t? * 2.0.F32)
        \\
        \\wobble : { t : Try(F32, [Bad]), uv : F32 } -> F32
        \\wobble = |input| match pick(input.t) {
        \\    Ok(v) => v
        \\    Err(_) => input.uv
        \\}
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ t : Builtin.Try, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : Builtin.Try
        \\  n1 = unwrap(n0) : [Err([Bad]), Ok(F32)]
        \\  n6 = switch n1 : F32 !spec
        \\    arm 0
        \\      n2 = field 1(p0) : F32
        \\      value n2
        \\    arm 1
        \\      n3 = payload Ok.0(n1) : F32 !spec
        \\      n4 = float 0x40000000 : F32
        \\      n5 = Num.F32.times(n3, n4) : F32
        \\      value n5
        \\  value n6
        \\
    );
}

test "a `?` body that delivers a name of its narrower row conforms to the result" {
    // The body's value is bound before it is returned, so no constructor
    // stands at the return to build at the function's result. The value
    // keeps its own empty error row, and no node takes it to the result's
    // (design.md "Row Coercion Primitive": the value-only sibling of the `?`
    // return boundary). The tag keeps its name, so the `match` reads it
    // through the `Wrap` and `Unwrap` and decides on `Ok`.
    const staged = try Staged.create(std.testing.allocator,
        \\pick : Try(F32, [Bad]) -> Try(F32, [Bad])
        \\pick = |t| {
        \\    x = Ok(t? * 2.0.F32)
        \\    x
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| match pick(Ok(input.time)) {
        \\    Ok(v) => v
        \\    Err(_) => input.uv
        \\}
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  n1 = float 0x40000000 : F32
        \\  n2 = Num.F32.times(n0, n1) : F32
        \\  value n2
        \\
    );
}

test "a `?` body that delivers a name of its narrower row reaches a wider match with no node between" {
    // M5: N13r moves the site's match into the arms of the switch below when
    // that switch has no other reader, so the dump shows one switch whose arms
    // hold the match's arms.
    // The argument is not known, so the `match` stays a switch. `n8` is the
    // tag `Ok` at the narrower union of the body, which the `Wrap` takes to
    // the wider `Builtin.Try` by conformance. The tag keeps its name, and
    // the `match` reads it by name.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\pick : Try(F32, [Bad]) -> Try(F32, [Bad])
        \\pick = |t| {
        \\    x = Ok(t? * 2.0.F32)
        \\    x
        \\}
        \\
        \\wobble : { t : Try(F32, [Bad]), uv : F32 } -> F32
        \\wobble = |input| match pick(input.t) {
        \\    Ok(v) => v
        \\    Err(_) => input.uv
        \\}
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ t : Builtin.Try, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : Builtin.Try
        \\  n1 = unwrap(n0) : [Err([Bad]), Ok(F32)]
        \\  n6 = switch n1 : F32 !spec
        \\    arm 0
        \\      n2 = field 1(p0) : F32
        \\      value n2
        \\    arm 1
        \\      n3 = payload Ok.0(n1) : F32 !spec
        \\      n4 = float 0x40000000 : F32
        \\      n5 = Num.F32.times(n3, n4) : F32
        \\      value n5
        \\  value n6
        \\
    );
}

// A helper whose type does not name `Try` builds tags of a structural
// union, and a `?` on its result lifts that union into `Try` (unify.zig
// `mergeToNominal`). The use fixes the lift as it fixes a quantified
// variable, so the helper's row is built at `Try` and its tags are wrapped.

test "a `?` on the Try a block-generalized helper returns describes as the helper's body in place" {
    try expectSameNormalForm(
        \\wobble : U64 -> Try(U64, U64)
        \\wobble = |input| {
        \\    check = |m| if m < 10 Ok(m) else Err(m)
        \\    v = check(input)?
        \\    Ok(v + 1)
        \\}
    ,
        \\wobble : U64 -> Try(U64, U64)
        \\wobble = |input| if input < 10 Ok(input + 1) else Err(input)
    );
}

test "a `?` on the Try an unannotated top-level helper returns describes as the helper's body in place" {
    try expectSameNormalForm(
        \\check = |m| if m < 10 Ok(m) else Err(m)
        \\
        \\wobble : U64 -> Try(U64, U64)
        \\wobble = |input| {
        \\    v = check(input)?
        \\    Ok(v + 1)
        \\}
    ,
        \\wobble : U64 -> Try(U64, U64)
        \\wobble = |input| if input < 10 Ok(input + 1) else Err(input)
    );
}

test "a `?` on a block-generalized helper's Try in the inline view is the helper's body in place" {
    const staged = try Staged.createInlined(std.testing.allocator,
        \\wobble : U64 -> Try(U64, U64)
        \\wobble = |input| {
        \\    check = |m| if m < 10 Ok(m) else Err(m)
        \\    v = check(input)?
        \\    w = check(v + 1)?
        \\    Ok(w)
        \\}
    );
    defer staged.destroy();
    try staged.expectDump(
        \\row r0 (U64) -> Builtin.Try
        \\  n0 = 10 : U64
        \\  n1 = Num.U64.is_lt(p0, n0) : Bool
        \\  n12 = switch n1 : Builtin.Try
        \\    arm 0
        \\      n2 = tag Err(p0) : [Err(U64), Ok(U64)]
        \\      n3 = wrap(n2) : Builtin.Try
        \\      value n3
        \\    arm 1
        \\      n4 = 1 : U64
        \\      n5 = Num.U64.plus(p0, n4) : U64
        \\      n6 = Num.U64.is_lt(n5, n0) : Bool
        \\      n11 = switch n6 : Builtin.Try
        \\        arm 0
        \\          n7 = tag Err(n5) : [Err(U64), Ok(U64)]
        \\          n8 = wrap(n7) : Builtin.Try
        \\          value n8
        \\        arm 1
        \\          n9 = tag Ok(n5) : [Err(U64), Ok(U64)]
        \\          n10 = wrap(n9) : Builtin.Try
        \\          value n10
        \\      value n11
        \\  value n12
        \\
    );
}

test "a `?` on a block-generalized helper's Try, twice, keeps the helper as one row at Try" {
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : U64 -> Try(U64, U64)
        \\wobble = |input| {
        \\    check = |m| if m < 10 Ok(m) else Err(m)
        \\    v = check(input)?
        \\    w = check(v + 1)?
        \\    Ok(w)
        \\}
    , "");
    defer staged.destroy();
    try staged.expectDump(
        \\row r0 (U64) -> Builtin.Try
        \\  n0 = call r1(p0) : Builtin.Try
        \\  n1 = unwrap(n0) : [Err(U64), Ok(U64)]
        \\  n17 = switch n1 : Builtin.Try !spec
        \\    arm 0
        \\      n2 = payload Err.0(n1) : U64 !spec
        \\      n3 = tag Err(n2) : [Err(U64), Ok(U64)]
        \\      n4 = wrap(n3) : Builtin.Try
        \\      value n4
        \\    arm 1
        \\      n5 = payload Ok.0(n1) : U64 !spec
        \\      n6 = 1 : U64
        \\      n7 = Num.U64.plus(n5, n6) : U64 !spec
        \\      n8 = call r1(n7) : Builtin.Try
        \\      n9 = unwrap(n8) : [Err(U64), Ok(U64)]
        \\      n16 = switch n9 : Builtin.Try !spec
        \\        arm 0
        \\          n10 = payload Err.0(n9) : U64 !spec
        \\          n11 = tag Err(n10) : [Err(U64), Ok(U64)]
        \\          n12 = wrap(n11) : Builtin.Try
        \\          value n12
        \\        arm 1
        \\          n13 = payload Ok.0(n9) : U64 !spec
        \\          n14 = tag Ok(n13) : [Err(U64), Ok(U64)]
        \\          n15 = wrap(n14) : Builtin.Try
        \\          value n15
        \\      value n16
        \\  value n17
        \\row r1 (U64) -> Builtin.Try
        \\  n0 = 10 : U64
        \\  n1 = Num.U64.is_lt(p0, n0) : Bool
        \\  n6 = switch n1 : Builtin.Try
        \\    arm 0
        \\      n2 = tag Err(p0) : [Err(U64), Ok(U64)]
        \\      n3 = wrap(n2) : Builtin.Try
        \\      value n3
        \\    arm 1
        \\      n4 = tag Ok(p0) : [Err(U64), Ok(U64)]
        \\      n5 = wrap(n4) : Builtin.Try
        \\      value n5
        \\  value n6
        \\
    );
}

test "a block-generalized helper read at its own union and at the Try it lifts into describes at each" {
    // The two uses key two rows, one at the helper's own union and one at
    // `Try`; a key that left the lift out would give both one row. Each row
    // has one call, so V1 inlines both, and the match folds to `input`.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : U64 -> Try(U64, U64)
        \\wobble = |input| {
        \\    check = |m| if m < 10 Ok(m) else Err(m)
        \\    n = match check(input) {
        \\        Ok(x) => x
        \\        Err(e) => e
        \\    }
        \\    v = check(n)?
        \\    Ok(v + 1)
        \\}
    , "");
    defer staged.destroy();
    try staged.expectDump(
        \\row r0 (U64) -> Builtin.Try
        \\  n0 = 10 : U64
        \\  n1 = Num.U64.is_lt(p0, n0) : Bool
        \\  n8 = switch n1 : Builtin.Try
        \\    arm 0
        \\      n2 = tag Err(p0) : [Err(U64), Ok(U64)]
        \\      n3 = wrap(n2) : Builtin.Try
        \\      value n3
        \\    arm 1
        \\      n4 = 1 : U64
        \\      n5 = Num.U64.plus(p0, n4) : U64
        \\      n6 = tag Ok(n5) : [Err(U64), Ok(U64)]
        \\      n7 = wrap(n6) : Builtin.Try
        \\      value n7
        \\  value n8
        \\
    );
}

test "a `?` on a block-generalized helper's Try inside a loop returns from the loop" {
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : List(U64) -> Try(U64, U64)
        \\wobble = |input| {
        \\    check = |m| if m < 10 Ok(m) else Err(m)
        \\    var $sum = 0
        \\    for x in input {
        \\        v = check(x)?
        \\        $sum = $sum + v
        \\    }
        \\    Ok($sum)
        \\}
    , "");
    defer staged.destroy();
    try staged.expectDump(
        \\row r0 (List(U64)) -> Builtin.Try
        \\  n0 = 0 : U64
        \\  n1 = 10 : U64
        \\  n7 = for_list(p0, n0) : U64 !spec
        \\    body (s7.0: U64, s7.1: U64, s7.2: U64)
        \\      n2 = Num.U64.is_lt(s7.1, n1) : Bool
        \\      n6 = switch n2 : !spec
        \\        arm 0
        \\          n3 = tag Err(s7.1) : [Err(U64), Ok(U64)]
        \\          n4 = wrap(n3) : Builtin.Try
        \\          return n4
        \\        arm 1
        \\          n5 = Num.U64.plus(s7.2, s7.1) : U64 !spec
        \\          continue n5
        \\      branch n6
        \\  n8 = tag Ok(n7) : [Err(U64), Ok(U64)]
        \\  n9 = wrap(n8) : Builtin.Try
        \\  value n9
        \\
    );
}

test "a `?` on a block-generalized helper's Try in a match arm is that arm's switch" {
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : { a : [P, Q], n : U64 } -> Try(U64, U64)
        \\wobble = |input| {
        \\    check = |m| if m < 10 Ok(m) else Err(m)
        \\    match input.a {
        \\        P => {
        \\            v = check(input.n)?
        \\            Ok(v + 1)
        \\        }
        \\        Q => Ok(0)
        \\    }
        \\}
    , "");
    defer staged.destroy();
    try staged.expectDump(
        \\row r0 ({ a : [P, Q], n : U64 }) -> Builtin.Try
        \\  n0 = field 0(p0) : [P, Q]
        \\  n14 = switch n0 : Builtin.Try
        \\    arm 0
        \\      n1 = field 1(p0) : U64
        \\      n2 = 10 : U64
        \\      n3 = Num.U64.is_lt(n1, n2) : Bool
        \\      n10 = switch n3 : Builtin.Try
        \\        arm 0
        \\          n4 = tag Err(n1) : [Err(U64), Ok(U64)]
        \\          n5 = wrap(n4) : Builtin.Try
        \\          value n5
        \\        arm 1
        \\          n6 = 1 : U64
        \\          n7 = Num.U64.plus(n1, n6) : U64
        \\          n8 = tag Ok(n7) : [Err(U64), Ok(U64)]
        \\          n9 = wrap(n8) : Builtin.Try
        \\          value n9
        \\      value n10
        \\    arm 1
        \\      n11 = 0 : U64
        \\      n12 = tag Ok(n11) : [Err(U64), Ok(U64)]
        \\      n13 = wrap(n12) : Builtin.Try
        \\      value n13
        \\  value n14
        \\
    );
}

test "a block-generalized helper that matches a structural union, called with a Try, takes the Try" {
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : Try(U64, U64) -> U64
        \\wobble = |input| {
        \\    get = |t| match t {
        \\        Ok(v) => v
        \\        Err(_) => 0
        \\    }
        \\    get(input)
        \\}
    , "");
    defer staged.destroy();
    try staged.expectDump(
        \\row r0 (Builtin.Try) -> U64
        \\  n0 = unwrap(p0) : [Err(U64), Ok(U64)]
        \\  n3 = switch n0 : U64 !spec
        \\    arm 0
        \\      n1 = 0 : U64
        \\      value n1
        \\    arm 1
        \\      n2 = payload Ok.0(n0) : U64 !spec
        \\      value n2
        \\  value n3
        \\
    );
}

test "a block-generalized helper that builds a record, read as a nominal record, wraps it" {
    const staged = try Staged.createRunning(std.testing.allocator,
        \\Point := { x : U64, y : U64 }
        \\
        \\wobble : U64 -> Point
        \\wobble = |input| {
        \\    make = |n| { x: n, y: n + 1 }
        \\    make(input)
        \\}
    , "");
    defer staged.destroy();
    try staged.expectDump(
        \\row r0 (U64) -> Point
        \\  n0 = 1 : U64
        \\  n1 = Num.U64.plus(p0, n0) : U64 !spec
        \\  n2 = record(p0, n1) : { x : U64, y : U64 }
        \\  n3 = wrap(n2) : Point
        \\  value n3
        \\
    );
}

// T2 copies the code after a `?` into the arm that continues, after the
// switch that owns the arm was built, so node ids are not an order in which
// every reader of a node comes first. The measure (`measure.zig`) counts in
// such an order of its own.

test "a `?` in a match arm, which the exit rules continue in its Ok arm, describes" {
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : { a : [P, Q], t : Try(U64, U64) } -> Try(U64, U64)
        \\wobble = |input| match input.a {
        \\    P => {
        \\        v = input.t?
        \\        Ok(v + 1)
        \\    }
        \\    Q => Ok(0)
        \\}
    , "");
    defer staged.destroy();
    try staged.expectDump(
        \\row r0 ({ a : [P, Q], t : Builtin.Try }) -> Builtin.Try
        \\  n0 = field 0(p0) : [P, Q]
        \\  n15 = switch n0 : Builtin.Try !spec
        \\    arm 0
        \\      n1 = field 1(p0) : Builtin.Try
        \\      n2 = unwrap(n1) : [Err(U64), Ok(U64)]
        \\      n11 = switch n2 : Builtin.Try !spec
        \\        arm 0
        \\          n3 = payload Err.0(n2) : U64 !spec
        \\          n4 = tag Err(n3) : [Err(U64), Ok(U64)]
        \\          n5 = wrap(n4) : Builtin.Try
        \\          value n5
        \\        arm 1
        \\          n6 = payload Ok.0(n2) : U64 !spec
        \\          n7 = 1 : U64
        \\          n8 = Num.U64.plus(n6, n7) : U64 !spec
        \\          n9 = tag Ok(n8) : [Err(U64), Ok(U64)]
        \\          n10 = wrap(n9) : Builtin.Try
        \\          value n10
        \\      value n11
        \\    arm 1
        \\      n12 = 0 : U64
        \\      n13 = tag Ok(n12) : [Err(U64), Ok(U64)]
        \\      n14 = wrap(n13) : Builtin.Try
        \\      value n14
        \\  value n15
        \\
    );
}

test "a helper that closes a row, read at a wider union, describes as the same code written inline" {
    const inline_code = try Staged.create(std.testing.allocator,
        \\describe : [Big, Huge, Small] -> F32
        \\describe = |tag| match tag {
        \\    Big => 2.0.F32
        \\    Huge => 3.0.F32
        \\    Small => 4.0.F32
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| describe(match (if input.uv < 1.0.F32 Small else Big) {
        \\    Big => Small
        \\    Small => Big
        \\})
    );
    defer inline_code.destroy();
    const helper = try Staged.create(std.testing.allocator,
        \\describe : [Big, Huge, Small] -> F32
        \\describe = |tag| match tag {
        \\    Big => 2.0.F32
        \\    Huge => 3.0.F32
        \\    Small => 4.0.F32
        \\}
        \\
        \\size : [Big, Small] -> [Big, Small]
        \\size = |x| match x {
        \\    Big => Small
        \\    Small => Big
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| describe(size(if input.uv < 1.0.F32 Small else Big))
    );
    defer helper.destroy();
    try std.testing.expectEqualStrings(inline_code.dump.items, helper.dump.items);
}

test "a match over a helper's closed row keeps the arm of a tag only the match lists" {
    // M5: N13r moves the site's match into the arms of the switch below when
    // that switch has no other reader, so the dump shows one switch whose arms
    // hold the match's arms.
    // `size` closes its row to `[Big, Small]`, and the match lists `Huge` too.
    // The call is read at the match's union, so the tags `size` builds are
    // built at it once the call is inlined, and the match keeps its `Huge` arm.
    const staged = try Staged.create(std.testing.allocator,
        \\size : F32 -> [Big, Small]
        \\size = |x| if x < 1.0.F32 Small else Big
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| match size(input.uv) {
        \\    Big => input.uv
        \\    Huge => 3.0.F32
        \\    Small => input.time
        \\}
    );
    defer staged.destroy();
    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 1(p0) : F32
        \\  n1 = float 0x3f800000 : F32
        \\  n2 = Num.F32.is_lt(n0, n1) : Bool
        \\  n4 = switch n2 : F32
        \\    arm 0
        \\      value n0
        \\    arm 1
        \\      n3 = field 0(p0) : F32
        \\      value n3
        \\  value n4
        \\
    );
}

test "a match over a helper with one tag lists a tag the helper cannot build" {
    // The helper's own union has one member, `Small`. The call is read at the
    // match's union, and the value is known to be `Small`.
    const staged = try Staged.create(std.testing.allocator,
        \\only : F32 -> [Small]
        \\only = |_x| Small
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| match only(input.uv) {
        \\    Huge => 3.0.F32
        \\    Small => input.time
        \\}
    );
    defer staged.destroy();
    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  value n0
        \\
    );
}

test "a numeral of the author's own type describes as the conversion that makes it" {
    // The operand `from_numeral` receives is a `Num.Numeral`. The description
    // builds the `Literal` the compiler makes from the digits the author
    // wrote, calls the row of the author's `from_numeral` with it, and reads
    // the `Ok` payload of its `Try`.
    const staged = try Staged.create(std.testing.allocator,
        \\Meters := { m : F32 }.{
        \\    from_numeral : Numeral -> Try(Meters, [InvalidNumeral(Str)])
        \\    from_numeral = |n| match F32.from_numeral(n) {
        \\        Ok(v) => Ok({ m: v })
        \\        Err(e) => Err(e)
        \\    }
        \\    scale : Meters, F32 -> F32
        \\    scale = |me, f| me.m * f
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| 3.0.Meters.scale(input.uv)
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = list() : List(U8)
        \\  n1 = 1 : U64
        \\  n2 = bytes 1 : List(U8)
        \\  n3 = False : Bool
        \\  n4 = record(n0, n1, n2, n3) : { digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool }
        \\  n5 = tag Literal(n4) : [Literal({ digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool })]
        \\  n6 = wrap(n5) : Builtin.Num.Numeral
        \\  n7 = Num.F32.from_numeral(n6) : Builtin.Try !spec
        \\  n8 = unwrap(n7) : [Err([InvalidNumeral(Str)]), Ok(F32)]
        \\  n14 = switch n8 : Meters !spec
        \\    arm 0
        \\      n9 = "this literal was rejected by its conversion" : Str
        \\      n10 = crash(n9) : Meters !spec
        \\      value n10
        \\    arm 1
        \\      n11 = payload Ok.0(n8) : F32 !spec
        \\      n12 = record(n11) : { m : F32 }
        \\      n13 = wrap(n12) : Meters
        \\      value n13
        \\  n15 = unwrap(n14) : { m : F32 }
        \\  n16 = field 0(n15) : F32
        \\  n17 = field 1(p0) : F32
        \\  n18 = Num.F32.times(n16, n17) : F32
        \\  value n18
        \\
    );
}

test "a whole numeral of the author's own type is a Numeral of its digits" {
    const staged = try Staged.create(std.testing.allocator,
        \\Count := { n : U32 }.{
        \\    from_numeral : Numeral -> Try(Count, [InvalidNumeral(Str)])
        \\    from_numeral = |n| match U32.from_numeral(n) {
        \\        Ok(v) => Ok({ n: v })
        \\        Err(e) => Err(e)
        \\    }
        \\    weigh : Count, F32 -> F32
        \\    weigh = |c, f| if c.n > 2 f else 0.0.F32
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| 7.Count.weigh(input.uv)
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = 2 : U32
        \\  n1 = list() : List(U8)
        \\  n2 = 0 : U64
        \\  n3 = bytes 1 : List(U8)
        \\  n4 = False : Bool
        \\  n5 = record(n1, n2, n3, n4) : { digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool }
        \\  n6 = tag Literal(n5) : [Literal({ digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool })]
        \\  n7 = wrap(n6) : Builtin.Num.Numeral
        \\  n8 = Num.U32.from_numeral(n7) : Builtin.Try !spec
        \\  n9 = unwrap(n8) : [Err([InvalidNumeral(Str)]), Ok(U32)]
        \\  n15 = switch n9 : Count !spec
        \\    arm 0
        \\      n10 = "this literal was rejected by its conversion" : Str
        \\      n11 = crash(n10) : Count !spec
        \\      value n11
        \\    arm 1
        \\      n12 = payload Ok.0(n9) : U32 !spec
        \\      n13 = record(n12) : { n : U32 }
        \\      n14 = wrap(n13) : Count
        \\      value n14
        \\  n16 = unwrap(n15) : { n : U32 }
        \\  n17 = field 0(n16) : U32
        \\  n18 = Num.U32.is_lt(n0, n17) : Bool
        \\  n21 = switch n18 : F32
        \\    arm 0
        \\      n19 = float 0x0 : F32
        \\      value n19
        \\    arm 1
        \\      n20 = field 1(p0) : F32
        \\      value n20
        \\  value n21
        \\
    );
}

test "a quoted literal of the author's own type describes as its conversion" {
    // `from_quote` receives the post-escape bytes, so the description carries
    // them as a `Str`, calls the row of the conversion with it, and reads the
    // `Ok` payload of its `Try`.
    const staged = try Staged.create(std.testing.allocator,
        \\Name := { text : Str }.{
        \\    from_quote : Str -> Try(Name, [BadQuotedBytes(Str)])
        \\    from_quote = |s| Ok({ text: s })
        \\    width : Name, F32 -> F32
        \\    width = |n, f| if n.text.is_empty() 0.0.F32 else f
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| "hi".Name.width(input.uv)
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = "hi" : Str
        \\  n1 = Str.is_empty(n0) : Bool !spec
        \\  n4 = switch n1 : F32
        \\    arm 0
        \\      n2 = field 1(p0) : F32
        \\      value n2
        \\    arm 1
        \\      n3 = float 0x0 : F32
        \\      value n3
        \\  value n4
        \\
    );
}

test "a numeral pattern of the author's own type carries its conversion as a condition" {
    // The checker turns the pattern into a binder and an equality against the
    // converted literal. The description keeps both, so a translator reads the
    // comparison the program performs rather than a literal it does not.
    const staged = try Staged.create(std.testing.allocator, count_nominal ++
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| match if input.uv > 0.0 7.Count else 8.Count {
        \\    7 => input.uv
        \\    _ => input.time
        \\}
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = float 0x0 : F32
        \\  n1 = field 1(p0) : F32
        \\  n2 = Num.F32.is_lt(n0, n1) : Bool
        \\  n3 = list() : List(U8)
        \\  n4 = 0 : U64
        \\  n6 = False : Bool
        \\  n16 = bytes 1 : List(U8)
        \\  n17 = record(n3, n4, n16, n6) : { digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool }
        \\  n18 = tag Literal(n17) : [Literal({ digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool })]
        \\  n19 = wrap(n18) : Builtin.Num.Numeral
        \\  n20 = call r1(n19) : Builtin.Try !spec
        \\  n21 = unwrap(n20) : [Err([InvalidNumeral(Str)]), Ok(Count)]
        \\  n26 = switch n2 : Count !spec
        \\    arm 0
        \\      n5 = bytes 1 : List(U8)
        \\      n7 = record(n3, n4, n5, n6) : { digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool }
        \\      n8 = tag Literal(n7) : [Literal({ digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool })]
        \\      n9 = wrap(n8) : Builtin.Num.Numeral
        \\      n10 = call r1(n9) : Builtin.Try !spec
        \\      n11 = unwrap(n10) : [Err([InvalidNumeral(Str)]), Ok(Count)]
        \\      n15 = switch n11 : Count !spec
        \\        arm 0
        \\          n12 = "this literal was rejected by its conversion" : Str
        \\          n13 = crash(n12) : Count !spec
        \\          value n13
        \\        arm 1
        \\          n14 = payload Ok.0(n11) : Count !spec
        \\          value n14
        \\      value n15
        \\    arm 1
        \\      n25 = switch n21 : Count !spec
        \\        arm 0
        \\          n22 = "this literal was rejected by its conversion" : Str
        \\          n23 = crash(n22) : Count !spec
        \\          value n23
        \\        arm 1
        \\          n24 = payload Ok.0(n21) : Count !spec
        \\          value n24
        \\      value n25
        \\  n27 = unwrap(n26) : { n : U32 }
        \\  n28 = field 0(n27) : U32
        \\  n32 = switch n21 : Count !spec
        \\    arm 0
        \\      n29 = "this literal was rejected by its conversion" : Str
        \\      n30 = crash(n29) : Count !spec
        \\      value n30
        \\    arm 1
        \\      n31 = payload Ok.0(n21) : Count !spec
        \\      value n31
        \\  n33 = unwrap(n32) : { n : U32 }
        \\  n34 = field 0(n33) : U32
        \\  n35 = Num.U32.is_eq(n28, n34) : Bool
        \\  n37 = switch n35 : F32
        \\    arm 0
        \\      n36 = field 0(p0) : F32
        \\      value n36
        \\    arm 1
        \\      value n1
        \\  value n37
        \\row r1 (Builtin.Num.Numeral) -> Builtin.Try
        \\  n0 = Num.U32.from_numeral(p0) : Builtin.Try !spec
        \\  n1 = unwrap(n0) : [Err([InvalidNumeral(Str)]), Ok(U32)]
        \\  n10 = switch n1 : Builtin.Try !spec
        \\    arm 0
        \\      n2 = payload Err.0(n1) : [InvalidNumeral(Str)] !spec
        \\      n3 = tag Err(n2) : [Err([InvalidNumeral(Str)]), Ok(Count)]
        \\      n4 = wrap(n3) : Builtin.Try
        \\      value n4
        \\    arm 1
        \\      n5 = payload Ok.0(n1) : U32 !spec
        \\      n6 = record(n5) : { n : U32 }
        \\      n7 = wrap(n6) : Count
        \\      n8 = tag Ok(n7) : [Err([InvalidNumeral(Str)]), Ok(Count)]
        \\      n9 = wrap(n8) : Builtin.Try
        \\      value n9
        \\  value n10
        \\
    );
}

test "each alternative of a branch carries its own condition" {
    // This is what a branch-level guard cannot hold: the two conditions read
    // two binders, and each holds for one alternative only.
    const staged = try Staged.create(std.testing.allocator, count_nominal ++
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| match if input.uv > 0.0 7.Count else 8.Count {
        \\    7 | 8 => input.uv
        \\    _ => input.time
        \\}
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = float 0x0 : F32
        \\  n1 = field 1(p0) : F32
        \\  n2 = Num.F32.is_lt(n0, n1) : Bool
        \\  n3 = list() : List(U8)
        \\  n4 = 0 : U64
        \\  n6 = False : Bool
        \\  n16 = bytes 1 : List(U8)
        \\  n17 = record(n3, n4, n16, n6) : { digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool }
        \\  n18 = tag Literal(n17) : [Literal({ digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool })]
        \\  n19 = wrap(n18) : Builtin.Num.Numeral
        \\  n20 = call r1(n19) : Builtin.Try !spec
        \\  n21 = unwrap(n20) : [Err([InvalidNumeral(Str)]), Ok(Count)]
        \\  n26 = switch n2 : Count !spec
        \\    arm 0
        \\      n5 = bytes 1 : List(U8)
        \\      n7 = record(n3, n4, n5, n6) : { digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool }
        \\      n8 = tag Literal(n7) : [Literal({ digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool })]
        \\      n9 = wrap(n8) : Builtin.Num.Numeral
        \\      n10 = call r1(n9) : Builtin.Try !spec
        \\      n11 = unwrap(n10) : [Err([InvalidNumeral(Str)]), Ok(Count)]
        \\      n15 = switch n11 : Count !spec
        \\        arm 0
        \\          n12 = "this literal was rejected by its conversion" : Str
        \\          n13 = crash(n12) : Count !spec
        \\          value n13
        \\        arm 1
        \\          n14 = payload Ok.0(n11) : Count !spec
        \\          value n14
        \\      value n15
        \\    arm 1
        \\      n25 = switch n21 : Count !spec
        \\        arm 0
        \\          n22 = "this literal was rejected by its conversion" : Str
        \\          n23 = crash(n22) : Count !spec
        \\          value n23
        \\        arm 1
        \\          n24 = payload Ok.0(n21) : Count !spec
        \\          value n24
        \\      value n25
        \\  n30 = switch n21 : Count !spec
        \\    arm 0
        \\      n27 = "this literal was rejected by its conversion" : Str
        \\      n28 = crash(n27) : Count !spec
        \\      value n28
        \\    arm 1
        \\      n29 = payload Ok.0(n21) : Count !spec
        \\      value n29
        \\  n31 = call r2(n26, n30) : Bool
        \\  n43 = or(n31) : Bool !spec
        \\    operand
        \\      n32 = bytes 1 : List(U8)
        \\      n33 = record(n3, n4, n32, n6) : { digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool }
        \\      n34 = tag Literal(n33) : [Literal({ digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool })]
        \\      n35 = wrap(n34) : Builtin.Num.Numeral
        \\      n36 = call r1(n35) : Builtin.Try !spec
        \\      n37 = unwrap(n36) : [Err([InvalidNumeral(Str)]), Ok(Count)]
        \\      n41 = switch n37 : Count !spec
        \\        arm 0
        \\          n38 = "this literal was rejected by its conversion" : Str
        \\          n39 = crash(n38) : Count !spec
        \\          value n39
        \\        arm 1
        \\          n40 = payload Ok.0(n37) : Count !spec
        \\          value n40
        \\      n42 = call r2(n26, n41) : Bool
        \\      value n42
        \\  n45 = switch n43 : F32
        \\    arm 0
        \\      n44 = field 0(p0) : F32
        \\      value n44
        \\    arm 1
        \\      value n1
        \\  value n45
        \\row r1 (Builtin.Num.Numeral) -> Builtin.Try
        \\  n0 = Num.U32.from_numeral(p0) : Builtin.Try !spec
        \\  n1 = unwrap(n0) : [Err([InvalidNumeral(Str)]), Ok(U32)]
        \\  n10 = switch n1 : Builtin.Try !spec
        \\    arm 0
        \\      n2 = payload Err.0(n1) : [InvalidNumeral(Str)] !spec
        \\      n3 = tag Err(n2) : [Err([InvalidNumeral(Str)]), Ok(Count)]
        \\      n4 = wrap(n3) : Builtin.Try
        \\      value n4
        \\    arm 1
        \\      n5 = payload Ok.0(n1) : U32 !spec
        \\      n6 = record(n5) : { n : U32 }
        \\      n7 = wrap(n6) : Count
        \\      n8 = tag Ok(n7) : [Err([InvalidNumeral(Str)]), Ok(Count)]
        \\      n9 = wrap(n8) : Builtin.Try
        \\      value n9
        \\  value n10
        \\row r2 (Count, Count) -> Bool
        \\  n0 = unwrap(p0) : { n : U32 }
        \\  n1 = field 0(n0) : U32
        \\  n2 = unwrap(p1) : { n : U32 }
        \\  n3 = field 0(n2) : U32
        \\  n4 = Num.U32.is_eq(n1, n3) : Bool
        \\  value n4
        \\
    );
}

test "a literal pattern inside a variant keeps its condition where it stands" {
    const staged = try Staged.create(std.testing.allocator, count_nominal ++
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| match if input.uv > 0.0 Ok(7.Count) else Err(Bad) {
        \\    Ok(7) => input.uv
        \\    Ok(_) => input.time
        \\    Err(_) => input.time
        \\}
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = float 0x0 : F32
        \\  n1 = field 1(p0) : F32
        \\  n2 = Num.F32.is_lt(n0, n1) : Bool
        \\  n21 = and(n2) : Bool !spec
        \\    operand
        \\      n3 = list() : List(U8)
        \\      n4 = 0 : U64
        \\      n5 = bytes 1 : List(U8)
        \\      n6 = False : Bool
        \\      n7 = record(n3, n4, n5, n6) : { digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool }
        \\      n8 = tag Literal(n7) : [Literal({ digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool })]
        \\      n9 = wrap(n8) : Builtin.Num.Numeral
        \\      n10 = Num.U32.from_numeral(n9) : Builtin.Try !spec
        \\      n11 = unwrap(n10) : [Err([InvalidNumeral(Str)]), Ok(U32)]
        \\      n17 = switch n11 : Count !spec
        \\        arm 0
        \\          n12 = "this literal was rejected by its conversion" : Str
        \\          n13 = crash(n12) : Count !spec
        \\          value n13
        \\        arm 1
        \\          n14 = payload Ok.0(n11) : U32 !spec
        \\          n15 = record(n14) : { n : U32 }
        \\          n16 = wrap(n15) : Count
        \\          value n16
        \\      n18 = unwrap(n17) : { n : U32 }
        \\      n19 = field 0(n18) : U32
        \\      n20 = Num.U32.is_eq(n19, n19) : Bool
        \\      value n20
        \\  n23 = switch n21 : F32
        \\    arm 0
        \\      n22 = field 0(p0) : F32
        \\      value n22
        \\    arm 1
        \\      value n1
        \\  value n23
        \\
    );
}

test "a quoted pattern of the author's own type carries its conversion too" {
    const staged = try Staged.create(std.testing.allocator,
        \\Name := { text : Str }.{
        \\    from_quote : Str -> Try(Name, [BadQuotedBytes(Str)])
        \\    from_quote = |s| Ok({ text: s })
        \\    is_eq : Name, Name -> Bool
        \\    is_eq = |a, b| a.text == b.text
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| match if input.uv > 0.0 "hi".Name else "bye".Name {
        \\    "hi" => input.uv
        \\    _ => input.time
        \\}
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = float 0x0 : F32
        \\  n1 = field 1(p0) : F32
        \\  n2 = Num.F32.is_lt(n0, n1) : Bool
        \\  n10 = "hi" : Str
        \\  n11 = call r1(n10) : Builtin.Try
        \\  n12 = unwrap(n11) : [Err([BadQuotedBytes(Str)]), Ok(Name)]
        \\  n17 = switch n2 : Name !spec
        \\    arm 0
        \\      n3 = "bye" : Str
        \\      n4 = call r1(n3) : Builtin.Try
        \\      n5 = unwrap(n4) : [Err([BadQuotedBytes(Str)]), Ok(Name)]
        \\      n9 = switch n5 : Name !spec
        \\        arm 0
        \\          n6 = "this literal was rejected by its conversion" : Str
        \\          n7 = crash(n6) : Name !spec
        \\          value n7
        \\        arm 1
        \\          n8 = payload Ok.0(n5) : Name !spec
        \\          value n8
        \\      value n9
        \\    arm 1
        \\      n16 = switch n12 : Name !spec
        \\        arm 0
        \\          n13 = "this literal was rejected by its conversion" : Str
        \\          n14 = crash(n13) : Name !spec
        \\          value n14
        \\        arm 1
        \\          n15 = payload Ok.0(n12) : Name !spec
        \\          value n15
        \\      value n16
        \\  n18 = unwrap(n17) : { text : Str }
        \\  n19 = field 0(n18) : Str
        \\  n23 = switch n12 : Name !spec
        \\    arm 0
        \\      n20 = "this literal was rejected by its conversion" : Str
        \\      n21 = crash(n20) : Name !spec
        \\      value n21
        \\    arm 1
        \\      n22 = payload Ok.0(n12) : Name !spec
        \\      value n22
        \\  n24 = unwrap(n23) : { text : Str }
        \\  n25 = field 0(n24) : Str
        \\  n26 = Str.is_eq(n19, n25) : Bool
        \\  n28 = switch n26 : F32
        \\    arm 0
        \\      n27 = field 0(p0) : F32
        \\      value n27
        \\    arm 1
        \\      value n1
        \\  value n28
        \\row r1 (Str) -> Builtin.Try
        \\  n0 = record(p0) : { text : Str }
        \\  n1 = wrap(n0) : Name
        \\  n2 = tag Ok(n1) : [Err([BadQuotedBytes(Str)]), Ok(Name)]
        \\  n3 = wrap(n2) : Builtin.Try
        \\  value n3
        \\
    );
}

test "a derived equality expands inside the condition it stands in" {
    // `is_eq : _` derives the comparison, so the condition is the field walk
    // the compiler performs rather than a name a translator resolves.
    const staged = try Staged.create(std.testing.allocator,
        \\Count := { n : U32 }.{
        \\    is_eq : _
        \\    from_numeral : Numeral -> Try(Count, [InvalidNumeral(Str)])
        \\    from_numeral = |v| match U32.from_numeral(v) {
        \\        Ok(u) => Ok({ n: u })
        \\        Err(e) => Err(e)
        \\    }
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| match if input.uv > 0.0 7.Count else 8.Count {
        \\    7 => input.uv
        \\    _ => input.time
        \\}
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = float 0x0 : F32
        \\  n1 = field 1(p0) : F32
        \\  n2 = Num.F32.is_lt(n0, n1) : Bool
        \\  n3 = list() : List(U8)
        \\  n4 = 0 : U64
        \\  n6 = False : Bool
        \\  n16 = bytes 1 : List(U8)
        \\  n17 = record(n3, n4, n16, n6) : { digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool }
        \\  n18 = tag Literal(n17) : [Literal({ digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool })]
        \\  n19 = wrap(n18) : Builtin.Num.Numeral
        \\  n20 = call r1(n19) : Builtin.Try !spec
        \\  n21 = unwrap(n20) : [Err([InvalidNumeral(Str)]), Ok(Count)]
        \\  n26 = switch n2 : Count !spec
        \\    arm 0
        \\      n5 = bytes 1 : List(U8)
        \\      n7 = record(n3, n4, n5, n6) : { digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool }
        \\      n8 = tag Literal(n7) : [Literal({ digits_after_pt : List(U8), digits_after_pt_count : U64, digits_before_pt : List(U8), is_negative : Bool })]
        \\      n9 = wrap(n8) : Builtin.Num.Numeral
        \\      n10 = call r1(n9) : Builtin.Try !spec
        \\      n11 = unwrap(n10) : [Err([InvalidNumeral(Str)]), Ok(Count)]
        \\      n15 = switch n11 : Count !spec
        \\        arm 0
        \\          n12 = "this literal was rejected by its conversion" : Str
        \\          n13 = crash(n12) : Count !spec
        \\          value n13
        \\        arm 1
        \\          n14 = payload Ok.0(n11) : Count !spec
        \\          value n14
        \\      value n15
        \\    arm 1
        \\      n25 = switch n21 : Count !spec
        \\        arm 0
        \\          n22 = "this literal was rejected by its conversion" : Str
        \\          n23 = crash(n22) : Count !spec
        \\          value n23
        \\        arm 1
        \\          n24 = payload Ok.0(n21) : Count !spec
        \\          value n24
        \\      value n25
        \\  n27 = unwrap(n26) : { n : U32 }
        \\  n28 = field 0(n27) : U32
        \\  n32 = switch n21 : Count !spec
        \\    arm 0
        \\      n29 = "this literal was rejected by its conversion" : Str
        \\      n30 = crash(n29) : Count !spec
        \\      value n30
        \\    arm 1
        \\      n31 = payload Ok.0(n21) : Count !spec
        \\      value n31
        \\  n33 = unwrap(n32) : { n : U32 }
        \\  n34 = field 0(n33) : U32
        \\  n35 = Num.U32.is_eq(n28, n34) : Bool
        \\  n37 = switch n35 : F32
        \\    arm 0
        \\      n36 = field 0(p0) : F32
        \\      value n36
        \\    arm 1
        \\      value n1
        \\  value n37
        \\row r1 (Builtin.Num.Numeral) -> Builtin.Try
        \\  n0 = Num.U32.from_numeral(p0) : Builtin.Try !spec
        \\  n1 = unwrap(n0) : [Err([InvalidNumeral(Str)]), Ok(U32)]
        \\  n10 = switch n1 : Builtin.Try !spec
        \\    arm 0
        \\      n2 = payload Err.0(n1) : [InvalidNumeral(Str)] !spec
        \\      n3 = tag Err(n2) : [Err([InvalidNumeral(Str)]), Ok(Count)]
        \\      n4 = wrap(n3) : Builtin.Try
        \\      value n4
        \\    arm 1
        \\      n5 = payload Ok.0(n1) : U32 !spec
        \\      n6 = record(n5) : { n : U32 }
        \\      n7 = wrap(n6) : Count
        \\      n8 = tag Ok(n7) : [Err([InvalidNumeral(Str)]), Ok(Count)]
        \\      n9 = wrap(n8) : Builtin.Try
        \\      value n9
        \\  value n10
        \\
    );
}

test "a string of more than one segment describes as the concatenation it is" {
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| if "p${input.uv.to_str()}q".is_empty() input.uv else input.time
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = "p" : Str
        \\  n1 = field 1(p0) : F32
        \\  n2 = Num.F32.to_str(n1) : Str !spec
        \\  n3 = "q" : Str
        \\  n4 = Str.concat(n0, n2, n3) : Str
        \\  n5 = Str.is_empty(n4) : Bool !spec
        \\  n7 = switch n5 : F32
        \\    arm 0
        \\      n6 = field 0(p0) : F32
        \\      value n6
        \\    arm 1
        \\      value n1
        \\  value n7
        \\
    );
}

test "an empty segment of an interpolated string joins nothing" {
    // `"${v}"` carries a segment on each side that the author wrote no text
    // in, so the literal describes as the value alone.
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| if "${input.uv.to_str()}".is_empty() input.uv else input.time
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 1(p0) : F32
        \\  n1 = Num.F32.to_str(n0) : Str !spec
        \\  n2 = Str.is_empty(n1) : Bool !spec
        \\  n4 = switch n2 : F32
        \\    arm 0
        \\      n3 = field 0(p0) : F32
        \\      value n3
        \\    arm 1
        \\      value n0
        \\  value n4
        \\
    );
}

test "a record update reads a subject that is already a name" {
    // `input` describes as a `Param`, which a translator repeats as it
    // stands, so the walk reads it once per field rather than binding it.
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| { ..input, uv: 1.0.F32 }.time
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  value n0
        \\
    );
}

test "a record type says which of its fields may be absent" {
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv ?: F32 } -> F32
        \\wobble = |input| input.time
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv ? F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  value n0
        \\
    );
}

test "a list pattern's rest splits the patterns written around it" {
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : List(F32) -> F32
        \\wobble = |input| match input {
        \\    [a, .. as mid, b] => a + b + mid.len().to_f32()
        \\    _ => 0.0
        \\}
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 (List(F32)) -> F32
        \\  n0 = List.len(p0) : U64
        \\  n1 = 2 : U64
        \\  n2 = Num.U64.is_lt(n0, n1) : Bool
        \\  n15 = switch n2 : F32 !spec
        \\    arm 0
        \\      n3 = 0 : U64
        \\      n4 = elem(p0, n3) : F32 !spec
        \\      n5 = 1 : U64
        \\      n6 = Num.U64.minus(n0, n5) : U64
        \\      n7 = elem(p0, n6) : F32 !spec
        \\      n8 = Num.F32.plus(n4, n7) : F32
        \\      n9 = List.drop_first(p0, n5) : List(F32) !spec
        \\      n10 = List.drop_last(n9, n5) : List(F32) !spec
        \\      n11 = List.len(n10) : U64
        \\      n12 = Num.U64.to_f32(n11) : F32 !spec
        \\      n13 = Num.F32.plus(n8, n12) : F32
        \\      value n13
        \\    arm 1
        \\      n14 = float 0x0 : F32
        \\      value n14
        \\  value n15
        \\
    );
}

test "a string pattern's capture keeps the name the author wrote in it" {
    // The pattern is the prefix test, one split at the first `z`, and an
    // exact end that leaves no text; the capture is what comes before the
    // split.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : Str -> Str
        \\wobble = |input| match input {
        \\    "a${head}z" => head
        \\    _ => input
        \\}
    , "");
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 (Str) -> Str
        \\  n0 = "a" : Str
        \\  n1 = Str.starts_with(p0, n0) : Bool !spec
        \\  n12 = switch n1 : Str !spec
        \\    arm 0
        \\      value p0
        \\    arm 1
        \\      n2 = Str.drop_prefix(p0, n0) : Str !spec
        \\      n3 = "z" : Str
        \\      n4 = Str.split_first(n2, n3) : Builtin.Try !spec
        \\      n5 = unwrap(n4) : [Err([NotFound]), Ok({ after : Str, before : Str })]
        \\      n11 = switch n5 : Str !spec
        \\        arm 0
        \\          value p0
        \\        arm 1
        \\          n6 = payload Ok.0(n5) : { after : Str, before : Str } !spec
        \\          n7 = field 0(n6) : Str
        \\          n8 = Str.is_empty(n7) : Bool !spec
        \\          n10 = switch n8 : Str
        \\            arm 0
        \\              value p0
        \\            arm 1
        \\              n9 = field 1(n6) : Str
        \\              value n9
        \\          value n10
        \\      value n11
        \\  value n12
        \\
    );
}

// L3: source pairs. Each pair is two spellings of one function under a
// refactor in R (`roc-reify-normalization-plan.md` 5.10, M1), and the two
// sides must describe as one normal form.

/// Both sources describe `wobble` to the same dump, and to the same dump in
/// the `outline` view (M9: every L3 row holds in `outline`, which is a
/// function of `inline` and so of the normal form).
fn expectSameNormalForm(left: []const u8, right: []const u8) (StagedError || error{ TestUnexpectedResult, TestExpectedEqual })!void {
    const gpa = std.testing.allocator;
    const a = try Staged.createRunning(gpa, left, "");
    defer a.destroy();
    const b = try Staged.createRunning(gpa, right, "");
    defer b.destroy();
    inline for (.{ a, b }) |side| switch (side.outcome) {
        .reified => {},
        .rejected => |rejection| {
            std.debug.print("reification rejected: {t} {s} at '{s}'\n", .{ rejection.kind, rejection.detail, side.env.getSource(rejection.region) });
            return error.TestUnexpectedResult;
        },
    };
    try std.testing.expectEqualStrings(a.dump.items, b.dump.items);
    try expectSameView(a, b, .outline);
}

/// The two fixtures' sites describe to one dump in `view`.
fn expectSameView(a: *Staged, b: *Staged, view: @TypeOf(@as(CodeReifier.Walk, undefined).view)) (StagedError || error{ TestUnexpectedResult, TestExpectedEqual })!void {
    const gpa = std.testing.allocator;
    const da = try a.viewDump(view) orelse return error.TestUnexpectedResult;
    defer gpa.free(da);
    const db = try b.viewDump(view) orelse return error.TestUnexpectedResult;
    defer gpa.free(db);
    try std.testing.expectEqualStrings(da, db);
}

test "L3: a literal's spelling does not reach the normal form" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| input + 0x10 + 1_000
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| input + 16 + 1000
    );
}

test "L3: `??` describes as the match it means" {
    try expectSameNormalForm(
        \\wobble : Try(U64, [Bad]) -> U64
        \\wobble = |input| input ?? 7
    ,
        \\wobble : Try(U64, [Bad]) -> U64
        \\wobble = |input| match input {
        \\    Ok(v) => v
        \\    Err(_) => 7
        \\}
    );
}

test "L3: a `var` threaded through statements is the value it ends at" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $x = input
        \\    $x = $x + 1
        \\    $x = $x * 2
        \\    $x
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| (input + 1) * 2
    );
}

test "L3: a binding inside a loop body is the value it names" {
    try expectSameNormalForm(
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for x in input {
        \\        d = x * 2
        \\        $total = $total + d
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $sum = 0
        \\    for item in input {
        \\        $sum = $sum + item * 2
        \\    }
        \\    $sum
        \\}
    );
}

test "L3: `a and b` is `if a b else Bool.False`" {
    try expectSameNormalForm(
        \\wobble : { a : Bool, b : Bool } -> Bool
        \\wobble = |input| input.a and input.b
    ,
        \\wobble : { a : Bool, b : Bool } -> Bool
        \\wobble = |input| if input.a input.b else Bool.False
    );
}

test "L3: `a or b` is `if a Bool.True else b`" {
    try expectSameNormalForm(
        \\wobble : { a : Bool, b : Bool } -> Bool
        \\wobble = |input| input.a or input.b
    ,
        \\wobble : { a : Bool, b : Bool } -> Bool
        \\wobble = |input| if input.a Bool.True else input.b
    );
}

test "L3: `return x` last is `x`" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    y = input + 1
        \\    return y
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| input + 1
    );
}

test "L3: an early `return` in a branch is the value of that branch" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    if input > 10 {
        \\        return 0
        \\    }
        \\    input + 1
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| if input > 10 0 else input + 1
    );
}

test "L3: `if c { break }; rest` is `rest` in the `else`" {
    try expectSameNormalForm(
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for x in input {
        \\        if x > 5 {
        \\            break
        \\        }
        \\        $total = $total + x
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for x in input {
        \\        if x > 5 {
        \\            break
        \\        } else {
        \\            $total = $total + x
        \\        }
        \\    }
        \\    $total
        \\}
    );
}

test "L3: `?` is the match it means" {
    try expectSameNormalForm(
        \\wobble : Try(U64, [Bad]) -> Try(U64, [Bad])
        \\wobble = |input| Ok(input? + 1)
    ,
        \\wobble : Try(U64, [Bad]) -> Try(U64, [Bad])
        \\wobble = |input| match input {
        \\    Ok(v) => Ok(v + 1)
        \\    Err(e) => return Err(e)
        \\}
    );
}

test "L3: `a != b` is `!(a == b)`" {
    try expectSameNormalForm(
        \\wobble : { a : U64, b : U64 } -> Bool
        \\wobble = |input| input.a != input.b
    ,
        \\wobble : { a : U64, b : U64 } -> Bool
        \\wobble = |input| !(input.a == input.b)
    );
}

// L4 and L5 over a fixed seed set: the R fuzzer and the soundness
// differential of `roc-reify-normalization-plan.md` 5.1, run by the driver
// the AFL target runs, on the cases `reify.fuzz_gen` generates from each seed.

// `m7` stays off here: with it on, seed 0x5eed case 119 fails with two normal
// forms because a literal `0` is placed once above a switch in one print and
// once inside an arm in the other (an N5 gap, not the cone of T1.11).
test "L4 and L5: every seed's two prints are one normal form, which computes what Roc computes" {
    var prng = std.Random.DefaultPrng.init(0x5eed);
    const random = prng.random();
    var bytes: [96]u8 = undefined;
    var verdicts = std.EnumArray(reify_fuzz.Verdict, u32).initFill(0);
    for (0..512) |_| {
        random.bytes(&bytes);
        var tmp = std.testing.tmpDir(.{});
        defer tmp.cleanup();
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const ctx = CoreCtx.default(std.testing.allocator, arena.allocator(), std.testing.io);
        verdicts.getPtr(try reify_fuzz.runCaseWith(ctx, try sharedBuiltinModules(), tmp.dir, &bytes, .{ .m7 = false })).* += 1;
    }
    // The seeds reach both rows of the C2 table.
    try std.testing.expect(verdicts.get(.agree) > 0 and verdicts.get(.reference_crashed) > 0);
}

/// A package whose type is a translator, `Lib.arity`, with `scale` in its
/// cut. `body` is the definition of `scale`.
fn translatorLib(comptime body: []const u8, comptime cut: []const u8) []const u8 {
    return
    \\Lib := {}.{
    \\    scale : U64, U64 -> U64
    \\
    ++ "    scale = " ++ body ++ "\n\n" ++
        "    code_primitives = " ++ cut ++ "\n\n" ++
        \\    arity : Code(f) -> U64
        \\    arity = |code| code.graph().root_row().params.len()
        \\}
    ;
}

const translated_caller =
    \\wobble : { a : U64, b : U64 } -> U64
    \\wobble = |input| Lib.scale(input.a, input.b) + 1
;

test "L7: a refactor inside a function in the translator's cut leaves the caller's normal form unchanged" {
    // N8h: a function in the cut is a named `Prim`, so its body is not the
    // description's, and a refactor inside it changes nothing here.
    const gpa = std.testing.allocator;
    const written = try Staged.createTranslated(gpa, translated_caller, "_n = Lib.arity(wobble)", translatorLib("|v, k| v * k", "(scale)"));
    defer written.destroy();
    const refactored = try Staged.createTranslated(gpa, translated_caller, "_n = Lib.arity(wobble)", translatorLib(
        \\|v, k| {
        \\        product = k * v
        \\        product
        \\    }
    , "(scale)"));
    defer refactored.destroy();
    try written.expectDump(
        \\row r0 ({ a : U64, b : U64 }) -> U64
        \\  n0 = field 0(p0) : U64
        \\  n1 = field 1(p0) : U64
        \\  n2 = Lib.scale(n0, n1) : U64 !spec
        \\  n3 = 1 : U64
        \\  n4 = Num.U64.plus(n2, n3) : U64 !spec
        \\  value n4
        \\
    );
    try std.testing.expectEqualStrings(written.dump.items, refactored.dump.items);
}

test "N8l M13: a function of another package outside the cut is walked by its body" {
    // The type declares a cut without `scale`, so the call is the body.
    const gpa = std.testing.allocator;
    const walked = try Staged.createTranslated(gpa, translated_caller, "_n = Lib.arity(wobble)", translatorLib("|v, k| v * k", "(arity)"));
    defer walked.destroy();
    try walked.expectDump(
        \\row r0 ({ a : U64, b : U64 }) -> U64
        \\  n0 = field 0(p0) : U64
        \\  n1 = field 1(p0) : U64
        \\  n2 = Num.U64.times(n0, n1) : U64 !spec
        \\  n3 = 1 : U64
        \\  n4 = Num.U64.plus(n2, n3) : U64 !spec
        \\  value n4
        \\
    );
    // A site no translator call holds has an empty cut, and reads the same body.
    const bare = try Staged.createSite(gpa, translated_caller, "", "input", translatorLib("|v, k| v * k", "(scale)"));
    defer bare.destroy();
    try std.testing.expectEqualStrings(walked.dump.items, bare.dump.items);
}

test "N8h M13: a method in the cut called as a method is the Prim its direct call is" {
    // The name is the qualified name of the definition, `Lib.Vec` and
    // `scale`, however the call is written.
    const gpa = std.testing.allocator;
    const lib =
        \\Lib := {}.{
        \\    Vec := { x : U64 }.{
        \\        scale : Vec, U64 -> U64
        \\        scale = |v, k| v.x * k
        \\    }
        \\
        \\    code_primitives = (Vec.scale)
        \\
        \\    arity : Code(f) -> U64
        \\    arity = |code| code.graph().root_row().params.len()
        \\}
    ;
    const direct = try Staged.createTranslated(gpa,
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| Lib.Vec.scale(Lib.Vec.({ x: input.a }), input.b)
    , "_n = Lib.arity(wobble)", lib);
    defer direct.destroy();
    const method = try Staged.createTranslated(gpa,
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| Lib.Vec.({ x: input.a }).scale(input.b)
    , "_n = Lib.arity(wobble)", lib);
    defer method.destroy();
    if (direct.outcome != .reified) return error.TestUnexpectedResult;
    try std.testing.expect(std.mem.find(u8, direct.dump.items, "Lib.Vec.scale(") != null);
    try std.testing.expectEqualStrings(direct.dump.items, method.dump.items);
}

test "I14 M13: a translator called as a method, through a pipe or through an alias takes the cut its direct call takes" {
    // The translator is the function the call names: the callee of a direct
    // call, the method a method call dispatches to. Its type's cut keeps
    // `scale` a `Prim` however the call is written.
    const gpa = std.testing.allocator;
    const lib =
        \\Lib := {}.{
        \\    scale : U64, U64 -> U64
        \\    scale = |v, k| v * k
        \\
        \\    code_primitives = (scale)
        \\
        \\    arity : Lib, Code(f) -> U64
        \\    arity = |_, code| code.graph().root_row().params.len()
        \\}
    ;
    const direct = try Staged.createTranslated(gpa, translated_caller, "_n = Lib.arity(Lib.({}), wobble)", lib);
    defer direct.destroy();
    try direct.expectDump(
        \\row r0 ({ a : U64, b : U64 }) -> U64
        \\  n0 = field 0(p0) : U64
        \\  n1 = field 1(p0) : U64
        \\  n2 = Lib.scale(n0, n1) : U64 !spec
        \\  n3 = 1 : U64
        \\  n4 = Num.U64.plus(n2, n3) : U64 !spec
        \\  value n4
        \\
    );
    const forms = [_][]const u8{
        "_n = Lib.({}).arity(wobble)",
        "_n = Lib.({}) |> Lib.arity(wobble)",
        // A local alias of the translator forwards to it.
        "s = Lib.arity\n    _n = s(Lib.({}), wobble)",
        // A site in a branch of the argument is an argument of the call.
        "_n = Lib.arity(Lib.({}), if Bool.True wobble else wobble)",
    };
    for (forms) |form| {
        const called = try Staged.createTranslated(gpa, translated_caller, form, lib);
        defer called.destroy();
        try std.testing.expectEqualStrings(direct.dump.items, called.dump.items);
    }
}

test "N8h M13: a function in the cut of a translator in the site's own module is a Prim" {
    // The cut is the translator's, in any package, the site's own included.
    const staged = try Staged.createTranslated(std.testing.allocator,
        \\Tr := {}.{
        \\    twice : U64 -> U64
        \\    twice = |x| x * 2
        \\
        \\    code_primitives = (Tr.twice)
        \\
        \\    arity : Code(f) -> U64
        \\    arity = |code| code.graph().root_row().params.len()
        \\}
        \\
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| Tr.twice(input.a)
    , "_n = Tr.arity(wobble)", null);
    defer staged.destroy();
    if (staged.outcome != .reified) return error.TestUnexpectedResult;
    try std.testing.expect(std.mem.find(u8, staged.dump.items, ".Tr.twice(n0)") != null or std.mem.find(u8, staged.dump.items, " Tr.twice(n0)") != null);
}

test "L3 M13: a refactor inside a dependency's function outside the cut meets the same refactor inside the package" {
    // N8l: the dependency's body is walked as the site's own helper is, so
    // a refactor in R inside it is absorbed, wherever the helper lives.
    const gpa = std.testing.allocator;
    const caller_away =
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| Lib.scale(input.a, input.b) + 1
    ;
    const plain = "|v, k| v * k";
    const bound =
        \\|v, k| {
        \\        product = v * k
        \\        product
        \\    }
    ;
    const away = try Staged.createSite(gpa, caller_away, "", "input", translatorLib(plain, "(arity)"));
    defer away.destroy();
    const away_refactored = try Staged.createSite(gpa, caller_away, "", "input", translatorLib(bound, "(arity)"));
    defer away_refactored.destroy();
    const here = try Staged.createRunning(gpa,
        \\scale : U64, U64 -> U64
        \\scale = |v, k| v * k
        \\
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| scale(input.a, input.b) + 1
    , "");
    defer here.destroy();
    const here_refactored = try Staged.createRunning(gpa,
        \\scale : U64, U64 -> U64
        \\scale = |v, k| {
        \\    product = v * k
        \\    product
        \\}
        \\
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| scale(input.a, input.b) + 1
    , "");
    defer here_refactored.destroy();
    if (away.outcome != .reified) return error.TestUnexpectedResult;
    try std.testing.expectEqualStrings(away.dump.items, away_refactored.dump.items);
    try std.testing.expectEqualStrings(away.dump.items, here.dump.items);
    try std.testing.expectEqualStrings(away.dump.items, here_refactored.dump.items);
}

test "M13: a dependency upgrade that changes the operations of a function outside the cut changes the normal form" {
    // Plan 5.12: apart. The upgrade is a new body, and the body is read.
    const gpa = std.testing.allocator;
    const caller =
        \\wobble : { a : F32, b : F32 } -> F32
        \\wobble = |input| Lib.norm(input.a) + 1.0.F32
    ;
    const before = try Staged.createSite(gpa, caller, "", "input",
        \\Lib := {}.{
        \\    norm : F32 -> F32
        \\    norm = |x| x * x
        \\}
    );
    defer before.destroy();
    const after = try Staged.createSite(gpa, caller, "", "input",
        \\Lib := {}.{
        \\    norm : F32 -> F32
        \\    norm = |x| x.sqrt()
        \\}
    );
    defer after.destroy();
    if (before.outcome != .reified or after.outcome != .reified) return error.TestUnexpectedResult;
    try std.testing.expect(std.mem.find(u8, after.dump.items, "Num.F32.sqrt") != null);
    try std.testing.expect(!std.mem.eql(u8, before.dump.items, after.dump.items));
}

/// The two sources describe `wobble` to different dumps.
fn expectOtherNormalForm(left: []const u8, right: []const u8) (StagedError || error{TestUnexpectedResult})!void {
    const gpa = std.testing.allocator;
    const a = try Staged.createRunning(gpa, left, "");
    defer a.destroy();
    const b = try Staged.createRunning(gpa, right, "");
    defer b.destroy();
    if (a.outcome != .reified or b.outcome != .reified) return error.TestUnexpectedResult;
    if (std.mem.eql(u8, a.dump.items, b.dump.items)) return error.TestUnexpectedResult;
}

// M4: flat matches, `if`, and `?` are one decision tree (N7a).

test "L3 M4: `if` is the `match` on a Bool" {
    try expectSameNormalForm(
        \\wobble : { c : Bool, x : U64, y : U64 } -> U64
        \\wobble = |input| if input.c input.x else input.y
    ,
        \\wobble : { c : Bool, x : U64, y : U64 } -> U64
        \\wobble = |input| match input.c {
        \\    Bool.True => input.x
        \\    Bool.False => input.y
        \\}
    );
}

test "L3 M4: the arms of a flat tag match in any order are one normal form" {
    try expectSameNormalForm(
        \\wobble : { t : [A, B, C], n : U64 } -> U64
        \\wobble = |input| match input.t {
        \\    A => input.n + 1
        \\    B => input.n + 2
        \\    C => input.n + 3
        \\}
    ,
        \\wobble : { t : [A, B, C], n : U64 } -> U64
        \\wobble = |input| match input.t {
        \\    C => input.n + 3
        \\    A => input.n + 1
        \\    B => input.n + 2
        \\}
    );
}

test "L3 M4: the arms of a flat tag match with payloads in any order are one normal form" {
    try expectSameNormalForm(
        \\wobble : Try(U64, U64) -> U64
        \\wobble = |input| match input {
        \\    Ok(a) => a + 1
        \\    Err(e) => e * 2
        \\}
    ,
        \\wobble : Try(U64, U64) -> U64
        \\wobble = |input| match input {
        \\    Err(e) => e * 2
        \\    Ok(a) => a + 1
        \\}
    );
}

test "L3 M4: a wildcard arm is the tags it covers" {
    try expectSameNormalForm(
        \\wobble : { t : [A, B, C], n : U64 } -> U64
        \\wobble = |input| match input.t {
        \\    A => input.n + 1
        \\    _ => 0
        \\}
    ,
        \\wobble : { t : [A, B, C], n : U64 } -> U64
        \\wobble = |input| match input.t {
        \\    A => input.n + 1
        \\    B => 0
        \\    C => 0
        \\}
    );
}

test "L3 M4: the arms of a flat literal match in any order are one normal form" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| match input {
        \\    1 => 10
        \\    2 => 20
        \\    3 => 30
        \\    _ => 0
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| match input {
        \\    3 => 30
        \\    1 => 10
        \\    2 => 20
        \\    _ => 0
        \\}
    );
}

test "L3 M4: a string literal match in any order is one normal form" {
    try expectSameNormalForm(
        \\wobble : Str -> U64
        \\wobble = |input| match input {
        \\    "a" => 1
        \\    "b" => 2
        \\    _ => 0
        \\}
    ,
        \\wobble : Str -> U64
        \\wobble = |input| match input {
        \\    "b" => 2
        \\    "a" => 1
        \\    _ => 0
        \\}
    );
}

test "L3 M4: `a >= b` over integers is `!(a < b)`" {
    try expectSameNormalForm(
        \\wobble : { a : U64, b : U64 } -> Bool
        \\wobble = |input| input.a >= input.b
    ,
        \\wobble : { a : U64, b : U64 } -> Bool
        \\wobble = |input| !(input.a < input.b)
    );
}

test "L3 M4: `if a >= b x else y` is `if a < b y else x` over integers" {
    try expectSameNormalForm(
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| if input.a >= input.b 1 else 2
    ,
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| if input.a < input.b 2 else 1
    );
}

test "L3 M4: `a >= b` over floats is not `!(a < b)`" {
    try expectOtherNormalForm(
        \\wobble : { a : F64, b : F64 } -> Bool
        \\wobble = |input| input.a >= input.b
    ,
        \\wobble : { a : F64, b : F64 } -> Bool
        \\wobble = |input| !(input.a < input.b)
    );
}

test "L3 M4: `if !c x else y` is `if c y else x`" {
    try expectSameNormalForm(
        \\wobble : { c : Bool, x : U64, y : U64 } -> U64
        \\wobble = |input| if !input.c input.x else input.y
    ,
        \\wobble : { c : Bool, x : U64, y : U64 } -> U64
        \\wobble = |input| if input.c input.y else input.x
    );
}

test "L3 M4: `if a Bool.False else b` is `!a and b`" {
    try expectSameNormalForm(
        \\wobble : { a : Bool, b : Bool } -> Bool
        \\wobble = |input| if input.a Bool.False else input.b
    ,
        \\wobble : { a : Bool, b : Bool } -> Bool
        \\wobble = |input| !input.a and input.b
    );
}

test "L3 M4: a test a dominating branch made is not made again" {
    try expectSameNormalForm(
        \\wobble : { c : Bool, x : U64, y : U64 } -> U64
        \\wobble = |input| if input.c (if input.c input.x else input.y) else input.y
    ,
        \\wobble : { c : Bool, x : U64, y : U64 } -> U64
        \\wobble = |input| if input.c input.x else input.y
    );
}

test "L3 M4: a match on a tag the code just built is the arm" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| match Ok(input) {
        \\    Ok(a) => a + 1
        \\    Err(_) => 0
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| input + 1
    );
}

test "L3 M4: the arms of a flat match that exit are one normal form in any order" {
    try expectSameNormalForm(
        \\wobble : { t : [A, B, C], n : U64 } -> U64
        \\wobble = |input| {
        \\    v = match input.t {
        \\        A => return 7
        \\        B => input.n + 2
        \\        C => input.n + 3
        \\    }
        \\    v * 2
        \\}
    ,
        \\wobble : { t : [A, B, C], n : U64 } -> U64
        \\wobble = |input| {
        \\    v = match input.t {
        \\        C => input.n + 3
        \\        B => input.n + 2
        \\        A => return 7
        \\    }
        \\    v * 2
        \\}
    );
}

test "L3 M4: a Bool match with a wildcard is the match of both arms" {
    try expectSameNormalForm(
        \\wobble : { c : Bool, x : U64, y : U64 } -> U64
        \\wobble = |input| match input.c {
        \\    Bool.True => input.x
        \\    _ => input.y
        \\}
    ,
        \\wobble : { c : Bool, x : U64, y : U64 } -> U64
        \\wobble = |input| match input.c {
        \\    Bool.False => input.y
        \\    Bool.True => input.x
        \\}
    );
}

test "L3 M4: an alternative pattern is the arms it lists" {
    try expectSameNormalForm(
        \\wobble : { t : [A, B, C], n : U64 } -> U64
        \\wobble = |input| match input.t {
        \\    A | B => input.n
        \\    C => 0
        \\}
    ,
        \\wobble : { t : [A, B, C], n : U64 } -> U64
        \\wobble = |input| match input.t {
        \\    C => 0
        \\    B => input.n
        \\    A => input.n
        \\}
    );
}

test "L3 M4: signed literal arms in any order are one normal form" {
    try expectSameNormalForm(
        \\wobble : I64 -> I64
        \\wobble = |input| match input {
        \\    -5 => 1
        \\    3 => 2
        \\    _ => 0
        \\}
    ,
        \\wobble : I64 -> I64
        \\wobble = |input| match input {
        \\    3 => 2
        \\    -5 => 1
        \\    _ => 0
        \\}
    );
}

test "L3 M4: `?` is the match on Try in either arm order" {
    try expectSameNormalForm(
        \\wobble : Try(U64, [Bad]) -> Try(U64, [Bad])
        \\wobble = |input| {
        \\    v = input?
        \\    Ok(v + 1)
        \\}
    ,
        \\wobble : Try(U64, [Bad]) -> Try(U64, [Bad])
        \\wobble = |input| match input {
        \\    Err(e) => Err(e)
        \\    Ok(v) => Ok(v + 1)
        \\}
    );
}

test "L3 M4: the arms of a flat match in a loop body in any order are one normal form" {
    try expectSameNormalForm(
        \\wobble : { t : List([A, B, C]), n : U64 } -> U64
        \\wobble = |input| {
        \\    var $s = 0
        \\    for x in input.t {
        \\        match x {
        \\            A => { $s = $s + 1 }
        \\            B => {}
        \\            C => { $s = $s + 3 }
        \\        }
        \\    }
        \\    $s
        \\}
    ,
        \\wobble : { t : List([A, B, C]), n : U64 } -> U64
        \\wobble = |input| {
        \\    var $s = 0
        \\    for x in input.t {
        \\        match x {
        \\            C => { $s = $s + 3 }
        \\            B => {}
        \\            A => { $s = $s + 1 }
        \\        }
        \\    }
        \\    $s
        \\}
    );
}

// M2: order and placement are canonical under C2 (plan 4, M2).

test "L3 M2: independent bindings in either order are one normal form" {
    try expectSameNormalForm(
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |input| {
        \\    a = input.x + 1
        \\    b = input.y * 2
        \\    a - b
        \\}
    ,
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |input| {
        \\    q = input.y * 2
        \\    p = input.x + 1
        \\    p - q
        \\}
    );
}

test "L3 M2: a field read in an inner and an outer branch is one node, however the inner branch is spelled" {
    // The reads of `a` in the inner arms merge into the inner `if`, which
    // merges again with the read in the outer arm.
    try expectSameNormalForm(
        \\wobble : { a : U64, b : U64, flag : Bool } -> U64
        \\wobble = |input|
        \\    if input.b == 5 {
        \\        input.a
        \\    } else if input.flag {
        \\        1 - input.a
        \\    } else {
        \\        input.a - input.b
        \\    }
    ,
        \\wobble : { a : U64, b : U64, flag : Bool } -> U64
        \\wobble = |input|
        \\    if input.b == 5 {
        \\        input.a
        \\    } else if !input.flag {
        \\        input.a - input.b
        \\    } else {
        \\        1 - input.a
        \\    }
    );
}

test "L3 M2: a value bound twice is the value bound once" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    a = input + 1
        \\    b = input + 1
        \\    a * b
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    a = input + 1
        \\    a * a
        \\}
    );
}

test "L3 M2: an if bound twice is the if bound once" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    a = if input > 10 input - 10 else input
        \\    b = if input > 10 input - 10 else input
        \\    a * b
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    a = if input > 10 input - 10 else input
        \\    a * a
        \\}
    );
}

test "L3 M2: a binding before a match is the binding in every arm" {
    try expectSameNormalForm(
        \\wobble : { tag : [A, B], n : U64 } -> U64
        \\wobble = |input| {
        \\    y = input.n + 1
        \\    match input.tag {
        \\        A => y * 2
        \\        B => y * 3
        \\    }
        \\}
    ,
        \\wobble : { tag : [A, B], n : U64 } -> U64
        \\wobble = |input| match input.tag {
        \\    A => (input.n + 1) * 2
        \\    B => (input.n + 1) * 3
        \\}
    );
}

test "L3 M2: a failing binding read in one branch is that branch's work" {
    try expectSameNormalForm(
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| {
        \\    q = input.a // input.b
        \\    if input.a > 10 q else 0
        \\}
    ,
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| if input.a > 10 input.a // input.b else 0
    );
}

test "L3 M2: a dead failing binding is dropped" {
    try expectSameNormalForm(
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| {
        \\    _q = input.a // input.b
        \\    input.a + 1
        \\}
    ,
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| input.a + 1
    );
}

test "L3 M2: a dominating test decides a binding written before the branch" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    y = if input > 10 1 else 2
        \\    if input > 10 y else 0
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| if input > 10 1 else 0
    );
}

test "L3 M2: failing integer work moved across a loop boundary is not in R" {
    try expectOtherNormalForm(
        \\wobble : { n : U64, items : List(U64) } -> U64
        \\wobble = |input| {
        \\    d = input.n * 2
        \\    var $total = 0
        \\    for x in input.items {
        \\        $total = $total + x + d
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : { n : U64, items : List(U64) } -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for x in input.items {
        \\        $total = $total + x + input.n * 2
        \\    }
        \\    $total
        \\}
    );
}

test "L3 M2: a test that no loop turn changes is one normal form wherever it is written" {
    try expectSameNormalForm(
        \\wobble : { n : U64, items : List(U64) } -> U64
        \\wobble = |input| {
        \\    big = input.n > 5
        \\    var $total = 0
        \\    for x in input.items {
        \\        if big {
        \\            $total = $total + x
        \\        }
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : { n : U64, items : List(U64) } -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for x in input.items {
        \\        if input.n > 5 {
        \\            $total = $total + x
        \\        }
        \\    }
        \\    $total
        \\}
    );
}

// L3 pairs of M3 (`roc-reify-normalization-plan.md` 4.1): rows are digests,
// finalized before their callers, and a function an `if` chooses or a
// record literal holds is called directly.

test "L3: a function an `if` chooses is called in each branch" {
    try expectSameNormalForm(
        \\half : U64 -> U64
        \\half = |x| x // 2
        \\
        \\twice : U64 -> U64
        \\twice = |x| x * 2
        \\
        \\wobble : { c : Bool, x : U64 } -> U64
        \\wobble = |input| (if input.c half else twice)(input.x)
    ,
        \\half : U64 -> U64
        \\half = |x| x // 2
        \\
        \\twice : U64 -> U64
        \\twice = |x| x * 2
        \\
        \\wobble : { c : Bool, x : U64 } -> U64
        \\wobble = |input| if input.c half(input.x) else twice(input.x)
    );
}

test "L3: a function read from a record literal is called directly" {
    try expectSameNormalForm(
        \\twice : U64 -> U64
        \\twice = |x| x * 2
        \\
        \\wobble : U64 -> U64
        \\wobble = |input| ({ op: twice }.op)(input)
    ,
        \\twice : U64 -> U64
        \\twice = |x| x * 2
        \\
        \\wobble : U64 -> U64
        \\wobble = |input| twice(input)
    );
}

test "L3: a lambda that captures, passed to a helper that calls it, meets the helper's body over it" {
    try expectSameNormalForm(
        \\apply : (U64 -> U64), U64 -> U64
        \\apply = |f, x| f(x)
        \\
        \\wobble : { k : U64, x : U64 } -> U64
        \\wobble = |input| {
        \\    k = input.k
        \\    apply(|y| y + k, input.x)
        \\}
    ,
        \\add : U64, U64 -> U64
        \\add = |k, y| y + k
        \\
        \\wobble : { k : U64, x : U64 } -> U64
        \\wobble = |input| add(input.k, input.x)
    );
}

test "a call of a function parameter no call fixes refuses the site" {
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : { f : U64 -> U64, x : U64 } -> U64
        \\wobble = |input| (input.f)(input.x)
    , "");
    defer staged.destroy();

    try staged.expectRejected("a call to a function value that no simplification resolves");
}

test "P1: a template is normalized once per argument digest, however many calls it has" {
    const gpa = std.testing.allocator;
    const self = try Staged.createChecked(gpa,
        \\wobble : F32 -> Code({ time : F32, uv : F32 } -> F32)
        \\wobble = |factor| |input| input.uv * factor
    , "_a = wobble(3.5.F32)\n_b = wobble(1.5.F32)");
    self.store = ConstStore.init(gpa);
    const artifact = self.coord.appRootCheckedArtifact();
    self.foreign = .{ .artifact = artifact, .builtins = &(try sharedBuiltinModules()).checked_artifact };
    self.walk = CodeReifier.Walk.init(gpa, &self.store, self.foreign.lookup());
    defer self.destroy();
    self.reifier = try self.walk.reader(.{
        .sources = CodeReifier.Reifier.artifactSources(artifact),
        .env = self.env,
    });
    const template = templateLambda(artifact, self.env, 1) orelse return error.StagedLambdaNotFound;

    // Five calls over two argument lists.
    var graphs: [5]ConstNodeId = undefined;
    for ([_][]const u8{ "3.5.F32", "1.5.F32", "3.5.F32", "3.5.F32", "1.5.F32" }, &graphs) |text, *graph| {
        const arg = checkedExprWithSource(artifact, self.env, text) orelse return error.StagedLambdaNotFound;
        var values = std.ArrayList(CodeReifier.Reifier.TemplateArg).empty;
        defer values.deinit(gpa);
        defer self.reifier.releaseTemplateArgs(values.items);
        if (try self.reifier.reifyConstants(&.{arg}, &values, gpa)) |_| return error.TestUnexpectedResult;
        const outcome = try self.reifier.reifyTemplateCall(template, values.items, .zero());
        if (outcome != .reified) return error.TestUnexpectedResult;
        graph.* = self.store.get(outcome.reified).record[0];
    }
    try std.testing.expectEqual(@as(u32, 2), self.walk.normalizations);
    try std.testing.expectEqual(graphs[0], graphs[2]);
    try std.testing.expectEqual(graphs[1], graphs[4]);
    try std.testing.expect(graphs[0] != graphs[1]);
}

/// A function whose block binds a lambda that reads the function's own
/// parameter, which exists only when the program runs.
const reads_outer =
    \\wobble : { k : U64, x : U64 } -> U64
    \\wobble = |outer| {
    \\    add_k = |input| outer.k + input
    \\    add_k(outer.x)
    \\}
;

test "N18a: a value the root reads from around itself is an input slot where the translator binds inputs" {
    const staged = try Staged.createInBlock(std.testing.allocator, reads_outer, true);
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 (U64) -> U64
        \\  n0 = Num.U64.plus(in1, p0) : U64 !spec
        \\  value n0
        \\
    );
    // The dump names slots by their place in the site's store, where the
    // whole `outer` the field read starts from is slot 0. The root reads one
    // slot: the field `k` of `outer`.
    const slots = staged.walk.slots;
    try std.testing.expectEqual(@as(usize, 1), slots.len);
    try std.testing.expectEqual(@as(usize, 1), slots[0].steps.len);
    try std.testing.expect(slots[0].steps[0] == .field);
}

test "a value the root reads from around itself is refused where the translator binds no inputs" {
    const staged = try Staged.createInBlock(std.testing.allocator, reads_outer, false);
    defer staged.destroy();

    try staged.expectRejected("outer");
}

test "a var the root reads from around itself is refused as an input slot" {
    const staged = try Staged.createInBlock(std.testing.allocator,
        \\wobble : U64 -> U64
        \\wobble = |n| {
        \\    var $total = n
        \\    $total = $total + 1
        \\    add = |input| input + $total
        \\    add(n)
        \\}
    , true);
    defer staged.destroy();

    try staged.expectRejected("a `var`, whose value at the call is not always the value the description reads");
}

test "a function value the root reads from around itself has no Code.Value" {
    const staged = try Staged.createInBlock(std.testing.allocator,
        \\wobble : { f : U64 -> U64, x : U64 } -> U64
        \\wobble = |outer| {
        \\    g = outer.f
        \\    apply = |input| g(input)
        \\    apply(outer.x)
        \\}
    , true);
    defer staged.destroy();

    switch (staged.outcome) {
        .reified => return error.TestUnexpectedResult,
        .rejected => {},
    }
}

// M5: chains, `and`/`or`, nested `if`, literal folding, bounded `List.get`, case of case (plan 4.2).

const m5_sig = "wobble : { a : Bool, b : Bool, c : Bool, x : U64, y : U64 } -> U64\nwobble = |input| ";

fn expectM5Same(left: []const u8, right: []const u8) !void {
    const gpa = std.testing.allocator;
    const l = try std.fmt.allocPrint(gpa, "{s}{s}\n", .{ m5_sig, left });
    defer gpa.free(l);
    const r = try std.fmt.allocPrint(gpa, "{s}{s}\n", .{ m5_sig, right });
    defer gpa.free(r);
    try expectSameNormalForm(l, r);
}

fn expectM5Other(left: []const u8, right: []const u8) !void {
    const gpa = std.testing.allocator;
    const l = try std.fmt.allocPrint(gpa, "{s}{s}\n", .{ m5_sig, left });
    defer gpa.free(l);
    const r = try std.fmt.allocPrint(gpa, "{s}{s}\n", .{ m5_sig, right });
    defer gpa.free(r);
    try expectOtherNormalForm(l, r);
}

test "L3 M5: nested `if`s are `and` in every arm order" {
    const shapes = [_][]const u8{
        "if input.a { if input.b input.x else input.y } else input.y",
        "if input.a and input.b input.x else input.y",
        "if !input.a { input.y } else { if input.b input.x else input.y }",
        "match input.a { Bool.True => match input.b { Bool.True => input.x, Bool.False => input.y }, Bool.False => input.y }",
        "if !(input.a and input.b) input.y else input.x",
        "if !input.a or !input.b input.y else input.x",
    };
    for (shapes[1..]) |s| try expectM5Same(shapes[0], s);
}

test "L3 M5: nested `if`s are `or` in every arm order" {
    const shapes = [_][]const u8{
        "if input.a input.x else { if input.b input.x else input.y }",
        "if input.a or input.b input.x else input.y",
        "if !input.a { if input.b input.x else input.y } else input.x",
        "if input.b { input.x } else { if input.a input.x else input.y }",
    };
    for (shapes[1..2]) |s| try expectM5Same(shapes[0], s);
    try expectM5Same(shapes[2], shapes[0]);
}

test "L3 M5: a negated operand nests as `and` and `or` do" {
    try expectM5Same(
        "if input.a input.y else { if input.b input.x else input.y }",
        "if !input.a and input.b input.x else input.y",
    );
    try expectM5Same(
        "if input.a { if input.b input.x else input.y } else input.x",
        "if !input.a or input.b input.x else input.y",
    );
}

test "L3 M5: `and` and `or` of three operands regroup" {
    try expectM5Same(
        "if input.a and input.b and input.c input.x else input.y",
        "if input.a and (input.b and input.c) input.x else input.y",
    );
    try expectM5Same(
        "if (input.a and input.b) and input.c input.x else input.y",
        "if input.a { if input.b { if input.c input.x else input.y } else input.y } else input.y",
    );
    try expectM5Same(
        "if input.a or input.b or input.c input.x else input.y",
        "if input.a or (input.b or input.c) input.x else input.y",
    );
    try expectM5Same(
        "if input.a or input.b or input.c input.x else input.y",
        "if input.a input.x else if input.b input.x else if input.c input.x else input.y",
    );
}

test "L3 M5: De Morgan holds in a condition" {
    try expectM5Same(
        "if !(input.a or input.b) input.x else input.y",
        "if !input.a and !input.b input.x else input.y",
    );
}

test "L3 M5: De Morgan holds in a value" {
    try expectM5Same(
        "if !(input.a or input.b) input.x else input.y",
        "if input.a input.y else if input.b input.y else input.x",
    );
}

test "L3 M5: operand order of `and` and `or` stays" {
    try expectM5Other(
        "if input.a and input.b input.x else input.y",
        "if input.b and input.a input.x else input.y",
    );
    try expectM5Other(
        "if input.a or input.b input.x else input.y",
        "if input.b or input.a input.x else input.y",
    );
}

test "L3 M5: a `Bool.not` of a decided Bool in an arm folds" {
    try expectM5Same(
        "if input.a { if !input.a input.x else input.y } else input.y",
        "if input.a input.y else input.y",
    );
}

test "L3 M5: a literal on the left of a Str equality swaps" {
    try expectSameNormalForm(
        \\wobble : Str -> U64
        \\wobble = |input| if "a" == input 1 else 2
    ,
        \\wobble : Str -> U64
        \\wobble = |input| if input == "a" 1 else 2
    );
}

test "L3 M5: a run of literals in a chain folds" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| input.plus_wrap(1).plus_wrap(2)
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| input.plus_wrap(3)
    );
    try expectSameNormalForm(
        \\wobble : Str -> Str
        \\wobble = |input| Str.concat(Str.concat("a", "b"), input)
    ,
        \\wobble : Str -> Str
        \\wobble = |input| Str.concat("ab", input)
    );
}

test "L3 M5: float literals fold with the bits of the type" {
    try expectSameNormalForm(
        \\wobble : F32 -> F32
        \\wobble = |input| input * (0.1.F32 + 0.2.F32)
    ,
        \\wobble : F32 -> F32
        \\wobble = |input| input * 0.3.F32
    );
    try expectOtherNormalForm(
        \\wobble : F64 -> F64
        \\wobble = |input| input * (0.1.F64 + 0.2.F64)
    ,
        \\wobble : F64 -> F64
        \\wobble = |input| input * 0.3.F64
    );
}

test "L3 M5: a bounded `List.get` is the element" {
    try expectSameNormalForm(
        \\wobble : { xs : List(U64), i : U64 } -> U64
        \\wobble = |input| if input.i < input.xs.len() {
        \\    match input.xs.get(input.i) {
        \\        Ok(v) => v
        \\        Err(_) => 0
        \\    }
        \\} else 0
    ,
        \\wobble : { xs : List(U64), i : U64 } -> U64
        \\wobble = |input| if input.xs.len() <= input.i 0 else match input.xs.get(input.i) {
        \\    Ok(v) => v
        \\    Err(_) => 7
        \\}
    );
}

test "L3 M5: an unbounded `List.get` stays" {
    try expectOtherNormalForm(
        \\wobble : { xs : List(U64), i : U64 } -> U64
        \\wobble = |input| match input.xs.get(input.i) {
        \\    Ok(v) => v
        \\    Err(_) => 0
        \\}
    ,
        \\wobble : { xs : List(U64), i : U64 } -> U64
        \\wobble = |input| if input.i < input.xs.len() {
        \\    match input.xs.get(input.i) {
        \\        Ok(v) => v
        \\        Err(_) => 0
        \\    }
        \\} else 0
    );
}

test "L3 M5: a match on a helper's Try is the match in place" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    check = |m| if m < 10 Ok(m) else Err(m)
        \\    match check(input) {
        \\        Ok(v) => v + 1
        \\        Err(e) => e + 2
        \\    }
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| if input < 10 input + 1 else input + 2
    );
}

test "L3 M5: the arms of a nested tag match in either test order are one normal form" {
    try expectSameNormalForm(
        \\wobble : { a : [P, Q], t : [A, B] } -> U64
        \\wobble = |input| match input.a {
        \\    P => match input.t { A => 1, B => 2 }
        \\    Q => match input.t { A => 3, B => 4 }
        \\}
    ,
        \\wobble : { a : [P, Q], t : [A, B] } -> U64
        \\wobble = |input| match input.t {
        \\    A => match input.a { P => 1, Q => 3 }
        \\    B => match input.a { P => 2, Q => 4 }
        \\}
    );
}

test "L3 M5: a helper's Try with two arms giving one Err stays a match on the helper's result" {
    try expectOtherNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    check = |m| if m < 10 Err(1) else if m < 20 Err(1) else Ok(m)
        \\    match check(input) {
        \\        Ok(v) => v + 1
        \\        Err(e) => e + 2
        \\    }
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| if input < 10 input else input + 3
    );
}

// M6: three canonical loop forms (plan 4.1, order 8).

test "L3 M6: the three `sum_to` bodies of normal-form 11.1 are one ForRange" {
    const shapes = [_][]const u8{
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for i in 0..<input {
        \\        $total = $total + i
        \\    }
        \\    $total
        \\}
        ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $i = 0
        \\    var $total = 0
        \\    while $i < input {
        \\        $total = $total + $i
        \\        $i = $i + 1
        \\    }
        \\    $total
        \\}
        ,
        \\go : U64, U64, U64 -> U64
        \\go = |acc, i, input| if i < input go(acc + i, i + 1, input) else acc
        \\
        \\wobble : U64 -> U64
        \\wobble = |input| go(0, 0, input)
    };
    for (shapes[1..]) |s| try expectSameNormalForm(shapes[0], s);
}

test "L3 M6: a counter `while` is the `for` over a range" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $i = 0
        \\    var $count = 0
        \\    while $i < input {
        \\        $count = $count + 3
        \\        $i = $i + 1
        \\    }
        \\    $count
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $count = 0
        \\    for _i in 0..<input {
        \\        $count = $count + 3
        \\    }
        \\    $count
        \\}
    );
}

test "L3 M6: a `while` that tests the length and reads by index is the `for` over the list" {
    try expectSameNormalForm(
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $i = 0
        \\    var $total = 0
        \\    while $i < input.len() {
        \\        $total = $total + (input.get($i) ?? 0)
        \\        $i = $i + 1
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for x in input {
        \\        $total = $total + x
        \\    }
        \\    $total
        \\}
    );
}

test "L3 M6: `for x in input` and `for x in input.iter()` are one ForList" {
    try expectSameNormalForm(
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for x in input {
        \\        $total = $total + x
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for x in input.iter() {
        \\        $total = $total + x
        \\    }
        \\    $total
        \\}
    );
}

test "L3 M6: a filtered iterator stays a general loop, so it is not the plain `for`" {
    try expectOtherNormalForm(
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for x in input.iter().keep_if(|y| y > 2) {
        \\        $total = $total + x
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for x in input {
        \\        $total = $total + x
        \\    }
        \\    $total
        \\}
    );
}

test "L3 M6: `while $i <= n` stays a general loop, so it is not the `for` over a range" {
    try expectOtherNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $i = 0
        \\    var $total = 0
        \\    while $i <= input {
        \\        $total = $total + $i
        \\        $i = $i + 1
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for i in 0..<input {
        \\        $total = $total + i
        \\    }
        \\    $total
        \\}
    );
}

test "L3 M12: a loop with a `$done` flag is the `for` over a range (N11n, then N11l)" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $i = 0
        \\    var $total = 0
        \\    var $done = Bool.False
        \\    while !$done {
        \\        if $i < input {
        \\            $total = $total + $i
        \\            $i = $i + 1
        \\        } else {
        \\            $done = Bool.True
        \\        }
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for i in 0..<input {
        \\        $total = $total + i
        \\    }
        \\    $total
        \\}
    );
}

test "L3 M12: a second counter derived from the first is the index plus its start (N11o)" {
    // M6 compared `$total + i + $j` with `$total + i + 5`, which differ from
    // the second turn on; the pair that computes one value is `i + 5`.
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    var $j = 5
        \\    for i in 0..<input {
        \\        $total = $total + i + $j
        \\        $j = $j + 1
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for i in 0..<input {
        \\        $total = $total + i + (i + 5)
        \\    }
        \\    $total
        \\}
    );
}

test "L3 M6: `while Bool.True` with a `break` is the `while` on the test" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $i = 0
        \\    var $total = 0
        \\    while Bool.True {
        \\        if $i >= input {
        \\            break
        \\        }
        \\        $total = $total + $i
        \\        $i = $i + 1
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $i = 0
        \\    var $total = 0
        \\    while $i < input {
        \\        $total = $total + $i
        \\        $i = $i + 1
        \\    }
        \\    $total
        \\}
    );
}

// `continue` is not in the language yet (docs/langref/statements.md), so the
// turn of a loop ends in a `Continue` the walk writes. The pair is the update
// made in each branch and the update made once from the branches' value.
test "L3 M6: an update in each branch of an `if` is one update to the `if`" {
    try expectSameNormalForm(
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for x in input {
        \\        if x > 5 {
        \\            $total = $total + 1
        \\        } else {
        \\            $total = $total + x
        \\        }
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for x in input {
        \\        $total = if x > 5 $total + 1 else $total + x
        \\    }
        \\    $total
        \\}
    );
}

test "L3 M6: `if c { break }; rest` is `rest` in the `else`" {
    try expectSameNormalForm(
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for x in input {
        \\        if x > 100 {
        \\            break
        \\        }
        \\        $total = $total + x
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for x in input {
        \\        if x > 100 {
        \\            break
        \\        } else {
        \\            $total = $total + x
        \\        }
        \\    }
        \\    $total
        \\}
    );
}

// M7: aggregate parameters of private helpers and aggregate loop slots are
// split into their components (plan 4.2, N14a and N14b).

test "L3 M7: `f(a, b)` is `f({ a, b })` for a private helper" {
    try expectSameNormalForm(
        \\f : U64, U64 -> U64
        \\f = |a, b| a * 2 + b * 3
        \\
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |input| f(input.x, input.y) + f(input.y, input.x)
    ,
        \\f : { a : U64, b : U64 } -> U64
        \\f = |r| r.a * 2 + r.b * 3
        \\
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |input| f({ a: input.x, b: input.y }) + f({ a: input.y, b: input.x })
    );
}

test "L3 M7: `f(a, b)` is `f((a, b))` for a private helper" {
    try expectSameNormalForm(
        \\f : U64, U64 -> U64
        \\f = |a, b| a * 2 + b * 3
        \\
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |input| f(input.x, input.y) + f(input.y, input.x)
    ,
        \\f : (U64, U64) -> U64
        \\f = |t| t.0 * 2 + t.1 * 3
        \\
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |input| f((input.x, input.y)) + f((input.y, input.x))
    );
}

test "L3 M7: a record parameter written as a destructuring pattern is the record" {
    try expectSameNormalForm(
        \\f : { a : U64, b : U64 } -> U64
        \\f = |{ a, b }| a * 2 + b * 3
        \\
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |input| f({ a: input.x, b: input.y }) + f({ a: input.y, b: input.x })
    ,
        \\f : { a : U64, b : U64 } -> U64
        \\f = |r| r.a * 2 + r.b * 3
        \\
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |input| f({ a: input.x, b: input.y }) + f({ a: input.y, b: input.x })
    );
}

test "L3 M7: a record that holds a record is split through both" {
    try expectSameNormalForm(
        \\f : U64, U64, U64 -> U64
        \\f = |a, b, c| a * 2 + b * 3 + c
        \\
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |input| f(input.x, input.y, 1) + f(input.y, input.x, 2)
    ,
        \\f : { head : { a : U64, b : U64 }, c : U64 } -> U64
        \\f = |r| r.head.a * 2 + r.head.b * 3 + r.c
        \\
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |input| f({ head: { a: input.x, b: input.y }, c: 1 }) + f({ head: { a: input.y, b: input.x }, c: 2 })
    );
}

test "L3 M7: a helper that returns its record whole is not the helper that takes the fields" {
    try expectOtherNormalForm(
        \\f : U64, U64 -> U64
        \\f = |a, b| a * 2 + b * 3
        \\
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |input| f(input.x, input.y) + f(input.y, input.x)
    ,
        \\same : { a : U64, b : U64 } -> { a : U64, b : U64 }
        \\same = |r| r
        \\
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |input| {
        \\    p = same({ a: input.x, b: input.y })
        \\    q = same({ a: input.y, b: input.x })
        \\    p.a * 2 + p.b * 3 + q.a * 2 + q.b * 3
        \\}
    );
}

test "L3 M7: a record `var` is one `var` per field" {
    try expectSameNormalForm(
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $acc = { a: 0, b: 0 }
        \\    for x in input {
        \\        $acc = { a: $acc.a + x, b: $acc.b + 1 }
        \\    }
        \\    $acc.a + $acc.b
        \\}
    ,
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $a = 0
        \\    var $b = 0
        \\    for x in input {
        \\        $a = $a + x
        \\        $b = $b + 1
        \\    }
        \\    $a + $b
        \\}
    );
}

test "L3 M7: a tuple `var` is one `var` per element" {
    try expectSameNormalForm(
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $acc = (0, 0)
        \\    for x in input {
        \\        $acc = ($acc.0 + x, $acc.1 + 1)
        \\    }
        \\    $acc.0 + $acc.1
        \\}
    ,
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $a = 0
        \\    var $b = 0
        \\    for x in input {
        \\        $a = $a + x
        \\        $b = $b + 1
        \\    }
        \\    $a + $b
        \\}
    );
}

test "L3 M7: a field of a record `var` that nothing changes is not a slot" {
    try expectSameNormalForm(
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $acc = { total: 0, spare: 7 }
        \\    for x in input {
        \\        $acc = { total: $acc.total + x, spare: $acc.spare }
        \\    }
        \\    $acc.total + $acc.spare
        \\}
    ,
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for x in input {
        \\        $total = $total + x
        \\    }
        \\    $total + 7
        \\}
    );
}

test "L3 M7: a record `var` that a loop passes whole to a helper stays a record" {
    try expectOtherNormalForm(
        \\same : { a : U64, b : U64 } -> { a : U64, b : U64 }
        \\same = |r| r
        \\
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $acc = { a: 0, b: 0 }
        \\    for x in input {
        \\        $acc = same(same({ a: $acc.a + x, b: $acc.b + 1 }))
        \\    }
        \\    $acc.a + $acc.b
        \\}
    ,
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $a = 0
        \\    var $b = 0
        \\    for x in input {
        \\        $a = $a + x
        \\        $b = $b + 1
        \\    }
        \\    $a + $b
        \\}
    );
}

// T1.11 and the speculatable conditions read the operand cone: `x - x` over a
// field of a loop output keeps the loop, because the loop can crash on
// checked-integer overflow (C2).
const record_accumulator_source =
    \\wobble : List(U64) -> U64
    \\wobble = |input| {
    \\    lc = {
    \\        var $acc = { total: 0, spare: 0 }
    \\        for x in input { $acc = { total: $acc.total + x, spare: $acc.spare } }
    \\        $acc.total
    \\    }
    \\    lc - lc
    \\}
;
const scalar_accumulator_source =
    \\wobble : List(U64) -> U64
    \\wobble = |input| {
    \\    lc = {
    \\        var $acc = 0
    \\        for x in input { $acc = $acc + x }
    \\        $acc
    \\    }
    \\    lc - lc
    \\}
;

test "L3 M7: `lc - lc` over a record accumulator and over a scalar one keep the loop and meet" {
    try expectSameNormalForm(record_accumulator_source, scalar_accumulator_source);
    const gpa = std.testing.allocator;
    const staged = try Staged.createRunning(gpa, record_accumulator_source, "");
    defer staged.destroy();
    try std.testing.expect(staged.outcome == .reified);
    try std.testing.expect(std.mem.indexOf(u8, staged.dump.items, "minus") != null);
}

test "L5 M7: `lc - lc` over a record accumulator crashes on overflow as Roc does, and is 0 otherwise" {
    const gpa = std.testing.allocator;
    const staged = try Staged.createRunning(gpa, record_accumulator_source, "");
    defer staged.destroy();
    try std.testing.expect(staged.outcome == .reified);
    var values_impl = std.heap.ArenaAllocator.init(gpa);
    defer values_impl.deinit();
    const values = values_impl.allocator();
    const site = staged.walk.site.?;
    var evaluator = try reify.eval.Evaluator.init(values, &site.store, &site.types, .strict);
    const small = [_]reify.eval.Value{ .{ .int = 3 }, .{ .int = 4 } };
    const fits = try evaluator.run(staged.walk.root.?, &.{.{ .list = &small }});
    try std.testing.expect(fits.eql(.{ .int = 0 }));
    const big = [_]reify.eval.Value{ .{ .int = std.math.maxInt(u64) }, .{ .int = 1 } };
    try std.testing.expectError(error.Crash, evaluator.run(staged.walk.root.?, &.{.{ .list = &big }}));
}

// The gap M3 left (plan 4.1): a lambda that captures a whole record, and a
// helper that takes one of its fields.
test "L3 M7: a lambda that captures a whole record meets a helper that takes the field" {
    try expectSameNormalForm(
        \\wobble : { j : U64, k : U64, x : U64 } -> U64
        \\wobble = |input| {
        \\    r = { j: input.j, k: input.k }
        \\    f = |y| y + r.k
        \\    f(input.x) * f(input.j)
        \\}
    ,
        \\add : U64, U64 -> U64
        \\add = |k, y| y + k
        \\
        \\wobble : { j : U64, k : U64, x : U64 } -> U64
        \\wobble = |input| add(input.k, input.x) * add(input.k, input.j)
    );
}

test "L4 and L5 M7: scalar replacement keeps every seed's two prints one normal form" {
    // The generator's M7 choices (a helper spelled five ways, an accumulator
    // spelled as a scalar, a record or a tuple) are on here.
    var prng = std.Random.DefaultPrng.init(0x7007);
    const random = prng.random();
    var bytes: [96]u8 = undefined;
    var verdicts = std.EnumArray(reify_fuzz.Verdict, u32).initFill(0);
    for (0..400) |_| {
        random.bytes(&bytes);
        var tmp = std.testing.tmpDir(.{});
        defer tmp.cleanup();
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const ctx = CoreCtx.default(std.testing.allocator, arena.allocator(), std.testing.io);
        verdicts.getPtr(try reify_fuzz.runCaseWith(ctx, try sharedBuiltinModules(), tmp.dir, &bytes, .{ .m7 = true })).* += 1;
    }
    try std.testing.expect(verdicts.get(.agree) > 0);
}

// M8, V5a: `inline_digest`. A node's digest is its content in the `inline`
// view, so spellings that meet give each node one digest, and a change to
// what a node computes changes it and the digests of the nodes that read it.

/// Every node digest of the `inline` view of `wobble`, row by row.
fn inlineDigests(gpa: Allocator, source: []const u8) (StagedError || error{ TestUnexpectedResult, TestExpectedEqual })![]u128 {
    const staged = try Staged.createInlined(gpa, source);
    defer staged.destroy();
    if (staged.outcome != .reified) {
        try staged.expectDump("");
        return error.TestUnexpectedResult;
    }
    // `Inlined := { digests, graph, site, version }`, in label order.
    const rows = staged.store.get(staged.store.get(staged.outcome.reified).record[0]).list.nodes;
    var out: std.ArrayList(u128) = .empty;
    errdefer out.deinit(gpa);
    for (rows) |row| for (staged.store.get(row).list.nodes) |digest| {
        try out.append(gpa, staged.store.get(digest).scalar.u128);
    };
    return out.toOwnedSlice(gpa);
}

fn expectSameDigests(left: []const u8, right: []const u8) !void {
    const gpa = std.testing.allocator;
    const a = try inlineDigests(gpa, left);
    defer gpa.free(a);
    const b = try inlineDigests(gpa, right);
    defer gpa.free(b);
    try std.testing.expect(a.len > 0);
    try std.testing.expectEqualSlices(u128, a, b);
}

/// The digests differ, as lists, and their last entry, which is the node
/// the function returns, differs too. `shared` is how many entries from the
/// start stay equal.
fn expectOtherDigests(left: []const u8, right: []const u8, shared: usize) !void {
    const gpa = std.testing.allocator;
    const a = try inlineDigests(gpa, left);
    defer gpa.free(a);
    const b = try inlineDigests(gpa, right);
    defer gpa.free(b);
    try std.testing.expect(a.len > 0 and b.len > 0);
    try std.testing.expect(a[a.len - 1] != b[b.len - 1]);
    try std.testing.expectEqualSlices(u128, a[0..shared], b[0..shared]);
    // Every digest of the unchanged part of one side is on the other side
    // only if the node it names is, so no digest of a changed node repeats.
    for (a[shared..]) |d| if (std.mem.findScalar(u128, b[shared..], d) != null) {
        // A node the change did not reach can still repeat; the last never does.
        try std.testing.expect(d != a[a.len - 1]);
    };
}

const m8_helper =
    \\step : U64 -> U64
    \\step = |x| x * 3 + 1
    \\
;

test "L3 M8: a helper called twice and its body written out have one inline_digest per node" {
    try expectSameDigests(
        m8_helper ++
            \\wobble : U64 -> U64
            \\wobble = |input| step(input) + step(input + 7)
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| (input * 3 + 1) + ((input + 7) * 3 + 1)
    );
}

test "L3 M8: extracting a helper, in any parameter order, keeps every inline_digest" {
    try expectSameDigests(
        \\wobble : U64 -> U64
        \\wobble = |input| (input * 3 + 1) + ((input + 7) * 3 + 1)
    ,
        \\scale : U64, U64 -> U64
        \\scale = |k, x| x * k + 1
        \\
        \\wobble : U64 -> U64
        \\wobble = |input| scale(3, input) + scale(3, input + 7)
    );
    try expectSameDigests(
        \\wobble : U64 -> U64
        \\wobble = |input| (input * 3 + 1) + ((input + 7) * 3 + 1)
    ,
        \\once : U64 -> U64
        \\once = |x| x * 3 + 1
        \\
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    base = once(input)
        \\    shifted = once(input + 7)
        \\    base + shifted
        \\}
    );
}

test "L3 M8: renamed bindings, a reorder and an if against a match keep every inline_digest" {
    try expectSameDigests(
        \\wobble : U64 -> U64
        \\wobble = |input| (input * 3 + 1) + ((input + 7) * 3 + 1)
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    shifted = input + 7
        \\    first = input * 3 + 1
        \\    second = shifted * 3 + 1
        \\    first + second
        \\}
    );
    try expectSameDigests(
        \\wobble : U64 -> U64
        \\wobble = |input| if input < 10 input * 2 else input + 5
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| match input < 10 {
        \\    Bool.True => input * 2
        \\    Bool.False => input + 5
        \\}
    );
}

test "L3 M8: a change to what a node computes changes the digests of the node and its readers" {
    // The constant changes the second `step`'s argument, so the first
    // half of the nodes stay and the sum changes.
    try expectOtherDigests(
        m8_helper ++
            \\wobble : U64 -> U64
            \\wobble = |input| step(input) + step(input + 7)
    ,
        m8_helper ++
            \\wobble : U64 -> U64
            \\wobble = |input| step(input) + step(input + 8)
    , 1);
    // A different operation in the helper changes every node that reads it.
    try expectOtherDigests(
        m8_helper ++
            \\wobble : U64 -> U64
            \\wobble = |input| step(input) + step(input + 7)
    ,
        \\step : U64 -> U64
        \\step = |x| x * 3 - 1
        \\
        \\wobble : U64 -> U64
        \\wobble = |input| step(input) + step(input + 7)
    , 0);
}

test "L3 M8: a recursive helper's call is named by its body" {
    const body =
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    go = |n, acc| if n == 0 acc else go(n - 1, acc + CHANGE)
        \\    go(input, 0)
        \\}
    ;
    const gpa = std.testing.allocator;
    const one = try std.mem.replaceOwned(u8, gpa, body, "CHANGE", "2");
    defer gpa.free(one);
    const same = try std.mem.replaceOwned(u8, gpa, body, "CHANGE", "2");
    defer gpa.free(same);
    const other = try std.mem.replaceOwned(u8, gpa, body, "CHANGE", "3");
    defer gpa.free(other);
    try expectSameDigests(one, same);
    const a = try inlineDigests(gpa, one);
    defer gpa.free(a);
    const b = try inlineDigests(gpa, other);
    defer gpa.free(b);
    try std.testing.expect(!std.mem.eql(u128, a, b));
}

// M9, V3: the `outline` view. It is a function of `inline`, so the refactors
// that keep `inline` keep it, and each computation of at least K nodes that
// repeats becomes one row that every place calls.

/// The `outline` dump of `source`'s `wobble`.
fn expectOutlineDump(source: []const u8, expected: []const u8) !void {
    const staged = try Staged.createOutlined(std.testing.allocator, source);
    defer staged.destroy();
    try staged.expectDump(expected);
}

/// The two sources describe to one dump in `outline`, and to two in `graph`.
fn expectSameOutlineOnly(left: []const u8, right: []const u8) !void {
    const gpa = std.testing.allocator;
    const a = try Staged.createRunning(gpa, left, "");
    defer a.destroy();
    const b = try Staged.createRunning(gpa, right, "");
    defer b.destroy();
    try std.testing.expect(a.outcome == .reified and b.outcome == .reified);
    try std.testing.expect(!std.mem.eql(u8, a.dump.items, b.dump.items));
    try expectSameView(a, b, .outline);
}

/// `source`'s `wobble` has one dump in `inline` and `outline`: nothing of it
/// is outlined.
fn expectNotOutlined(source: []const u8) !void {
    const gpa = std.testing.allocator;
    const staged = try Staged.createRunning(gpa, source, "");
    defer staged.destroy();
    const inlined = try staged.viewDump(.inline_) orelse return error.TestUnexpectedResult;
    defer gpa.free(inlined);
    const outlined = try staged.viewDump(.outline) orelse return error.TestUnexpectedResult;
    defer gpa.free(outlined);
    try std.testing.expectEqualStrings(inlined, outlined);
}

const m9_helper =
    \\step : U64 -> U64
    \\step = |x| ((x * 3 + 1) * x + 5) * x
    \\
;

// The inner `step(input)` is read by the outer `step` and by the sum, so it
// is a computation of its own and the outer one reads it as a hole. Both
// have the shape of `step`.
const m9_twice =
    \\wobble : U64 -> U64
    \\wobble = |input| step(input) + step(step(input))
;

test "L3 M9: a helper called from two places is one row of the outline view" {
    try expectOutlineDump(m9_helper ++ m9_twice,
        \\row r0 (U64) -> U64
        \\  n0 = call r1(p0) : U64 !spec
        \\  n1 = call r1(n0) : U64 !spec
        \\  n2 = Num.U64.plus(n0, n1) : U64 !spec
        \\  value n2
        \\row r1 (U64) -> U64
        \\  n0 = 3 : U64
        \\  n1 = Num.U64.times(p0, n0) : U64 !spec
        \\  n2 = 1 : U64
        \\  n3 = Num.U64.plus(n1, n2) : U64 !spec
        \\  n4 = Num.U64.times(n3, p0) : U64 !spec
        \\  n5 = 5 : U64
        \\  n6 = Num.U64.plus(n4, n5) : U64 !spec
        \\  n7 = Num.U64.times(n6, p0) : U64 !spec
        \\  value n7
        \\
    );
}

test "L3 M9: a helper called twice and its body written out twice meet in outline, not in graph" {
    try expectSameOutlineOnly(m9_helper ++ m9_twice,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    s = ((input * 3 + 1) * input + 5) * input
        \\    s + ((s * 3 + 1) * s + 5) * s
        \\}
    );
}

test "L3 M9: extracting a helper over its parameters in another order keeps the outline view" {
    try expectSameOutlineOnly(
        \\scale : U64, U64 -> U64
        \\scale = |k, x| ((x * k + 1) * x + 5) * x
        \\
        \\wobble : U64 -> U64
        \\wobble = |input| scale(3, input) + scale(3, scale(3, input))
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    s = ((input * 3 + 1) * input + 5) * input
        \\    s + ((s * 3 + 1) * s + 5) * s
        \\}
    );
}

test "L3 M9: a computation a third place also reads part of stays apart from the two that do not share it" {
    // `input * 3 + 1` is read by the inner `step` and by the sum, so the
    // inner `step` reads it as a hole and the outer one does not: the two
    // have different shapes.
    try expectNotOutlined(m9_helper ++
        \\wobble : U64 -> U64
        \\wobble = |input| step(input) + step(step(input)) + (input * 3 + 1)
    );
}

test "L3 M9: a switch that returns from the function stays, and the computations in it are outlined" {
    // The two loop bodies have one shape, and the `switch` of each is the
    // largest cone. A row cannot return from its caller, so the `switch`
    // stays, and its condition and its returned value are rows.
    try expectOutlineDump(
        \\wobble : { xs : List(U64), ys : List(U64) } -> U64
        \\wobble = |input| {
        \\    for x in input.xs {
        \\        if ((x * 3 + 1) * x + 5) * x > 100 {
        \\            return ((x * 7 + 2) * x + 1) * x
        \\        }
        \\    }
        \\    for y in input.ys {
        \\        if ((y * 3 + 1) * y + 5) * y > 100 {
        \\            return ((y * 7 + 2) * y + 1) * y
        \\        }
        \\    }
        \\    0
        \\}
    ,
        \\row r0 ({ xs : List(U64), ys : List(U64) }) -> U64
        \\  n0 = 0 : U64
        \\  n1 = field 0(p0) : List(U64)
        \\  n5 = for_list(n1) : !spec
        \\    body (s5.0: U64, s5.1: U64)
        \\      n2 = call r1(s5.1) : Bool !spec
        \\      n4 = switch n2 : !spec
        \\        arm 0
        \\          continue
        \\        arm 1
        \\          n3 = call r2(s5.1) : U64 !spec
        \\          return n3
        \\      branch n4
        \\  n6 = field 1(p0) : List(U64)
        \\  n10 = for_list(n6) : !spec
        \\    body (s10.0: U64, s10.1: U64)
        \\      n7 = call r1(s10.1) : Bool !spec
        \\      n9 = switch n7 : !spec
        \\        arm 0
        \\          continue
        \\        arm 1
        \\          n8 = call r2(s10.1) : U64 !spec
        \\          return n8
        \\      branch n9
        \\  value n0
        \\row r1 (U64) -> Bool
        \\  n0 = 100 : U64
        \\  n1 = 3 : U64
        \\  n2 = Num.U64.times(p0, n1) : U64 !spec
        \\  n3 = 1 : U64
        \\  n4 = Num.U64.plus(n2, n3) : U64 !spec
        \\  n5 = Num.U64.times(n4, p0) : U64 !spec
        \\  n6 = 5 : U64
        \\  n7 = Num.U64.plus(n5, n6) : U64 !spec
        \\  n8 = Num.U64.times(n7, p0) : U64 !spec
        \\  n9 = Num.U64.is_lt(n0, n8) : Bool
        \\  value n9
        \\row r2 (U64) -> U64
        \\  n0 = 7 : U64
        \\  n1 = Num.U64.times(p0, n0) : U64 !spec
        \\  n2 = 2 : U64
        \\  n3 = Num.U64.plus(n1, n2) : U64 !spec
        \\  n4 = Num.U64.times(n3, p0) : U64 !spec
        \\  n5 = 1 : U64
        \\  n6 = Num.U64.plus(n4, n5) : U64 !spec
        \\  n7 = Num.U64.times(n6, p0) : U64 !spec
        \\  value n7
        \\
    );
}

// V3b: anti-unification. Places that differ in a value are one row when the
// value can be a hole (normal-form 5.3, rules 3 and 4).

/// The `inline` and `outline` views of `source`'s `wobble`, over a record
/// `{ a : U64, b : U64 }`, compute one value on each of `inputs`.
fn expectOutlineAgrees(source: []const u8, inputs: []const [2]i128) !void {
    const gpa = std.testing.allocator;
    const inlined = try Staged.createInlined(gpa, source);
    defer inlined.destroy();
    const outlined = try Staged.createOutlined(gpa, source);
    defer outlined.destroy();
    try std.testing.expect(inlined.outcome == .reified and outlined.outcome == .reified);
    var values_impl = std.heap.ArenaAllocator.init(gpa);
    defer values_impl.deinit();
    const values = values_impl.allocator();
    for (inputs) |input| {
        const fields = try values.alloc(reify.eval.Value, 2);
        for (fields, input) |*field, v| field.* = .{ .int = v };
        const args = [_]reify.eval.Value{.{ .agg = fields }};
        var computed: [2]reify.eval.Value = undefined;
        for ([_]*Staged{ inlined, outlined }, &computed) |staged, *value| {
            const site = staged.walk.site.?;
            var evaluator = try reify.eval.Evaluator.init(values, &site.store, &site.types, .strict);
            value.* = try evaluator.run(staged.walk.root.?, &args);
        }
        try std.testing.expect(computed[0].eql(computed[1]));
    }
}

const v3b_step =
    \\step : U64 -> U64
    \\step = |x| ((x * 3 + 1) * x + 5) * x
    \\
;

const v3b_fields =
    \\wobble : { a : U64, b : U64 } -> U64
    \\wobble = |input| step(input.a) + step(input.b)
;

test "L3 V3b: `step(input.a)` and `step(input.b)` are one row, and each place passes its field" {
    try expectOutlineDump(v3b_step ++ v3b_fields,
        \\row r0 ({ a : U64, b : U64 }) -> U64
        \\  n0 = field 0(p0) : U64
        \\  n1 = call r1(n0) : U64 !spec
        \\  n2 = field 1(p0) : U64
        \\  n3 = call r1(n2) : U64 !spec
        \\  n4 = Num.U64.plus(n1, n3) : U64 !spec
        \\  value n4
        \\row r1 (U64) -> U64
        \\  n0 = 3 : U64
        \\  n1 = Num.U64.times(p0, n0) : U64 !spec
        \\  n2 = 1 : U64
        \\  n3 = Num.U64.plus(n1, n2) : U64 !spec
        \\  n4 = Num.U64.times(n3, p0) : U64 !spec
        \\  n5 = 5 : U64
        \\  n6 = Num.U64.plus(n4, n5) : U64 !spec
        \\  n7 = Num.U64.times(n6, p0) : U64 !spec
        \\  value n7
        \\
    );
    try expectOutlineAgrees(v3b_step ++ v3b_fields, &.{ .{ 1, 2 }, .{ 0, 7 }, .{ 300, 11 } });
}

test "L3 V3b: the body of `step` written out over two fields meets the helper in outline, not in graph" {
    try expectSameOutlineOnly(v3b_step ++ v3b_fields,
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| ((input.a * 3 + 1) * input.a + 5) * input.a + ((input.b * 3 + 1) * input.b + 5) * input.b
    );
}

// `scale(1, x)` folds `x * 1` to `x`, so the two places differ in that
// node: the row takes it as a parameter and keeps the rest.
const v3b_scaled =
    \\scale : U64, U64 -> U64
    \\scale = |k, x| ((x * k + 1) * x + 5) * x
    \\
    \\wobble : { a : U64, b : U64 } -> U64
    \\wobble = |input| scale(1, input.a) + scale(2, input.b)
;

test "L3 V3b: a helper called with constants that fold differently shares only the common part" {
    try expectOutlineDump(v3b_scaled,
        \\row r0 ({ a : U64, b : U64 }) -> U64
        \\  n0 = field 0(p0) : U64
        \\  n1 = call r1(n0, n0) : U64 !spec
        \\  n2 = field 1(p0) : U64
        \\  n3 = 2 : U64
        \\  n4 = Num.U64.times(n2, n3) : U64 !spec
        \\  n5 = call r1(n4, n2) : U64 !spec
        \\  n6 = Num.U64.plus(n1, n5) : U64 !spec
        \\  value n6
        \\row r1 (U64, U64) -> U64
        \\  n0 = 1 : U64
        \\  n1 = Num.U64.plus(p0, n0) : U64 !spec
        \\  n2 = Num.U64.times(n1, p1) : U64 !spec
        \\  n3 = 5 : U64
        \\  n4 = Num.U64.plus(n2, n3) : U64 !spec
        \\  n5 = Num.U64.times(n4, p1) : U64 !spec
        \\  value n5
        \\
    );
    try expectOutlineAgrees(v3b_scaled, &.{ .{ 1, 2 }, .{ 0, 7 }, .{ 300, 11 } });
}

// An interpolated literal of the author's own type is converted in two stages
// (static-dispatch.md). The walk runs the first stage by its definition where
// the literal stands, because the segments are literals, and the literal is
// the closure that stage hands back, applied to the list of the interpolated
// values.

test "an interpolated literal of a type that escapes its values describes as the escaped fold" {
    // The conversion rejects segments, so its first stage branches. The
    // program compiled, so that stage returned `Ok` for these segments: the
    // arm that only delivers `Err` is not taken, and nothing of the test it
    // would have made is described. `Str.from_interpolation` is walked too,
    // so the literal is its fold over the values, which this conversion
    // escapes first.
    const staged = try Staged.create(std.testing.allocator,
        \\Html := [Html(Str)].{
        \\    from_interpolation : List(Str) -> Try((List(Str) -> Html), [InvalidInterpolation(Str)])
        \\    from_interpolation = |segments|
        \\        if segments.any(|segment| segment.contains("<script")) {
        \\            Err(InvalidInterpolation("no scripts"))
        \\        } else {
        \\            Str.from_interpolation(segments).map_ok(|assemble|
        \\                |values| Html(assemble(values.map(|value| value.replace_each("<", "&lt;")))))
        \\        }
        \\    width : Html, F32 -> F32
        \\    width = |h, f| match h {
        \\        Html(text) => if text.is_empty() 0.0.F32 else f
        \\    }
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| "<p>${input.uv.to_str()}!</p>".Html.width(input.uv)
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 1(p0) : F32
        \\  n1 = Num.F32.to_str(n0) : Str !spec
        \\  n2 = "<" : Str
        \\  n3 = "&lt;" : Str
        \\  n4 = Str.replace_each(n1, n2, n3) : Str !spec
        \\  n5 = list(n4) : List(Str)
        \\  n6 = "<p>" : Str
        \\  n7 = tag Ok(n6) : [Err([ListWasEmpty]), Ok(Str)]
        \\  n8 = wrap(n7) : Builtin.Try
        \\  n9 = "" : Str
        \\  n10 = Try.ok_or(n8, n9) : Str !spec
        \\  n11 = "!</p>" : Str
        \\  n12 = list(n6, n11) : List(Str)
        \\  n13 = closure r1(n12) : (Str, Str, U64 -> Str)
        \\  n14 = List.fold_with_index(n5, n10, n13) : Str !spec
        \\  n15 = Str.is_empty(n14) : Bool !spec
        \\  n17 = switch n15 : F32
        \\    arm 0
        \\      value n0
        \\    arm 1
        \\      n16 = float 0x0 : F32
        \\      value n16
        \\  value n17
        \\row r1 (List(Str), Str, Str, U64) -> Str
        \\  n0 = 1 : U64
        \\  n1 = Num.U64.plus(p3, n0) : U64 !spec
        \\  n2 = List.get(p0, n1) : Builtin.Try
        \\  n3 = "" : Str
        \\  n4 = Try.ok_or(n2, n3) : Str !spec
        \\  n5 = Str.concat(p1, p2, n4) : Str
        \\  value n5
        \\
    );
}

test "an interpolated literal of a type that only wraps the assembler of Str describes as the fold of Str" {
    const staged = try Staged.create(std.testing.allocator,
        \\Label := { text : Str }.{
        \\    from_interpolation : List(Str) -> Try((List(Str) -> Label), [InvalidInterpolation(Str)])
        \\    from_interpolation = |segments| Str.from_interpolation(segments).map_ok(|assemble| |values| { text: assemble(values) })
        \\    width : Label, F32 -> F32
        \\    width = |l, f| if l.text.is_empty() 0.0.F32 else f
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| "a${input.uv.to_str()}b".Label.width(input.uv)
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = field 1(p0) : F32
        \\  n1 = Num.F32.to_str(n0) : Str !spec
        \\  n2 = list(n1) : List(Str)
        \\  n3 = "a" : Str
        \\  n4 = tag Ok(n3) : [Err([ListWasEmpty]), Ok(Str)]
        \\  n5 = wrap(n4) : Builtin.Try
        \\  n6 = "" : Str
        \\  n7 = Try.ok_or(n5, n6) : Str !spec
        \\  n8 = "b" : Str
        \\  n9 = list(n3, n8) : List(Str)
        \\  n10 = closure r1(n9) : (Str, Str, U64 -> Str)
        \\  n11 = List.fold_with_index(n2, n7, n10) : Str !spec
        \\  n12 = Str.is_empty(n11) : Bool !spec
        \\  n14 = switch n12 : F32
        \\    arm 0
        \\      value n0
        \\    arm 1
        \\      n13 = float 0x0 : F32
        \\      value n13
        \\  value n14
        \\row r1 (List(Str), Str, Str, U64) -> Str
        \\  n0 = 1 : U64
        \\  n1 = Num.U64.plus(p3, n0) : U64 !spec
        \\  n2 = List.get(p0, n1) : Builtin.Try
        \\  n3 = "" : Str
        \\  n4 = Try.ok_or(n2, n3) : Str !spec
        \\  n5 = Str.concat(p1, p2, n4) : Str
        \\  value n5
        \\
    );
}

test "an interpolated literal of a conversion that reads its segments carries them as a list" {
    const staged = try Staged.create(std.testing.allocator,
        \\Joined := { text : Str }.{
        \\    from_interpolation : List(Str) -> Try((List(Str) -> Joined), [InvalidInterpolation(Str)])
        \\    from_interpolation = |segments| Ok(|values| { text: Str.join_with(segments.concat(values), "-") })
        \\    width : Joined, F32 -> F32
        \\    width = |j, f| if j.text.is_empty() 0.0.F32 else f
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| "a${input.uv.to_str()}b".Joined.width(input.uv)
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = "a" : Str
        \\  n1 = "b" : Str
        \\  n2 = field 1(p0) : F32
        \\  n3 = Num.F32.to_str(n2) : Str !spec
        \\  n4 = list(n0, n1, n3) : List(Str)
        \\  n5 = "-" : Str
        \\  n6 = Str.join_with(n4, n5) : Str !spec
        \\  n7 = Str.is_empty(n6) : Bool !spec
        \\  n9 = switch n7 : F32
        \\    arm 0
        \\      value n2
        \\    arm 1
        \\      n8 = float 0x0 : F32
        \\      value n8
        \\  value n9
        \\
    );
}

test "an interpolated literal passed as an argument describes as the value it converts to" {
    const staged = try Staged.create(std.testing.allocator,
        \\Wrapped := { text : Str }.{
        \\    from_interpolation : List(Str) -> Try((List(Str) -> Wrapped), [InvalidInterpolation(Str)])
        \\    from_interpolation = |segments| Str.from_interpolation(segments).map_ok(|assemble| |values| Wrapped.{ text: assemble(values) })
        \\    size : Wrapped -> U64
        \\    size = |w| w.text.count_utf8_bytes()
        \\}
        \\
        \\measure : Wrapped, F32 -> F32
        \\measure = |w, f| if Wrapped.size(w) > 3 f else 0.0.F32
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| measure("x${input.uv.to_str()}y", input.uv)
    );
    defer staged.destroy();

    try staged.expectDump(
        \\row r0 ({ time : F32, uv : F32 }) -> F32
        \\  n0 = 3 : U64
        \\  n1 = field 1(p0) : F32
        \\  n2 = Num.F32.to_str(n1) : Str !spec
        \\  n3 = list(n2) : List(Str)
        \\  n4 = "x" : Str
        \\  n5 = tag Ok(n4) : [Err([ListWasEmpty]), Ok(Str)]
        \\  n6 = wrap(n5) : Builtin.Try
        \\  n7 = "" : Str
        \\  n8 = Try.ok_or(n6, n7) : Str !spec
        \\  n9 = "y" : Str
        \\  n10 = list(n4, n9) : List(Str)
        \\  n11 = closure r1(n10) : (Str, Str, U64 -> Str)
        \\  n12 = List.fold_with_index(n3, n8, n11) : Str !spec
        \\  n13 = Str.count_utf8_bytes(n12) : U64 !spec
        \\  n14 = Num.U64.is_lt(n0, n13) : Bool
        \\  n16 = switch n14 : F32
        \\    arm 0
        \\      n15 = float 0x0 : F32
        \\      value n15
        \\    arm 1
        \\      value n1
        \\  value n16
        \\row r1 (List(Str), Str, Str, U64) -> Str
        \\  n0 = 1 : U64
        \\  n1 = Num.U64.plus(p3, n0) : U64 !spec
        \\  n2 = List.get(p0, n1) : Builtin.Try
        \\  n3 = "" : Str
        \\  n4 = Try.ok_or(n2, n3) : Str !spec
        \\  n5 = Str.concat(p1, p2, n4) : Str
        \\  value n5
        \\
    );
}

test "an interpolated literal of a type whose conversion is in the cut is a Prim over its segments and values" {
    // N8h: the conversion and `size` are in the translator's cut, so the
    // literal is named by the type and `from_interpolation`.
    const written = try Staged.createTranslated(std.testing.allocator,
        \\wobble : { a : F32, b : F32 } -> F32
        \\wobble = |input| Lib.size("x${input.a.to_str()}y")
    , "_n = Lib.arity(wobble)",
        \\Lib := { text : Str }.{
        \\    from_interpolation : List(Str) -> Try((List(Str) -> Lib), [InvalidInterpolation(Str)])
        \\    from_interpolation = |segments| Str.from_interpolation(segments).map_ok(|assemble| |values| { text: assemble(values) })
        \\
        \\    size : Lib -> F32
        \\    size = |l| if l.text.is_empty() 0.0.F32 else 1.0.F32
        \\
        \\    code_primitives = (Lib.from_interpolation, Lib.size)
        \\
        \\    arity : Code(f) -> U64
        \\    arity = |code| code.graph().root_row().params.len()
        \\}
    );
    defer written.destroy();
    try written.expectDump(
        \\row r0 ({ a : F32, b : F32 }) -> F32
        \\  n0 = "x" : Str
        \\  n1 = "y" : Str
        \\  n2 = list(n0, n1) : List(Str)
        \\  n3 = field 0(p0) : F32
        \\  n4 = Num.F32.to_str(n3) : Str !spec
        \\  n5 = list(n4) : List(Str)
        \\  n6 = Lib.from_interpolation(n2, n5) : Lib !spec
        \\  n7 = Lib.size(n6) : F32 !spec
        \\  value n7
        \\
    );
}

/// A package whose type `Lib` converts interpolated literals by wrapping the
/// assembler of `Str`, and is a translator, `Lib.arity`, with `cut`.
fn interpolatingLib(comptime cut: []const u8) []const u8 {
    return
    \\Lib := { text : Str }.{
    \\    from_interpolation : List(Str) -> Try((List(Str) -> Lib), [InvalidInterpolation(Str)])
    \\    from_interpolation = |segments| Str.from_interpolation(segments).map_ok(|assemble| |values| { text: assemble(values) })
    \\
    \\    size : Lib -> F32
    \\    size = |l| if l.text.is_empty() 0.0.F32 else 1.0.F32
    \\
    ++ "    code_primitives = " ++ cut ++ "\n\n" ++
        \\    arity : Code(f) -> U64
        \\    arity = |code| code.graph().root_row().params.len()
        \\}
    ;
}

test "M13: an interpolated literal of another package's type whose conversion is outside the cut is walked by its definition" {
    // N8l: the cut names `size` only, so `from_interpolation` is walked as
    // the site's own type's is, and the literal is the fold of `Str`.
    const staged = try Staged.createTranslated(std.testing.allocator,
        \\wobble : { a : F32, b : F32 } -> F32
        \\wobble = |input| Lib.size("x${input.a.to_str()}y")
    , "_n = Lib.arity(wobble)", interpolatingLib("(Lib.size)"));
    defer staged.destroy();
    try staged.expectDump(
        \\row r0 ({ a : F32, b : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  n1 = Num.F32.to_str(n0) : Str !spec
        \\  n2 = list(n1) : List(Str)
        \\  n3 = "x" : Str
        \\  n4 = tag Ok(n3) : [Err([ListWasEmpty]), Ok(Str)]
        \\  n5 = wrap(n4) : Builtin.Try
        \\  n6 = "" : Str
        \\  n7 = Try.ok_or(n5, n6) : Str !spec
        \\  n8 = "y" : Str
        \\  n9 = list(n3, n8) : List(Str)
        \\  n10 = closure r1(n9) : (Str, Str, U64 -> Str)
        \\  n11 = List.fold_with_index(n2, n7, n10) : Str !spec
        \\  n12 = record(n11) : { text : Str }
        \\  n13 = wrap(n12) : Lib
        \\  n14 = Lib.size(n13) : F32 !spec
        \\  value n14
        \\row r1 (List(Str), Str, Str, U64) -> Str
        \\  n0 = 1 : U64
        \\  n1 = Num.U64.plus(p3, n0) : U64 !spec
        \\  n2 = List.get(p0, n1) : Builtin.Try
        \\  n3 = "" : Str
        \\  n4 = Try.ok_or(n2, n3) : Str !spec
        \\  n5 = Str.concat(p1, p2, n4) : Str
        \\  value n5
        \\
    );
}

/// The site's own module: a type `Label` that converts interpolated literals,
/// and a translator `Tr.arity` with `cut`, called on `wobble`.
fn ownInterpolationSource(comptime cut: []const u8) []const u8 {
    return
    \\Label := { text : Str }.{
    \\    from_interpolation : List(Str) -> Try((List(Str) -> Label), [InvalidInterpolation(Str)])
    \\    from_interpolation = |segments| Str.from_interpolation(segments).map_ok(|assemble| |values| { text: assemble(values) })
    \\
    \\    size : Label -> F32
    \\    size = |l| if l.text.is_empty() 0.0.F32 else 1.0.F32
    \\}
    \\
    \\Tr := {}.{
    \\
    ++ "    code_primitives = " ++ cut ++ "\n\n" ++
        \\    arity : Code(f) -> U64
        \\    arity = |code| code.graph().root_row().params.len()
        \\}
        \\
        \\wobble : { a : F32, b : F32 } -> F32
        \\wobble = |input| Label.size("x${input.a.to_str()}${input.b.to_str()}y")
    ;
}

test "M13: an interpolated literal of a type in the site's own module is a Prim in the cut and walked outside it" {
    // N8h and N8l: the cut of a translator in the site's module decides as
    // a dependency's does. In the cut, the conversion is one `Prim` over the
    // segments and the values, each list in source order.
    const gpa = std.testing.allocator;
    const cut = try Staged.createTranslated(gpa, ownInterpolationSource("(Label.from_interpolation, Label.size)"), "_n = Tr.arity(wobble)", null);
    defer cut.destroy();
    try cut.expectDump(
        \\row r0 ({ a : F32, b : F32 }) -> F32
        \\  n0 = "x" : Str
        \\  n1 = "" : Str
        \\  n2 = "y" : Str
        \\  n3 = list(n0, n1, n2) : List(Str)
        \\  n4 = field 0(p0) : F32
        \\  n5 = Num.F32.to_str(n4) : Str !spec
        \\  n6 = field 1(p0) : F32
        \\  n7 = Num.F32.to_str(n6) : Str !spec
        \\  n8 = list(n5, n7) : List(Str)
        \\  n9 = Label.from_interpolation(n3, n8) : Label !spec
        \\  n10 = Label.size(n9) : F32 !spec
        \\  value n10
        \\
    );
    const walked = try Staged.createTranslated(gpa, ownInterpolationSource("(Label.size)"), "_n = Tr.arity(wobble)", null);
    defer walked.destroy();
    try walked.expectDump(
        \\row r0 ({ a : F32, b : F32 }) -> F32
        \\  n0 = field 0(p0) : F32
        \\  n1 = Num.F32.to_str(n0) : Str !spec
        \\  n2 = field 1(p0) : F32
        \\  n3 = Num.F32.to_str(n2) : Str !spec
        \\  n4 = list(n1, n3) : List(Str)
        \\  n5 = "x" : Str
        \\  n6 = tag Ok(n5) : [Err([ListWasEmpty]), Ok(Str)]
        \\  n7 = wrap(n6) : Builtin.Try
        \\  n8 = "" : Str
        \\  n9 = Try.ok_or(n7, n8) : Str !spec
        \\  n10 = "y" : Str
        \\  n11 = list(n5, n8, n10) : List(Str)
        \\  n12 = closure r1(n11) : (Str, Str, U64 -> Str)
        \\  n13 = List.fold_with_index(n4, n9, n12) : Str !spec
        \\  n14 = record(n13) : { text : Str }
        \\  n15 = wrap(n14) : Label
        \\  n16 = Label.size(n15) : F32 !spec
        \\  value n16
        \\row r1 (List(Str), Str, Str, U64) -> Str
        \\  n0 = 1 : U64
        \\  n1 = Num.U64.plus(p3, n0) : U64 !spec
        \\  n2 = List.get(p0, n1) : Builtin.Try
        \\  n3 = "" : Str
        \\  n4 = Try.ok_or(n2, n3) : Str !spec
        \\  n5 = Str.concat(p1, p2, n4) : Str
        \\  value n5
        \\
    );
}

test "an interpolated literal whose conversion can leave its body early is refused" {
    const staged = try Staged.create(std.testing.allocator,
        \\Early := { text : Str }.{
        \\    from_interpolation : List(Str) -> Try((List(Str) -> Early), [InvalidInterpolation(Str)])
        \\    from_interpolation = |segments| {
        \\        assemble = Str.from_interpolation(segments)?
        \\        Ok(|values| { text: assemble(values) })
        \\    }
        \\    width : Early, F32 -> F32
        \\    width = |e, f| if e.text.is_empty() 0.0.F32 else f
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| "a${input.uv.to_str()}b".Early.width(input.uv)
    );
    defer staged.destroy();

    try staged.expectRejected("a conversion that leaves its body early");
}

test "an interpolated literal whose conversion is generic in the item type of its assembler is refused" {
    // The lambda's own type holds a variable that nothing fixes: the checker
    // relates the item type to the values' types, which the lambda's type
    // does not see.
    const staged = try Staged.create(std.testing.allocator,
        \\Count := { n : U64 }.{
        \\    from_interpolation : List(Str) -> Try((List(item) -> Count), [InvalidInterpolation(Str)])
        \\    from_interpolation = |_segments| Ok(|values| { n: List.len(values) })
        \\    weigh : Count, F32 -> F32
        \\    weigh = |c, f| if c.n > 1 f else 0.0.F32
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| "a${input.uv.to_str()}b${input.time.to_str()}".Count.weigh(input.uv)
    );
    defer staged.destroy();

    try staged.expectRejected("a type variable");
}

// N13w: the `Err` of a literal's conversion is the crash of a rejected
// literal, which the compiler wrote, so a path to it computes no result and
// C2 lets it go. However the conversion spells the rejection, as an `if`, a
// `match`, a test in a helper or a chain of tests, the literal describes as
// the conversion that never rejects.

/// `Html` with `from_interpolation` defined as `body`, and `wobble` over one
/// literal of it.
fn htmlSource(comptime body: []const u8) []const u8 {
    return
        \\Html := [Html(Str)].{
        \\    from_interpolation : List(Str) -> Try((List(Str) -> Html), [InvalidInterpolation(Str)])
        \\    from_interpolation = |segments|
        \\
    ++ body ++
        \\
        \\    check : List(Str) -> Try({}, [InvalidInterpolation(Str)])
        \\    check = |segments| if segments.any(|segment| segment.contains("<script")) Err(InvalidInterpolation("no scripts")) else Ok({})
        \\    width : Html, F32 -> F32
        \\    width = |h, f| match h {
        \\        Html(text) => if text.is_empty() 0.0.F32 else f
        \\    }
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| "<p>${input.uv.to_str()}!</p>".Html.width(input.uv)
    ;
}

const html_accepts =
    \\        Str.from_interpolation(segments).map_ok(|assemble|
    \\            |values| Html(assemble(values.map(|value| value.replace_each("<", "&lt;")))))
;

test "L3 N13w: a rejection written as an `if` is the conversion that never rejects" {
    try expectSameNormalForm(htmlSource(
        \\        if segments.any(|segment| segment.contains("<script")) {
        \\            Err(InvalidInterpolation("no scripts"))
        \\        } else {
        \\
    ++ html_accepts ++
        \\
        \\        }
    ), htmlSource(html_accepts));
}

test "L3 N13w: a rejection written as a `match` is the conversion that never rejects" {
    try expectSameNormalForm(htmlSource(
        \\        match segments.find_first(|segment| segment.contains("<script")) {
        \\            Ok(_) => Err(InvalidInterpolation("no scripts"))
        \\            Err(NotFound) => {
        \\
    ++ html_accepts ++
        \\
        \\            }
        \\        }
    ), htmlSource(html_accepts));
}

test "L3 N13w: a rejection tested in a helper is the conversion that never rejects" {
    try expectSameNormalForm(htmlSource(
        \\        match Html.check(segments) {
        \\            Ok({}) => {
        \\
    ++ html_accepts ++
        \\
        \\            }
        \\            Err(e) => Err(e)
        \\        }
    ), htmlSource(html_accepts));
}

test "L3 N13w: a chain of rejections is the conversion that never rejects" {
    try expectSameNormalForm(htmlSource(
        \\        if segments.any(|segment| segment.contains("<script")) {
        \\            Err(InvalidInterpolation("no scripts"))
        \\        } else if segments.len() > 9 {
        \\            Err(InvalidInterpolation("too long"))
        \\        } else {
        \\
    ++ html_accepts ++
        \\
        \\        }
    ), htmlSource(html_accepts));
}

test "a crash the author wrote in a conversion is not a rejected literal" {
    // Only the crash of a rejected literal is the compiler's. The author's
    // `crash` stays where it was written (normal-form 1.1), with the test
    // that reaches it, so the first stage keeps its branch, and the function
    // its `Ok` holds is chosen at run time, which no node applies.
    const staged = try Staged.create(std.testing.allocator, htmlSource(
        \\        if segments.any(|segment| segment.contains("<script")) {
        \\            crash "no scripts"
        \\        } else {
        \\
    ++ html_accepts ++
        \\
        \\        }
    ));
    defer staged.destroy();

    try staged.expectRejected("a call to a function value that no simplification resolves");
}

// L3 M10: layer L (normal-form 3.16). The laws apply only at a site that
// opts in with `Code.Lawful(f)`, so each pair meets in the `lawful` view and
// stays apart in the `graph` view.

/// The two sources describe `wobble` to one dump in the `lawful` view and to
/// two dumps in the `graph` view.
fn expectSameLawfulOnly(left: []const u8, right: []const u8) (StagedError || error{ TestUnexpectedResult, TestExpectedEqual })!void {
    const gpa = std.testing.allocator;
    const a = try Staged.createRunning(gpa, left, "");
    defer a.destroy();
    const b = try Staged.createRunning(gpa, right, "");
    defer b.destroy();
    inline for (.{ a, b }) |side| switch (side.outcome) {
        .reified => {},
        .rejected => |rejection| {
            std.debug.print("reification rejected: {t} {s} at '{s}'\n", .{ rejection.kind, rejection.detail, side.env.getSource(rejection.region) });
            return error.TestUnexpectedResult;
        },
    };
    try expectSameView(a, b, .lawful);
    // Without the opt-in, no law applies.
    try std.testing.expect(!std.mem.eql(u8, a.dump.items, b.dump.items));
}

test "L3 M10: a loop that appends each mapped element is List.map" {
    try expectSameLawfulOnly(
        \\wobble : List(U64) -> List(U64)
        \\wobble = |input| {
        \\    var $out = []
        \\    for x in input {
        \\        $out = $out.append(x * 3 + 1)
        \\    }
        \\    $out
        \\}
    ,
        \\wobble : List(U64) -> List(U64)
        \\wobble = |input| input.map(|x| x * 3 + 1)
    );
}

test "L3 M10: a loop that appends each element under a test is List.keep_if" {
    try expectSameLawfulOnly(
        \\wobble : List(U64) -> List(U64)
        \\wobble = |input| {
        \\    var $out = []
        \\    for x in input {
        \\        if x > 3 {
        \\            $out = $out.append(x)
        \\        }
        \\    }
        \\    $out
        \\}
    ,
        \\wobble : List(U64) -> List(U64)
        \\wobble = |input| input.keep_if(|x| x > 3)
    );
}

test "L3 M10: a fold of a known function is the loop written by hand" {
    try expectSameLawfulOnly(
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $s = 0
        \\    for x in input {
        \\        $s = $s + x * 2
        \\    }
        \\    $s
        \\}
    ,
        \\wobble : List(U64) -> U64
        \\wobble = |input| input.fold(0, |s, x| s + x * 2)
    );
}

test "L3 M10: a fold whose function reads two fields of a captured record is the loop written by hand" {
    // The capture splits into its fields (N14a) when N16c calls the row, and
    // the row that takes them is renumbered with a switch on a parameter.
    try expectSameLawfulOnly(
        \\wobble : { b : U64, c : Bool, xs : List(U64) } -> U64
        \\wobble = |input| input.xs.fold(11, |s, _y| s + (if input.c 14 else input.b))
    ,
        \\wobble : { b : U64, c : Bool, xs : List(U64) } -> U64
        \\wobble = |input| {
        \\    var $s = 11
        \\    for _y in input.xs {
        \\        $s = $s + (if input.c 14 else input.b)
        \\    }
        \\    $s
        \\}
    );
}

test "L3 M10: a fold whose function has the body of a helper called twice is the loop written by hand" {
    // The lambda's row and the helper's row merge (N8g), so the row has
    // three callers; N16c inlines it at the loop all the same.
    const helper =
        \\add : U64, U64 -> U64
        \\add = |p, q| p + q
        \\
        \\
    ;
    try expectSameLawfulOnly(helper ++
        \\wobble : { a : U64, b : U64, xs : List(U64) } -> U64
        \\wobble = |input| input.xs.fold(0, |s, x| s + x) + add(input.a, 1) + add(input.b, 2)
    , helper ++
        \\wobble : { a : U64, b : U64, xs : List(U64) } -> U64
        \\wobble = |input| {
        \\    var $s = 0
        \\    for x in input.xs {
        \\        $s = $s + x
        \\    }
        \\    $s + add(input.a, 1) + add(input.b, 2)
        \\}
    );
}

test "L3 M10: a map of a map is one map" {
    try expectSameLawfulOnly(
        \\wobble : List(U64) -> List(U64)
        \\wobble = |input| input.map(|x| x + 1).map(|y| y * 3)
    ,
        \\wobble : List(U64) -> List(U64)
        \\wobble = |input| input.map(|x| (x + 1) * 3)
    );
}

test "L3 M10: a length above 0 is not is_empty" {
    try expectSameLawfulOnly(
        \\wobble : List(U64) -> Bool
        \\wobble = |input| input.len() > 0
    ,
        \\wobble : List(U64) -> Bool
        \\wobble = |input| !input.is_empty()
    );
}

test "L3 M10: a length equal to 0 is is_empty" {
    try expectSameLawfulOnly(
        \\wobble : List(U64) -> Bool
        \\wobble = |input| 0 == input.len()
    ,
        \\wobble : List(U64) -> Bool
        \\wobble = |input| input.is_empty()
    );
}

test "L3 M10: an `if` on a length not equal to 0 is an `if` on not is_empty" {
    // The `if` makes the comparison a literal switch on the length (N13n),
    // which N16f makes a switch on `List.is_empty`.
    try expectSameLawfulOnly(
        \\wobble : { a : U64, b : U64, xs : List(U64) } -> U64
        \\wobble = |input| if input.xs.len() != 0 input.b else input.a
    ,
        \\wobble : { a : U64, b : U64, xs : List(U64) } -> U64
        \\wobble = |input| if !input.xs.is_empty() input.b else input.a
    );
}

test "L3 M10: a loop whose body reads the index stays a loop" {
    // `map` gives the function no index (N16a), so the two stay apart.
    const gpa = std.testing.allocator;
    const a = try Staged.createRunning(gpa,
        \\wobble : List(U64) -> List(U64)
        \\wobble = |input| {
        \\    var $out = []
        \\    var $i = 0
        \\    for x in input {
        \\        $out = $out.append(x + $i)
        \\        $i = $i + 1
        \\    }
        \\    $out
        \\}
    , "");
    defer a.destroy();
    const lawful = try a.viewDump(.lawful) orelse return error.TestUnexpectedResult;
    defer gpa.free(lawful);
    try std.testing.expect(std.mem.find(u8, lawful, "List.map") == null);
}

// The N5d gap of M10 (fuzz seed 0x1010): an equal literal that two sibling
// regions read is one node where it was built before the switch, and one
// node per arm where an inlined helper built it. Since M12 the number stage
// runs N5c over what the hoist brings into the arms, so both are one node.

const triple_helpers =
    \\triple : U64, U64, List(U64) -> U64
    \\triple = |k, b, xs| {
    \\    var $t = k
    \\    for _z in xs {
    \\        $t = $t + b * 3
    \\    }
    \\    $t
    \\}
    \\
;

test "L3 M12: a literal two arms read is one node, whether written before the switch or by an inlined helper" {
    try expectSameNormalForm(triple_helpers ++
        \\wobble : { a : U64, b : U64, c : Bool, xs : List(U64) } -> U64
        \\wobble = |input| if input.c input.a * 3 else {
        \\    k = 12.U64 * 3
        \\    var $t = k
        \\    for _z in input.xs {
        \\        $t = $t + input.b * 3
        \\    }
        \\    $t
        \\}
    , triple_helpers ++
        \\wobble : { a : U64, b : U64, c : Bool, xs : List(U64) } -> U64
        \\wobble = |input| if input.c input.a * 3 else {
        \\    k = 12.U64 * 3
        \\    triple(k, input.b, input.xs)
        \\}
    );
}

test "L3 M10: two helpers that differ only in where they share a literal merge into one row" {
    // Both helpers have one value but share the literal 3 differently until
    // N5d, so their numberings do not pair position by position. They merge
    // by the pairs the row comparison found (N8g, N10); pairing by position
    // crashed the compiler (M10 fuzz seed 0x1010, case 4).
    const staged = try Staged.createRunning(std.testing.allocator, triple_helpers ++
        \\inlined : Bool, U64, U64, List(U64) -> U64
        \\inlined = |c, a, b, xs| if c a * 3 else {
        \\    k = 12.U64 * 3
        \\    triple(k, b, xs)
        \\}
        \\
        \\written : Bool, U64, U64, List(U64) -> U64
        \\written = |c, a, b, xs| if c a * 3 else {
        \\    k = 12.U64 * 3
        \\    var $t = k
        \\    for _z in xs {
        \\        $t = $t + b * 3
        \\    }
        \\    $t
        \\}
        \\
        \\wobble : { a : U64, b : U64, c : Bool, xs : List(U64) } -> U64
        \\wobble = |input| inlined(input.c, input.a, input.b, input.xs) + inlined(input.c, input.b, input.a, input.xs) + written(input.c, input.a, input.b, input.xs) + written(input.c, input.b, input.a, input.xs)
    , "");
    defer staged.destroy();
    try std.testing.expect(staged.outcome == .reified);
    try std.testing.expect(std.mem.indexOf(u8, staged.dump.items, "row r1") != null);
    try std.testing.expect(std.mem.indexOf(u8, staged.dump.items, "row r2") == null);
}

// A loop that can return and that nothing reads decides the row's value, so
// the digest and the structural comparison read it (N8g, N7).

const find_looped =
    \\looped : List(U64), U64 -> U64
    \\looped = |xs, k| {
    \\    for x in xs {
    \\        if x == k {
    \\            return x
    \\        }
    \\    }
    \\    xs.len() + k
    \\}
    \\
;

test "L3 N8g: two helpers alike with a loop that can return and that nothing reads are one row" {
    const staged = try Staged.createRunning(std.testing.allocator, find_looped ++
        \\again : List(U64), U64 -> U64
        \\again = |xs, k| {
        \\    for x in xs {
        \\        if x == k {
        \\            return x
        \\        }
        \\    }
        \\    xs.len() + k
        \\}
        \\
        \\wobble : { xs : List(U64), k : U64 } -> U64
        \\wobble = |input| looped(input.xs, input.k) * again(input.xs, input.k)
    , "");
    defer staged.destroy();
    try std.testing.expect(staged.outcome == .reified);
    try std.testing.expect(std.mem.indexOf(u8, staged.dump.items, "row r1") != null);
    try std.testing.expect(std.mem.indexOf(u8, staged.dump.items, "row r2") == null);
}

test "L3 N8g: a helper with a loop that can return stays apart from one without it, in either call order" {
    for ([_][]const u8{
        \\wobble : { xs : List(U64), k : U64 } -> U64
        \\wobble = |input| looped(input.xs, input.k) * plain(input.xs, input.k)
        ,
        \\wobble : { xs : List(U64), k : U64 } -> U64
        \\wobble = |input| plain(input.xs, input.k) * looped(input.xs, input.k)
    }) |site| {
        const source = try std.mem.concat(std.testing.allocator, u8, &.{ find_looped,
            \\plain : List(U64), U64 -> U64
            \\plain = |xs, k| xs.len() + k
            \\
            \\
        , site });
        defer std.testing.allocator.free(source);
        const staged = try Staged.createRunning(std.testing.allocator, source, "");
        defer staged.destroy();
        try std.testing.expect(staged.outcome == .reified);
        // `plain` is inlined into the root and `looped` is the one helper;
        // a merge of the two made the root call `looped` twice.
        const dump = staged.dump.items;
        const helper = std.mem.indexOf(u8, dump, "row r1") orelse return error.TestUnexpectedResult;
        try std.testing.expect(std.mem.indexOf(u8, dump, "row r2") == null);
        try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, dump, "call r1"));
        try std.testing.expect(std.mem.indexOf(u8, dump[0..helper], "List.len") != null);
        try std.testing.expect(std.mem.indexOf(u8, dump[helper..], "for_list") != null);
        try std.testing.expect(std.mem.indexOf(u8, dump[helper..], "return") != null);
    }
}

test "L3 N7: an if whose arms differ only in a loop that can return keeps the loop and its return" {
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : { xs : List(U64), k : U64, c : Bool } -> U64
        \\wobble = |input| if input.c {
        \\    for x in input.xs {
        \\        if x == input.k {
        \\            return x
        \\        }
        \\    }
        \\    input.k
        \\} else {
        \\    input.k
        \\}
    , "");
    defer staged.destroy();
    try std.testing.expect(staged.outcome == .reified);
    try std.testing.expect(std.mem.indexOf(u8, staged.dump.items, "for_list") != null);
    try std.testing.expect(std.mem.indexOf(u8, staged.dump.items, "return") != null);
}

// M11: literal intervals (N13u, N8k) and the parameter half of N15c.

test "L3 M11: `while $i <= n` with `n` bounded is the `for` over `0..=n`" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| if input < 100 {
        \\    var $i = 0
        \\    var $total = 0
        \\    while $i <= input {
        \\        $total = $total + $i
        \\        $i = $i + 1
        \\    }
        \\    $total
        \\} else 0
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| if input < 100 {
        \\    var $total = 0
        \\    for i in 0..=input {
        \\        $total = $total + i
        \\    }
        \\    $total
        \\} else 0
    );
}

test "L3 M11: `while $i <= n` with `n` unbounded stays apart from the `for` over `0..=n`" {
    try expectOtherNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $i = 0
        \\    var $total = 0
        \\    while $i <= input {
        \\        $total = $total + $i
        \\        $i = $i + 1
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for i in 0..=input {
        \\        $total = $total + i
        \\    }
        \\    $total
        \\}
    );
}

test "L3 M11: `a + 1` is `1 + a`, and so on for `*` and `==` with a literal" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| input + 1
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| 1 + input
    );
    try expectSameNormalForm(
        \\wobble : U64 -> Bool
        \\wobble = |input| input * 3 == 6
    ,
        \\wobble : U64 -> Bool
        \\wobble = |input| 6 == 3 * input
    );
}

test "L3 M11: two root parameters swapped in `+`, `*` and `==` are one normal form, over integers and Str" {
    try expectSameNormalForm(
        \\wobble : U64, U64 -> U64
        \\wobble = |input, other| (input + other) * (input * other)
    ,
        \\wobble : U64, U64 -> U64
        \\wobble = |input, other| (other + input) * (other * input)
    );
    try expectSameNormalForm(
        \\wobble : U64, U64 -> Bool
        \\wobble = |input, other| input == other
    ,
        \\wobble : U64, U64 -> Bool
        \\wobble = |input, other| other == input
    );
    try expectSameNormalForm(
        \\wobble : Str, Str -> Bool
        \\wobble = |input, other| input == other
    ,
        \\wobble : Str, Str -> Bool
        \\wobble = |input, other| other == input
    );
    // `-` is not commutative.
    try expectOtherNormalForm(
        \\wobble : U64, U64 -> U64
        \\wobble = |input, other| input - other
    ,
        \\wobble : U64, U64 -> U64
        \\wobble = |input, other| other - input
    );
}

test "L3 M11: a helper with its parameters reordered still meets itself" {
    try expectSameNormalForm(
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |input| {
        \\    h = |a, b| a * 2 + b
        \\    h(input.x, input.y) * h(input.y, input.x)
        \\}
    ,
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |input| {
        \\    h = |b, a| a * 2 + b
        \\    h(input.y, input.x) * h(input.x, input.y)
        \\}
    );
}

test "L3 M11: matches on two root parameters in either test order are one decision tree" {
    try expectSameNormalForm(
        \\wobble : [P, Q], [A, B] -> U64
        \\wobble = |input, other| match input {
        \\    P => match other { A => 1, B => 2 }
        \\    Q => match other { A => 3, B => 4 }
        \\}
    ,
        \\wobble : [P, Q], [A, B] -> U64
        \\wobble = |input, other| match other {
        \\    A => match input { P => 1, Q => 3 }
        \\    B => match input { P => 2, Q => 4 }
        \\}
    );
}

test "L3 M11: a test that an enclosing test decides is gone" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| if input < 10 {
        \\    if input < 20 input + 1 else 7
        \\} else 3
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| if input < 10 input + 1 else 3
    );
}

test "L3 M11: a `plus` chain whose operands a test bounds is one sum in either grouping" {
    try expectSameNormalForm(
        \\wobble : { a : U64, b : U64, c : U64 } -> U64
        \\wobble = |input| if input.a < 100 and input.b < 100 and input.c < 100 {
        \\    (input.a + input.b) + input.c
        \\} else 0
    ,
        \\wobble : { a : U64, b : U64, c : U64 } -> U64
        \\wobble = |input| if input.a < 100 and input.b < 100 and input.c < 100 {
        \\    input.a + (input.b + input.c)
        \\} else 0
    );
    // Unbounded, regrouping can overflow where the written sum does not.
    try expectOtherNormalForm(
        \\wobble : { a : U64, b : U64, c : U64 } -> U64
        \\wobble = |input| (input.a + input.b) + input.c
    ,
        \\wobble : { a : U64, b : U64, c : U64 } -> U64
        \\wobble = |input| input.a + (input.b + input.c)
    );
}

test "L3 M11: a comparison of a helper's call that its result range decides is gone (N8k)" {
    try expectSameNormalForm(
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| {
        \\    h = |v| v * 2 + 1
        \\    if h(input.a) > 0 h(input.a) * h(input.b) else 7
        \\}
    ,
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| {
        \\    h = |v| v * 2 + 1
        \\    h(input.a) * h(input.b)
        \\}
    );
}

test "L3 M11: an interval a test gives a node holds only inside that test, in either build order and in a sibling arm" {
    // Built in the arm first, then outside: outside, `input + 1 > 100` can hold.
    try expectOtherNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| (if input < 10 { input + 1 } else { 0 }) + (if input + 1 > 100 { 1 } else { 2 })
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| (if input < 10 { input + 1 } else { 0 }) + 2
    );
    // Built outside first, then in the arm.
    try expectOtherNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| (if input + 1 > 100 { 1 } else { 2 }) + (if input < 10 { input + 1 } else { 0 })
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| 2 + (if input < 10 { input + 1 } else { 0 })
    );
    // In the sibling arm `input + 1` is at least 11, which decides `< 11` and not `< 50`.
    try expectOtherNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| if input < 10 { input + 1 } else if input + 1 < 50 { 1 } else { 2 }
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| if input < 10 { input + 1 } else { 1 }
    );
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| if input < 10 { input + 1 } else if input + 1 < 11 { 1 } else { 2 }
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| if input < 10 { input + 1 } else { 2 }
    );
}

test "L3 M11: a helper's result range is the union over all its results, not the interval of one returned under a test (N8k)" {
    try expectOtherNormalForm(
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| {
        \\    h = |v| {
        \\        if v < 10 {
        \\            return v + 1
        \\        }
        \\        v
        \\    }
        \\    if h(input.a) > 100 h(input.b) else 7
        \\}
    ,
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| 7
    );
}

test "L4 and L5 M11: literal operands on either side and bounded inclusive sums keep every seed's two prints one normal form" {
    // The generator's M11 choices are on: a literal operand of `+`, `*` and
    // `==` first or last, and a sum over `0..=n` under a test that bounds
    // `n`, written as a `for` or a `while $i <= n`. The harness checks that
    // every interval holds every value the normal form computes (L2).
    var prng = std.Random.DefaultPrng.init(0x0b11);
    const random = prng.random();
    var bytes: [96]u8 = undefined;
    var verdicts = std.EnumArray(reify_fuzz.Verdict, u32).initFill(0);
    for (0..300) |_| {
        random.bytes(&bytes);
        var tmp = std.testing.tmpDir(.{});
        defer tmp.cleanup();
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const ctx = CoreCtx.default(std.testing.allocator, arena.allocator(), std.testing.io);
        verdicts.getPtr(try reify_fuzz.runCaseWith(ctx, try sharedBuiltinModules(), tmp.dir, &bytes, .{ .m7 = false, .m11 = true })).* += 1;
    }
    try std.testing.expect(verdicts.get(.agree) > 0 and verdicts.get(.reference_crashed) > 0);
}

// M12: facts across loop turns (N11n, N11o).

test "L3 M12: a `$done` flag set where the `break` would be is the loop with `break`" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $i = 0
        \\    var $total = 0
        \\    var $done = Bool.False
        \\    while !$done {
        \\        if $i >= input {
        \\            $done = Bool.True
        \\        } else {
        \\            $total = $total + $i
        \\            $i = $i + 1
        \\        }
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $i = 0
        \\    var $total = 0
        \\    while Bool.True {
        \\        if $i >= input {
        \\            break
        \\        }
        \\        $total = $total + $i
        \\        $i = $i + 1
        \\    }
        \\    $total
        \\}
    );
}

test "L3 M12: a search that sets a `$done` flag in two places is the search with two `break`s" {
    try expectSameNormalForm(
        \\wobble : { xs : List(U64), k : U64 } -> U64
        \\wobble = |input| {
        \\    var $i = 0
        \\    var $found = 0
        \\    var $done = Bool.False
        \\    while !$done {
        \\        if $i < input.xs.len() {
        \\            x = input.xs.get($i) ?? 0
        \\            if x == input.k {
        \\                $found = x + 1
        \\                $done = Bool.True
        \\            } else {
        \\                $i = $i + 1
        \\            }
        \\        } else {
        \\            $done = Bool.True
        \\        }
        \\    }
        \\    $found
        \\}
    ,
        \\wobble : { xs : List(U64), k : U64 } -> U64
        \\wobble = |input| {
        \\    var $i = 0
        \\    var $found = 0
        \\    while $i < input.xs.len() {
        \\        x = input.xs.get($i) ?? 0
        \\        if x == input.k {
        \\            $found = x + 1
        \\            break
        \\        }
        \\        $i = $i + 1
        \\    }
        \\    $found
        \\}
    );
}

test "L3 M12: a `$done` flag that a computed value sets stays a general loop" {
    try expectOtherNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $i = 0
        \\    var $total = 0
        \\    var $done = Bool.False
        \\    while !$done {
        \\        $total = $total + $i
        \\        $i = $i + 1
        \\        $done = $i >= input
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $i = 0
        \\    var $total = 0
        \\    while Bool.True {
        \\        $total = $total + $i
        \\        $i = $i + 1
        \\        if $i >= input {
        \\            break
        \\        }
        \\    }
        \\    $total
        \\}
    );
}

test "L3 M12: a second counter from a range's start that N13u proves below its own is the index plus the difference" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    var $j = 10
        \\    for i in 3..<input {
        \\        $total = $total + $j
        \\        $j = $j + 1
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for i in 3..<input {
        \\        $total = $total + (i + 7)
        \\    }
        \\    $total
        \\}
    );
}

test "L3 M12: a second counter whose difference N13u does not prove stays a slot" {
    // `0 - input` fits a `U64` only where `input` is 0.
    try expectOtherNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    var $j = 0
        \\    for i in input..<20 {
        \\        $total = $total + $j
        \\        $j = $j + 1
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for i in input..<20 {
        \\        $total = $total + (i - input)
        \\    }
        \\    $total
        \\}
    );
}

test "L3 M12: a second counter stepped by 2 stays a slot" {
    try expectOtherNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    var $j = 5
        \\    for i in 0..<input {
        \\        $total = $total + $j
        \\        $j = $j + 2
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for i in 0..<input {
        \\        $total = $total + (i * 2 + 5)
        \\    }
        \\    $total
        \\}
    );
}

test "L3 M12: a second counter read after the loop stays a slot" {
    try expectOtherNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    var $j = 5
        \\    for i in 0..<input {
        \\        $total = $total + $j
        \\        $j = $j + 1
        \\    }
        \\    $total + $j
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    for i in 0..<input {
        \\        $total = $total + (i + 5)
        \\    }
        \\    $total + (input + 5)
        \\}
    );
}

test "L3 M12: a second counter over a list's indices is the index plus its start, in either loop" {
    try expectSameNormalForm(
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    var $j = 1
        \\    for x in input {
        \\        $total = $total + x * $j
        \\        $j = $j + 1
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : List(U64) -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    var $j = 1
        \\    for i in 0..<input.len() {
        \\        x = input.get(i) ?? 0
        \\        $total = $total + x * $j
        \\        $j = $j + 1
        \\    }
        \\    $total
        \\}
    );
}

test "L4 and L5 M12: `$done` flag loops and derived counters keep every seed's two prints one normal form" {
    // The generator's M12 choices are on: a sum over `0..<n` under a test
    // that bounds `n`, written as a `for`, a `while $i < n` or a `while
    // !$done`, with a second counter as a stepped `var` or as `i + j0`.
    // Case 278 of this seed meets a gap of placement that is not M12's: a
    // literal that hash-consing merged into one node through a node a later
    // round removed stays one node read from two arms (normal-form 3.5).
    var prng = std.Random.DefaultPrng.init(0x0b12);
    const random = prng.random();
    var bytes: [96]u8 = undefined;
    var verdicts = std.EnumArray(reify_fuzz.Verdict, u32).initFill(0);
    for (0..250) |_| {
        random.bytes(&bytes);
        var tmp = std.testing.tmpDir(.{});
        defer tmp.cleanup();
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const ctx = CoreCtx.default(std.testing.allocator, arena.allocator(), std.testing.io);
        verdicts.getPtr(try reify_fuzz.runCaseWith(ctx, try sharedBuiltinModules(), tmp.dir, &bytes, .{ .m7 = false, .m12 = true })).* += 1;
    }
    try std.testing.expect(verdicts.get(.agree) > 0 and verdicts.get(.reference_crashed) > 0);
}

test "L4 and L5 M13: a helper in another package, outside every cut, keeps every seed's two prints one normal form" {
    // The generator's M7 helpers are on, and M13 puts each one, per print,
    // in the app or in a module `Lib` of another package. No cut lists it,
    // so its body is walked wherever it lives (N8l).
    var prng = std.Random.DefaultPrng.init(0x0d13);
    const random = prng.random();
    var bytes: [96]u8 = undefined;
    var verdicts = std.EnumArray(reify_fuzz.Verdict, u32).initFill(0);
    for (0..200) |_| {
        random.bytes(&bytes);
        var tmp = std.testing.tmpDir(.{});
        defer tmp.cleanup();
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const ctx = CoreCtx.default(std.testing.allocator, arena.allocator(), std.testing.io);
        verdicts.getPtr(try reify_fuzz.runCaseWith(ctx, try sharedBuiltinModules(), tmp.dir, &bytes, .{ .m13 = true })).* += 1;
    }
    try std.testing.expect(verdicts.get(.agree) > 0 and verdicts.get(.reference_crashed) > 0);
}

test "L4 and L5 M17: builtins and loops over literal lists keep every seed's two prints one normal form" {
    // The generator's M17 choices are on: a builtin over a literal list as
    // the call or as its result (N17a, N17b, N17f), and a `for` over a
    // literal list as the loop or as its statements written out (N17g).
    var prng = std.Random.DefaultPrng.init(0x0e17);
    const random = prng.random();
    var bytes: [96]u8 = undefined;
    var verdicts = std.EnumArray(reify_fuzz.Verdict, u32).initFill(0);
    for (0..250) |_| {
        random.bytes(&bytes);
        var tmp = std.testing.tmpDir(.{});
        defer tmp.cleanup();
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const ctx = CoreCtx.default(std.testing.allocator, arena.allocator(), std.testing.io);
        verdicts.getPtr(try reify_fuzz.runCaseWith(ctx, try sharedBuiltinModules(), tmp.dir, &bytes, .{ .m7 = false, .m17 = true })).* += 1;
    }
    try std.testing.expect(verdicts.get(.agree) > 0 and verdicts.get(.reference_crashed) > 0);
}

test "L3 M12: a counter `while` with a second slot only its body reads is the `for` over the range (N11l)" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $i = 0
        \\    var $total = 0
        \\    var $j = 3
        \\    while $i < input {
        \\        $total = $total + $j * $i
        \\        $j = $j * 2
        \\        $i = $i + 1
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $total = 0
        \\    var $j = 3
        \\    for i in 0..<input {
        \\        $total = $total + $j * i
        \\        $j = $j * 2
        \\    }
        \\    $total
        \\}
    );
}

test "L3 M12: a literal written in a loop of one arm and before it merges alike with the other arm's (N5c after the hoist)" {
    try expectSameNormalForm(
        \\wobble : { c : Bool, n : U64 } -> U64
        \\wobble = |input| if input.c input.n * 7 else {
        \\    var $total = 0
        \\    for i in 0..<input.n {
        \\        $total = $total + i + 7
        \\    }
        \\    $total
        \\}
    ,
        \\wobble : { c : Bool, n : U64 } -> U64
        \\wobble = |input| if input.c input.n * 7 else {
        \\    k = 7
        \\    var $total = 0
        \\    for i in 0..<input.n {
        \\        $total = $total + i + k
        \\    }
        \\    $total
        \\}
    );
}

// M14: the safety matrix (`roc-reify-normalization-plan.md` 5.12). One L3
// pair per row of `roc-reify-refactor-safety.md` 4.1, per row of its
// section 2 that R absorbs, and per row of its section 5. A row an earlier
// milestone pinned keeps that test, and 5.12 names it.

test "L3 M14: rename a local or a parameter meets (N2)" {
    // The site's own parameter, a local and a helper's parameter, renamed.
    const gpa = std.testing.allocator;
    const written = try Staged.createNamed(gpa,
        \\grow : U64 -> U64
        \\grow = |k| k * 3 + 1
        \\
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |input| {
        \\    wave = grow(input.x)
        \\    wave * input.y
        \\}
    , "", "input");
    defer written.destroy();
    const renamed = try Staged.createNamed(gpa,
        \\grow : U64 -> U64
        \\grow = |seed| seed * 3 + 1
        \\
        \\wobble : { x : U64, y : U64 } -> U64
        \\wobble = |args| {
        \\    ripple = grow(args.x)
        \\    ripple * args.y
        \\}
    , "", "args");
    defer renamed.destroy();
    if (written.outcome != .reified or renamed.outcome != .reified) return error.TestUnexpectedResult;
    try std.testing.expectEqualStrings(written.dump.items, renamed.dump.items);
}

test "L3 M14: extract or inline a helper with one use meets (N8d to N8g, V1)" {
    try expectSameNormalForm(
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| (input.a * 3 + input.b) * input.b
    ,
        \\mix : U64, U64 -> U64
        \\mix = |x, y| (x * 3 + y) * y
        \\
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| mix(input.a, input.b)
    );
}

test "L3 M14: extract or inline a helper with many uses meets in `inline` (V2)" {
    // In `graph` the helper with two calls stays a row (N8e), so only the
    // `inline` view of a `Code.Inlined(f)` site meets.
    const gpa = std.testing.allocator;
    const extracted = try Staged.createRunning(gpa,
        \\mix : U64, U64 -> U64
        \\mix = |x, y| (x * 3 + y) * y
        \\
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| mix(input.a, input.b) + mix(input.b, input.a)
    , "");
    defer extracted.destroy();
    const written = try Staged.createRunning(gpa,
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| (input.a * 3 + input.b) * input.b + (input.b * 3 + input.a) * input.a
    , "");
    defer written.destroy();
    if (extracted.outcome != .reified or written.outcome != .reified) return error.TestUnexpectedResult;
    try std.testing.expect(!std.mem.eql(u8, extracted.dump.items, written.dump.items));
    try expectSameView(extracted, written, .inline_);
}

test "L3 M14: destructure or read fields meets (N1f)" {
    try expectSameNormalForm(
        \\wobble : { a : U64, c : U64 } -> U64
        \\wobble = |input| {
        \\    { a, c } = input
        \\    a * c + a
        \\}
    ,
        \\wobble : { a : U64, c : U64 } -> U64
        \\wobble = |input| input.a * input.c + input.a
    );
}

test "L3 M14: move code, reformat, comment meets (N10)" {
    // The helper moves from after the site to before it, the body is
    // reformatted, and comments are added.
    try expectSameNormalForm(
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| if input.a > input.b { step(input.a) } else { input.b }
        \\
        \\step : U64 -> U64
        \\step = |x| x * 2 + 1
    ,
        \\# The step every branch may take.
        \\step : U64 -> U64
        \\step = |x|
        \\    x * 2 # doubled
        \\    + 1
        \\
        \\
        \\
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input|
        \\    # Take the step only from the larger field.
        \\    if input.a > input.b {
        \\        step(input.a)
        \\    } else {
        \\        input.b
        \\    }
    );
}

test "L3 M14: add or remove a type annotation meets (types from the checker)" {
    try expectSameNormalForm(
        \\scale : U64, U64 -> U64
        \\scale = |v, k| v * k
        \\
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| {
        \\    p : U64
        \\    p = scale(input.a, input.b)
        \\    p + 1
        \\}
    ,
        \\scale = |v, k| v * k
        \\
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| {
        \\    p = scale(input.a, input.b)
        \\    p + 1
        \\}
    );
}

test "L3 M14: reorder unrelated top-level definitions meets (N8g, N9)" {
    // Two helpers with two calls each stay rows in `graph`, so their order
    // in the module could reach the row numbering.
    const call =
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| inc(input.a) * dbl(input.b) + inc(input.b) * dbl(input.a)
        \\
    ;
    const inc =
        \\inc : U64 -> U64
        \\inc = |x| x * x + 1
        \\
    ;
    const dbl =
        \\dbl : U64 -> U64
        \\dbl = |x| x * 2 + x
        \\
    ;
    try expectSameNormalForm(inc ++ "\n" ++ dbl ++ "\n" ++ call, call ++ "\n" ++ dbl ++ "\n" ++ inc);
    try expectRows(inc ++ "\n" ++ dbl ++ "\n" ++ call, 3);
}

test "L3 M14: reorder two calls to one generic function meets (N8d, N8g)" {
    // `count` is one generic function at two types, and each instantiation
    // has two calls, so each stays a row. The calls are made in the other
    // order on the right.
    const count =
        \\count : List(a) -> U64
        \\count = |xs| xs.len() * 2 + 1
        \\
        \\
    ;
    try expectSameNormalForm(count ++
        \\wobble : { xs : List(U64), ys : List(U64), ss : List(Str), ts : List(Str) } -> U64
        \\wobble = |input| {
        \\    n = count(input.xs) + count(input.ys)
        \\    m = count(input.ss) + count(input.ts)
        \\    n * m
        \\}
    , count ++
        \\wobble : { xs : List(U64), ys : List(U64), ss : List(Str), ts : List(Str) } -> U64
        \\wobble = |input| {
        \\    m = count(input.ss) + count(input.ts)
        \\    n = count(input.xs) + count(input.ys)
        \\    n * m
        \\}
    );
    try expectRows(count ++
        \\wobble : { xs : List(U64), ys : List(U64), ss : List(Str), ts : List(Str) } -> U64
        \\wobble = |input| count(input.xs) + count(input.ys) + count(input.ss) + count(input.ts)
    , 3);
}

/// `source`'s `wobble` describes as `count` rows, its root's included.
fn expectRows(source: []const u8, count: usize) !void {
    const staged = try Staged.createRunning(std.testing.allocator, source, "");
    defer staged.destroy();
    if (staged.outcome != .reified) return error.TestUnexpectedResult;
    try std.testing.expectEqual(count, std.mem.count(u8, staged.dump.items, "row r"));
}

test "L3 M14: `x * 2` or `x + x`, and `(a + b) + c` or `a + (b + c)`, stay apart (safety 5)" {
    // Integer `+` crashes on overflow, so neither is an equation of Roc.
    try expectOtherNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| input * 2
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| input + input
    );
    // No test bounds the operands, so N13u proves no sum fits (compare
    // "L3 M11: a `plus` chain whose operands a test bounds is one sum in
    // either grouping").
    try expectOtherNormalForm(
        \\wobble : { a : U64, b : U64, c : U64 } -> U64
        \\wobble = |input| (input.a + input.b) + input.c
    ,
        \\wobble : { a : U64, b : U64, c : U64 } -> U64
        \\wobble = |input| input.a + (input.b + input.c)
    );
}

test "L3 M14: a recursive function or a fold stays apart (safety 5)" {
    try expectOtherNormalForm(
        \\total : List(U64) -> U64
        \\total = |xs| match xs {
        \\    [x, .. as rest] => x + total(rest)
        \\    [] => 0
        \\}
        \\
        \\wobble : List(U64) -> U64
        \\wobble = |input| total(input)
    ,
        \\wobble : List(U64) -> U64
        \\wobble = |input| input.fold(0, |s, x| s + x)
    );
}

// M17: known lists (N17, normal-form 3.17). The three meeting pairs of 3.17,
// then the rows it keeps apart.

/// The fixture's site dump, which must hold `want` and not `unwanted`.
fn expectDumpHas(staged: *Staged, want: []const u8, unwanted: []const u8) !void {
    if (std.mem.find(u8, staged.dump.items, want) == null or (unwanted.len > 0 and std.mem.find(u8, staged.dump.items, unwanted) != null)) {
        std.debug.print("expected {s} and not {s} in:\n{s}\n", .{ want, unwanted, staged.dump.items });
        return error.TestUnexpectedResult;
    }
}

test "L3 M17: `map2` then `sum` over known lists is the written sum in `inline`, and a row called three times in `graph`" {
    const gpa = std.testing.allocator;
    const mapped = try Staged.createRunning(gpa,
        \\wobble : { r : F32, g : F32, b : F32 } -> F32
        \\wobble = |input| {
        \\    weights = [0.25.F32, 0.5, 0.125]
        \\    [input.r, input.g, input.b].map2(weights, |x, w| x * w).sum()
        \\}
    , "");
    defer mapped.destroy();
    const written = try Staged.createRunning(gpa,
        \\wobble : { r : F32, g : F32, b : F32 } -> F32
        \\wobble = |input| input.r * 0.25 + input.g * 0.5 + input.b * 0.125
    , "");
    defer written.destroy();
    if (mapped.outcome != .reified or written.outcome != .reified) return error.TestUnexpectedResult;
    try expectSameView(mapped, written, .inline_);
    // Tier B in `graph`: the lambda is one row, called once per element.
    try std.testing.expectEqual(@as(usize, 3), std.mem.count(u8, mapped.dump.items, "= call r"));
    try expectDumpHas(mapped, "Num.F32.plus(", "List.");
}

test "L3 M17: a `for` over a known list is the `fold` over it, three calls of the step" {
    try expectSameNormalForm(
        \\step : U64, U64 -> U64
        \\step = |s, x| s * 3 + x
        \\
        \\wobble : { a : U64, b : U64, c : U64 } -> U64
        \\wobble = |input| {
        \\    var $s = 1
        \\    for x in [input.a, input.b, input.c] {
        \\        $s = step($s, x)
        \\    }
        \\    $s
        \\}
    ,
        \\step : U64, U64 -> U64
        \\step = |s, x| s * 3 + x
        \\
        \\wobble : { a : U64, b : U64, c : U64 } -> U64
        \\wobble = |input| [input.a, input.b, input.c].fold(1, step)
    );
}

test "L3 M17: `[a, b].concat([c])` is the list `[a, b, c]`" {
    try expectSameNormalForm(
        \\wobble : { a : U64, b : U64, c : U64 } -> List(U64)
        \\wobble = |input| [input.a, input.b].concat([input.c])
    ,
        \\wobble : { a : U64, b : U64, c : U64 } -> List(U64)
        \\wobble = |input| [input.a, input.b, input.c]
    );
}

test "L3 M17: a lookup in a known list is a literal switch on the index, apart from the `match` on the month" {
    const gpa = std.testing.allocator;
    const looked_up = try Staged.createRunning(gpa,
        \\wobble : U64 -> U64
        \\wobble = |input| [31, 28, 31, 30].get(input - 1) ?? 31
    , "");
    defer looked_up.destroy();
    if (looked_up.outcome != .reified) return error.TestUnexpectedResult;
    try expectDumpHas(looked_up, "default", "List.get(");
    try expectOtherNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| [31, 28, 31, 30].get(input - 1) ?? 31
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| match input {
        \\    2 => 28
        \\    4 => 30
        \\    _ => 31
        \\}
    );
}

test "L3 M17: a list whose length depends on the input keeps its builtins" {
    const gpa = std.testing.allocator;
    inline for (.{
        \\wobble : List(U64) -> U64
        \\wobble = |input| input.len() + input.sum()
        ,
        \\wobble : { xs : List(U64), k : U64 } -> U64
        \\wobble = |input| [input.k, 1].concat(input.xs).len()
        ,
        \\wobble : { xs : List(U64), k : U64 } -> U64
        \\wobble = |input| [input.k, 5].keep_if(|x| x > 3).len()
    }, .{ "List.sum(", "List.len(", "List.keep_if(" }) |source, kept| {
        const staged = try Staged.createRunning(gpa, source, "");
        defer staged.destroy();
        if (staged.outcome != .reified) return error.TestUnexpectedResult;
        try expectDumpHas(staged, kept, "");
    }
}

test "L3 M17: a `keep_if` whose every predicate value is known is the kept list" {
    try expectSameNormalForm(
        \\wobble : U64 -> List(U64)
        \\wobble = |input| [1, 5, 2, 9].keep_if(|x| x > 3).concat([input])
    ,
        \\wobble : U64 -> List(U64)
        \\wobble = |input| [5, 9, input]
    );
}

test "L3 M17: an `Iter` pipeline over a known list keeps its `Iter` builtins" {
    const gpa = std.testing.allocator;
    const staged = try Staged.createRunning(gpa,
        \\wobble : U64 -> List(U64)
        \\wobble = |input| [input, 2, 3].iter().map(|x| x + 1).collect()
    , "");
    defer staged.destroy();
    if (staged.outcome != .reified) return error.TestUnexpectedResult;
    try expectDumpHas(staged, "Iter.", "");
}

test "L3 M17: a loop over a known list with a `break`, or longer than B, stays a `ForList`" {
    const gpa = std.testing.allocator;
    inline for (.{
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $s = 0
        \\    for x in [input, 7, 2] {
        \\        if x == 7 {
        \\            break
        \\        }
        \\        $s = $s + x
        \\    }
        \\    $s
        \\}
        ,
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $s = 0
        \\    for x in [input, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] {
        \\        $s = $s + x
        \\    }
        \\    $s
        \\}
    }) |source| {
        const staged = try Staged.createRunning(gpa, source, "");
        defer staged.destroy();
        if (staged.outcome != .reified) return error.TestUnexpectedResult;
        try expectDumpHas(staged, "for_list(", "");
    }
    // At B elements it is the sum written out.
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    var $s = 0
        \\    for x in [input, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] {
        \\        $s = $s + x
        \\    }
        \\    $s
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| 0 + input + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 + 13 + 14 + 15
    );
}

test "L3 M17: the builtins of a known list are their results" {
    try expectSameNormalForm(
        \\wobble : U64 -> U64
        \\wobble = |input| {
        \\    xs = [input, 2, 3]
        \\    n = xs.len()
        \\    first = xs.first() ?? 0
        \\    last = xs.last() ?? 0
        \\    n + first + last + (xs.append(4).get(3) ?? 0)
        \\}
    ,
        \\wobble : U64 -> U64
        \\wobble = |input| 3 + input + 3 + 4
    );
}

// One recursive type has one `TyId` (roc-reify-normal-form.md 2.1). A cycle
// through two nominals has a tree for each nominal it can be closed at, and
// these three sites compared two of those trees as two types.

/// `wobble` over `C`, a row whose optional field reaches `C` again through
/// the type `nick` is written as.
fn optionalReadOf(comptime nick: []const u8) []const u8 {
    return
    \\Wrap(a) := { items : List(a) }
    \\
    ++ "C := { name : Str, nick ?: " ++ nick ++ " }\n\n" ++
        \\wobble : C -> Bool
        \\wobble = |input| input.?nick.is_ok()
    ;
}

test "a `.?` read of a field that reaches its row again through a second nominal has the type of the whole path" {
    // The field's `Try` is built from the record's field type, and the path's
    // from the checker's type of the whole read. Both are one type, so they
    // are one `TyId`.
    const staged = try Staged.createRunning(std.testing.allocator, optionalReadOf("Wrap(C)"), "");
    defer staged.destroy();
    try staged.expectDump(
        \\row r0 (C) -> Bool
        \\  n0 = unwrap(p0) : { name : Str, nick ? Wrap }
        \\  n1 = opt_field(n0) : Builtin.Try
        \\  n2 = Try.is_ok(n1) : Bool !spec
        \\  value n2
        \\
    );
}

test "a `.?` read of a field that reaches its row without a second nominal, or not at all, reifies alike" {
    inline for (.{ "Wrap(Str)", "List(C)", "[Has(C), No]" }) |nick| {
        const staged = try Staged.createRunning(std.testing.allocator, optionalReadOf(nick), "");
        defer staged.destroy();
        if (staged.outcome != .reified) return error.TestUnexpectedResult;
    }
}

/// `wobble` comparing a `Link(Customer)` with one it builds, where
/// `Customer` holds `referrer`.
fn linkCompareOf(comptime referrer: []const u8) []const u8 {
    return
    \\Link(row) := { key : Str, row : List(row) }.{
    \\    is_eq : Link(row), Link(row) -> Bool
    \\    is_eq = |Link.(a), Link.(b)| a.key == b.key
    \\}
    \\
    \\link : Str -> Link(row)
    \\link = |key| Link.({ key, row: [] })
    \\
    ++ "Customer := { name : Str, referrer : " ++ referrer ++ " }\n\n" ++
        \\wobble : { customer : Link(Customer) } -> Bool
        \\wobble = |input| input.customer == link("ada")
    ;
}

test "an inlined method over a nominal whose argument reaches the nominal again is read at the type it gives" {
    // `is_eq` is inlined, and the call's type and the inlined row's result
    // are one type, so its ends need no widening.
    const staged = try Staged.createRunning(std.testing.allocator, linkCompareOf("Link(Customer)"), "");
    defer staged.destroy();
    try staged.expectDump(
        \\row r0 ({ customer : Link }) -> Bool
        \\  n0 = field 0(p0) : Link
        \\  n1 = unwrap(n0) : { key : Str, row : List(Customer) }
        \\  n2 = field 0(n1) : Str
        \\  n3 = "ada" : Str
        \\  n4 = Str.is_eq(n2, n3) : Bool
        \\  value n4
        \\
    );
}

test "an inlined method over a nominal whose argument reaches it through a union, or not at all, reifies alike" {
    inline for (.{ "[Nobody, Referred(Link(Customer))]", "Str", "List(Customer)" }) |referrer| {
        const staged = try Staged.createRunning(std.testing.allocator, linkCompareOf(referrer), "");
        defer staged.destroy();
        if (staged.outcome != .reified) return error.TestUnexpectedResult;
    }
}

test "an inlined method that unwraps one nominal of a cycle to the other gives the type spelled at the other's root" {
    // `get` is walked by its body: its `Unwrap` of `Link` gives the backing
    // that holds `Person`, and the row's result is `Person` itself.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\Person := { links : List(Link) }
        \\
        \\Link := { row : Person }.{
        \\    get : Link -> Person
        \\    get = |Link.(l)| l.row
        \\}
        \\
        \\wobble : Link -> Bool
        \\wobble = |input| input.get().links.is_empty()
    , "");
    defer staged.destroy();
    try staged.expectDump(
        \\row r0 (Link) -> Bool
        \\  n0 = unwrap(p0) : { row : Person }
        \\  n1 = field 0(n0) : Person
        \\  n2 = unwrap(n1) : { links : List(Link) }
        \\  n3 = field 0(n2) : List(Link)
        \\  n4 = List.is_empty(n3) : Bool
        \\  value n4
        \\
    );
}

test "an inlined unwrap in a cycle through a union, a generic link, or self recursion alone reifies alike" {
    inline for (.{
        // The cycle runs through a tag union.
        \\Person := { referrer : [Nobody, Referred(Link)] }
        \\
        \\Link := { row : Person }.{
        \\    get : Link -> Person
        \\    get = |Link.(l)| l.row
        \\}
        \\
        \\wobble : Link -> Bool
        \\wobble = |input| match input.get().referrer { Nobody => Bool.True, Referred(_) => Bool.False }
        ,
        // The link is generic.
        \\Person := { links : List(Link(Person)) }
        \\
        \\Link(row) := { row : row }.{
        \\    get : Link(row) -> row
        \\    get = |Link.(l)| l.row
        \\}
        \\
        \\wobble : Link(Person) -> Bool
        \\wobble = |input| input.get().links.is_empty()
        ,
        // One nominal reaches itself.
        \\Person := { links : List(Person) }.{
        \\    links_of : Person -> List(Person)
        \\    links_of = |Person.(p)| p.links
        \\}
        \\
        \\wobble : Person -> Bool
        \\wobble = |input| input.links_of().is_empty()
    }) |source| {
        const staged = try Staged.createRunning(std.testing.allocator, source, "");
        defer staged.destroy();
        if (staged.outcome != .reified) return error.TestUnexpectedResult;
    }
}
