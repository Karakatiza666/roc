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

    const WalkedAs = union(enum) {
        /// A definition, at the scheme of its template.
        named,
        /// A definition, at the scheme of its template, in the `inline` view.
        inlined,
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
            .inlined => self.walk.view = .inline_,
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

test "a top-level value of another package that computes a function is a Prim named by its module and name" {
    // N8h: the definition is that package's body, which the walk does not read.
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
        \\  n1 = Lib.doubler(n0) : F32 !spec
        \\  value n1
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
        \\  n12 = switch n1 : Builtin.Try !spec
        \\    arm 0
        \\      n2 = tag Err(p0) : [Err(U64), Ok(U64)]
        \\      n3 = wrap(n2) : Builtin.Try
        \\      value n3
        \\    arm 1
        \\      n4 = 1 : U64
        \\      n5 = Num.U64.plus(p0, n4) : U64 !spec
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
        \\  n8 = switch n1 : Builtin.Try !spec
        \\    arm 0
        \\      n2 = tag Err(p0) : [Err(U64), Ok(U64)]
        \\      n3 = wrap(n2) : Builtin.Try
        \\      value n3
        \\    arm 1
        \\      n4 = 1 : U64
        \\      n5 = Num.U64.plus(p0, n4) : U64 !spec
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
        \\  n14 = switch n0 : Builtin.Try !spec
        \\    arm 0
        \\      n1 = field 1(p0) : U64
        \\      n2 = 10 : U64
        \\      n3 = Num.U64.is_lt(n1, n2) : Bool
        \\      n10 = switch n3 : Builtin.Try !spec
        \\        arm 0
        \\          n4 = tag Err(n1) : [Err(U64), Ok(U64)]
        \\          n5 = wrap(n4) : Builtin.Try
        \\          value n5
        \\        arm 1
        \\          n6 = 1 : U64
        \\          n7 = Num.U64.plus(n1, n6) : U64 !spec
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
        \\  n4 = switch n2 : F32
        \\    arm 0
        \\      n3 = field 0(p0) : F32
        \\      value n3
        \\    arm 1
        \\      value n1
        \\  value n4
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
        \\      n6 = Num.U64.minus(n0, n5) : U64 !spec
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

/// Both sources describe `wobble` to the same dump.
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

test "L7: a refactor inside a function of another package leaves the caller's normal form unchanged" {
    // N8h: a function of another package is a named `Prim`, so its body is
    // not the description's, and a refactor inside it changes nothing here.
    const gpa = std.testing.allocator;
    const caller =
        \\wobble : { a : U64, b : U64 } -> U64
        \\wobble = |input| Lib.scale(input.a, input.b) + 1
    ;
    const written = try Staged.createSite(gpa, caller, "", "input",
        \\Lib := {}.{
        \\    scale : U64, U64 -> U64
        \\    scale = |v, k| v * k
        \\}
    );
    defer written.destroy();
    const refactored = try Staged.createSite(gpa, caller, "", "input",
        \\Lib := {}.{
        \\    scale : U64, U64 -> U64
        \\    scale = |v, k| {
        \\        product = k * v
        \\        product
        \\    }
        \\}
    );
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

test "L3 M6: a loop with a `$done` flag stays a general loop, so it is not the `for` over a range" {
    try expectOtherNormalForm(
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

test "L3 M6: a second counter derived from the first stays a slot of the loop" {
    try expectOtherNormalForm(
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
        \\        $total = $total + i + 5
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
