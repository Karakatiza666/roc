//! The reifier over a real checked module: a function written in Roc becomes a
//! `Code.Ir` tree in the module's const store.

const std = @import("std");
const base = @import("base");
const build_options = @import("build_options");
const can = @import("can");
const check = @import("check");
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

const platform_main =
    \\platform ""
    \\    requires {} { main! : List(Str) => Try({}, [Exit(I8), ..]) }
    \\    exposes [Echo]
    \\    packages {}
    \\    provides { "roc_main": main_for_host! }
    \\    hosted { "roc_echo_line": Echo.line! }
    \\
    \\import Echo
    \\
    \\main_for_host! : List(Str) => I8
    \\main_for_host! = |args|
    \\    match main!(args) {
    \\        Ok({}) => 0
    \\        Err(Exit(code)) => code
    \\        Err(other) => {
    \\            Echo.line!("Program exited with error: ${Str.inspect(other)}")
    \\            1
    \\        }
    \\    }
;

const platform_echo =
    \\Echo := [].{
    \\    line! : Str => {}
    \\}
;

/// The method registries the walk reads, for a test that walks one app.
///
/// A fixture declares its nominals in the app module, and the walk asks the
/// registries whether such a nominal writes `is_eq` or `to_hash` or derives
/// it, and whether its `to_inspect` is an inspect override. Publication answers
/// both from every view it holds; a test holds the app it published, where its
/// fixtures' nominals are declared, and the builtin artifact, where a builtin
/// container declares its own.
///
/// The other three questions keep the answer this harness has always given
/// them, which is none.
const StagedLookup = struct {
    artifact: *const check.CheckedArtifact.CheckedModuleArtifact,
    builtins: *const check.CheckedArtifact.CheckedModuleArtifact,

    fn lookup(self: *const StagedLookup) CodeReifier.ForeignLookup {
        var asked = CodeReifier.ForeignLookup.none;
        asked.context = self;
        asked.resolve_method = resolveMethod;
        asked.resolve_inspect_override = resolveInspectOverride;
        return asked;
    }

    fn resolveInspectOverride(
        context: *const anyopaque,
        owner: CodeReifier.ForeignNominal,
    ) ?check.StaticDispatchRegistry.MethodTarget {
        const self: *const StagedLookup = @ptrCast(@alignCast(context));
        if (check.CheckedArtifact.registeredMethod(&self.artifact.canonical_names, &self.artifact.method_registry, owner, "to_inspect") != null) {
            return check.CheckedArtifact.registeredInspectOverride(&self.artifact.canonical_names, &self.artifact.method_registry, owner);
        }
        return check.CheckedArtifact.registeredInspectOverride(&self.builtins.canonical_names, &self.builtins.method_registry, owner);
    }

    fn resolveMethod(
        context: *const anyopaque,
        owner: CodeReifier.ForeignNominal,
        method: []const u8,
    ) ?check.StaticDispatchRegistry.MethodTarget {
        const self: *const StagedLookup = @ptrCast(@alignCast(context));
        if (check.CheckedArtifact.registeredMethod(
            &self.artifact.canonical_names,
            &self.artifact.method_registry,
            owner,
            method,
        )) |target| return target;
        return check.CheckedArtifact.registeredMethod(
            &self.builtins.canonical_names,
            &self.builtins.method_registry,
            owner,
            method,
        );
    }
};

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
        const self = try createChecked(gpa, wobble_source, main_statement);
        const artifact = self.coord.appRootCheckedArtifact();

        const lambda = stagedLambda(artifact, self.env) orelse return error.StagedLambdaNotFound;

        self.store = ConstStore.init(gpa);
        self.foreign = .{ .artifact = artifact, .builtins = &(try sharedBuiltinModules()).checked_artifact };
        self.walk = CodeReifier.Walk.init(gpa, &self.store, self.foreign.lookup());
        self.reifier = try self.walk.reader(.{
            .sources = CodeReifier.Reifier.artifactSources(artifact),
            .env = self.env,
        });
        self.outcome = try self.reifier.reifyLambda(lambda, .{
            .scheme = self.reifier.templateScheme(stagedTemplate(artifact, lambda) orelse return error.StagedLambdaNotFound),
            .in_block = false,
            .caller = self.reifier,
            // Every fixture here declares `wobble` at one concrete type, so
            // there is no quantified variable for a site to fix.
            .fixed = null,
            .region = base.Region.zero(),
        });
        return self;
    }

    /// The fixture, compiled and checked, with nothing described yet.
    fn createChecked(
        gpa: Allocator,
        wobble_source: []const u8,
        main_statement: []const u8,
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

        const app_source = try std.fmt.allocPrint(gpa,
            \\app [main!] {{ pf: platform "./.roc_echo_platform/main.roc" }}
            \\
            \\import pf.Echo
            \\
            \\{s}
            \\
            \\main! = |_args| {{
            \\    {s}
            \\    Ok({{}})
            \\}}
            \\
        , .{ wobble_source, main_statement });
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
        return self;
    }

    fn destroy(self: *Staged) void {
        self.walk.deinit();
        self.store.deinit();
        self.coord.deinit();
        self.arena_impl.deinit();
        self.tmp.cleanup();
        self.gpa.destroy(self);
    }

    /// The `Ir` root, or a test failure naming what the walk refused.
    ///
    /// A site holds `Code`'s backing, `{ defs, root }`, whose fields are in
    /// label order, so the body is the second.
    fn root(self: *Staged) RejectedError!ConstNodeId {
        switch (self.outcome) {
            .reified => |node| return self.recordFields(node)[1],
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

    fn tagName(self: *Staged, node: ConstNodeId) []const u8 {
        return self.store.get(node).tag.tag_name;
    }

    fn payloads(self: *Staged, node: ConstNodeId) []const ConstNodeId {
        return self.store.get(node).tag.payloads;
    }

    fn strText(self: *Staged, node: ConstNodeId) []const u8 {
        return self.store.strBytes(self.store.get(node).str);
    }

    fn listNodes(self: *Staged, node: ConstNodeId) []const ConstNodeId {
        return self.store.get(node).list.nodes;
    }

    fn recordFields(self: *Staged, node: ConstNodeId) []const ConstNodeId {
        return self.store.get(node).record;
    }

    /// The definitions a site's table holds, as `{ ir, name }` rows in label
    /// order.
    fn definitions(self: *Staged) RejectedError![]const ConstNodeId {
        switch (self.outcome) {
            .reified => |node| return self.listNodes(self.recordFields(node)[0]),
            .rejected => return error.StagedBodyRejected,
        }
    }

    /// The type a node's `Meta` carries. A constant record's fields are
    /// restored in label order, so `region` precedes `ty`.
    fn metaTy(self: *Staged, meta: ConstNodeId) ConstNodeId {
        return self.recordFields(meta)[1];
    }

    /// The node a `Meta`'s region names its module through. Every `Region` in
    /// a description names one module, so this is one node per walk.
    fn metaModule(self: *Staged, meta: ConstNodeId) ConstNodeId {
        return self.recordFields(self.recordFields(meta)[0])[2];
    }

    /// The region a node's `Meta` carries, as (module_name, start_line,
    /// start_column, end_line, end_column) read out of its label order.
    fn metaRegion(self: *Staged, meta: ConstNodeId) struct {
        module_name: []const u8,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    } {
        const fields = self.recordFields(self.recordFields(meta)[0]);
        return .{
            .module_name = self.strText(fields[2]),
            .start_line = self.store.get(fields[4]).scalar.u32,
            .start_column = self.store.get(fields[3]).scalar.u32,
            .end_line = self.store.get(fields[1]).scalar.u32,
            .end_column = self.store.get(fields[0]).scalar.u32,
        };
    }

    /// The `Ir` body of the staged lambda, past its parameter list.
    fn body(self: *Staged) RejectedError!ConstNodeId {
        return self.payloads(try self.root())[1];
    }
};

/// The lambda bound to `wobble`, found by the name of its one parameter. The
/// source-node map is build-only, so the test reads the pattern's region the
/// same way the reifier does.
fn stagedLambda(
    artifact: *const check.CheckedArtifact.CheckedModuleArtifact,
    env: *const ModuleEnv,
) ?CheckedExprId {
    for (0..artifact.checked_bodies.exprCount()) |raw| {
        const expr_id: CheckedExprId = @fromBackingInt(@intCast(@as(u32, @intCast(raw))));
        const data = artifact.checked_bodies.expr(expr_id).data;
        if (data != .lambda) continue;
        const lambda = data.lambda;
        if (lambda.args.len != 1) continue;
        const pattern = artifact.checked_bodies.pattern(lambda.args[0]);
        if (pattern.data != .assign) continue;
        if (!std.mem.eql(u8, env.getSource(pattern.source_region), "input")) continue;
        return expr_id;
    }
    return null;
}

/// The procedure template one checked lambda is the body of, which says what
/// the definition quantifies over.
fn stagedTemplate(
    artifact: *const check.CheckedArtifact.CheckedModuleArtifact,
    lambda: CheckedExprId,
) ?check.CheckedArtifact.CheckedProcedureTemplate {
    for (artifact.checked_procedure_templates.templates.items) |template| {
        const body = switch (template.body) {
            .checked_body => |body_id| body_id,
            .intrinsic_wrapper, .entry_wrapper, .unimplemented => continue,
        };
        if (artifact.checked_bodies.body(body).root_expr != lambda) continue;
        return template;
    }
    return null;
}

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

    const body = try staged.body();
    try std.testing.expectEqualStrings("Binop", staged.tagName(body));
    try std.testing.expectEqualStrings("times", staged.strText(staged.payloads(body)[0]));

    const rhs = staged.payloads(body)[2];
    try std.testing.expectEqualStrings("Lit", staged.tagName(rhs));
    const literal = staged.payloads(rhs)[0];
    try std.testing.expectEqualStrings("Frac", staged.tagName(literal));
    const bits = staged.store.get(staged.payloads(literal)[0]).scalar.f64_bits;
    try std.testing.expectEqual(@as(f64, 3.5), @as(f64, @bitCast(bits)));

    // The staged lambda's parameters are its own, so the template's parameter
    // is absent from the signature the stage reads.
    const params = staged.listNodes(staged.payloads(try staged.root())[0]);
    try std.testing.expectEqual(@as(usize, 1), params.len);
    try std.testing.expectEqualStrings("input", staged.strText(staged.recordFields(params[0])[0]));
}

test "a checked function body becomes a Code.Ir tree" {
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| {
        \\    wave = input.uv * 2.0.F32
        \\    wave + input.time
        \\}
    );
    defer staged.destroy();

    // Lambda([{ name: "input", ty: Named(...) }], Let(...), Meta)
    const root = try staged.root();
    try std.testing.expectEqualStrings("Lambda", staged.tagName(root));
    const lambda_args = staged.payloads(root);
    try std.testing.expectEqual(@as(usize, 3), lambda_args.len);

    const params = staged.listNodes(lambda_args[0]);
    try std.testing.expectEqual(@as(usize, 1), params.len);
    try std.testing.expectEqualStrings("input", staged.strText(staged.recordFields(params[0])[0]));

    // A lambda carries its own type, the way every other node does, so the
    // return type sits inside the function type rather than in the slot.
    const lambda_ty = staged.metaTy(lambda_args[2]);
    try std.testing.expectEqualStrings("Fn", staged.tagName(lambda_ty));
    try std.testing.expectEqualStrings("F32", staged.tagName(staged.payloads(lambda_ty)[1]));

    // The `wave =` binding survives as a Let rather than being inlined, which
    // is the property a stage needs to emit one GLSL local.
    const let_node = try staged.body();
    try std.testing.expectEqualStrings("Let", staged.tagName(let_node));
    const let_args = staged.payloads(let_node);
    try std.testing.expectEqualStrings("wave", staged.strText(let_args[0]));

    // wave = input.uv * 2.0.F32
    const times = staged.payloads(let_args[1]);
    try std.testing.expectEqualStrings("Binop", staged.tagName(let_args[1]));
    try std.testing.expectEqualStrings("times", staged.strText(times[0]));
    try std.testing.expectEqualStrings("Field", staged.tagName(times[1]));
    const uv = staged.payloads(times[1]);
    try std.testing.expectEqualStrings("Param", staged.tagName(uv[0]));
    try std.testing.expectEqualStrings("input", staged.strText(staged.payloads(uv[0])[0]));
    try std.testing.expectEqualStrings("uv", staged.strText(uv[1]));

    // The digit pool is a big-endian base-256 magnitude, not ASCII, so assert
    // the decoded value and not just the node's shape.
    try std.testing.expectEqualStrings("Lit", staged.tagName(times[2]));
    const frac = staged.payloads(staged.payloads(times[2])[0]);
    try std.testing.expectEqual(
        @as(f64, 2.0),
        @as(f64, @bitCast(staged.store.get(frac[0]).scalar.f64_bits)),
    );

    // wave + input.time
    const plus = staged.payloads(let_args[2]);
    try std.testing.expectEqualStrings("Binop", staged.tagName(let_args[2]));
    try std.testing.expectEqualStrings("plus", staged.strText(plus[0]));
    try std.testing.expectEqualStrings("Local", staged.tagName(plus[1]));
    try std.testing.expectEqualStrings("wave", staged.strText(staged.payloads(plus[1])[0]));
    try std.testing.expectEqualStrings("Field", staged.tagName(plus[2]));
    try std.testing.expectEqualStrings("time", staged.strText(staged.payloads(plus[2])[1]));
}

test "a plain call names its callee, and the table holds the callee's body" {
    const staged = try Staged.create(std.testing.allocator,
        \\step : F32 -> F32
        \\step = |x| x + 1.0.F32
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| step(input.uv) + step(step(input.time))
    );
    defer staged.destroy();

    // The call names the callee, module-qualified, and the callee's body is
    // nowhere in the described body.
    const plus = staged.payloads(try staged.body());
    try std.testing.expectEqualStrings("Call", staged.tagName(plus[1]));
    try std.testing.expectEqualStrings("main.step", staged.strText(staged.payloads(plus[1])[0]));

    // One row, however many calls reach it. `Code.Def` is `{ ir, name }`, and
    // a constant record's fields are restored in label order.
    const rows = try staged.definitions();
    try std.testing.expectEqual(@as(usize, 1), rows.len);
    const row = staged.recordFields(rows[0]);
    try std.testing.expectEqualStrings("main.step", staged.strText(row[1]));
    try std.testing.expectEqualStrings("Lambda", staged.tagName(row[0]));
}

test "every Ir node carries where it was written" {
    // The region is resolved to lines and columns in the walk rather than left
    // as a byte offset, because a stage holds a description and never the
    // source text an offset would need. The lambda spans two lines, so all four
    // numbers differ and a field restored out of order cannot pass.
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input|
        \\    input.uv * 2.0.F32
    );
    defer staged.destroy();

    // The fixture's app header takes four lines, so `wobble = ` is on line 6.
    const lambda = staged.metaRegion(staged.payloads(try staged.root())[2]);
    try std.testing.expectEqualStrings("main", lambda.module_name);
    try std.testing.expectEqual(@as(u32, 6), lambda.start_line);
    try std.testing.expectEqual(@as(u32, 10), lambda.start_column);
    try std.testing.expectEqual(@as(u32, 7), lambda.end_line);
    try std.testing.expectEqual(@as(u32, 23), lambda.end_column);

    // A node inside the body points at its own span, not the lambda's.
    const body = try staged.body();
    const times = staged.metaRegion(staged.payloads(body)[3]);
    try std.testing.expectEqual(@as(u32, 7), times.start_line);
    try std.testing.expectEqual(@as(u32, 5), times.start_column);
    try std.testing.expectEqual(@as(u32, 7), times.end_line);
    try std.testing.expectEqual(@as(u32, 23), times.end_column);

    // A chain of field reads becomes one `Field` per segment, and each points
    // at its own segment: this one covers `.uv`, not the `input` it reads from.
    const field = staged.metaRegion(staged.payloads(staged.payloads(body)[1])[2]);
    try std.testing.expectEqual(@as(u32, 10), field.start_column);
    try std.testing.expectEqual(@as(u32, 13), field.end_column);
}

test "a derived == on a scalar becomes an is_eq Binop" {
    // `==` desugars to `is_eq`, and every numeric type derives it, so the
    // checker rewrites the call to `structural_eq` before the reifier sees it.
    // A comparison against a constant is the first thing a shader body writes.
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| if input.time == 0.0.F32 input.uv else input.time
    );
    defer staged.destroy();

    const body = try staged.body();
    try std.testing.expectEqualStrings("If", staged.tagName(body));
    const condition = staged.payloads(body)[0];
    try std.testing.expectEqualStrings("Binop", staged.tagName(condition));
    try std.testing.expectEqualStrings("is_eq", staged.strText(staged.payloads(condition)[0]));
    try std.testing.expectEqualStrings("Field", staged.tagName(staged.payloads(condition)[1]));
    try std.testing.expectEqualStrings("Lit", staged.tagName(staged.payloads(condition)[2]));
}

test "a derived != on a scalar becomes a negated is_eq" {
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| if input.time != 0.0.F32 input.uv else input.time
    );
    defer staged.destroy();

    const condition = staged.payloads(try staged.body())[0];
    try std.testing.expectEqualStrings("Unary", staged.tagName(condition));
    try std.testing.expectEqualStrings("not", staged.strText(staged.payloads(condition)[0]));
    const compare = staged.payloads(condition)[1];
    try std.testing.expectEqualStrings("Binop", staged.tagName(compare));
    try std.testing.expectEqualStrings("is_eq", staged.strText(staged.payloads(compare)[0]));
}

test "a hand-written is_eq becomes an is_eq Binop" {
    // A written `is_eq` carries a dispatch plan, so it is an ordinary method
    // call. It reads as derived only because the checker groups it with the
    // two forms that are.
    const staged = try Staged.create(std.testing.allocator,
        \\Meters := F32.{
        \\    is_eq : Meters, Meters -> Bool
        \\    is_eq = |Meters.(a), Meters.(b)| a == b
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input|
        \\    if Meters.(input.time) == Meters.(0.0.F32) input.uv else input.time
    );
    defer staged.destroy();

    const condition = staged.payloads(try staged.body())[0];
    try std.testing.expectEqualStrings("Binop", staged.tagName(condition));
    try std.testing.expectEqualStrings("is_eq", staged.strText(staged.payloads(condition)[0]));
}

test "a written is_eq reached by != becomes a negated is_eq" {
    // Which of `==` and `!=` the author wrote rides on the dispatch plan when
    // the type writes its own `is_eq`, so a walk that reads only the checked
    // node describes the comparison the body negates.
    const staged = try Staged.create(std.testing.allocator,
        \\Meters := F32.{
        \\    is_eq : Meters, Meters -> Bool
        \\    is_eq = |Meters.(a), Meters.(b)| a == b
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input|
        \\    if Meters.(input.time) != Meters.(0.0.F32) input.uv else input.time
    );
    defer staged.destroy();

    const condition = staged.payloads(try staged.body())[0];
    try std.testing.expectEqualStrings("Unary", staged.tagName(condition));
    try std.testing.expectEqualStrings("not", staged.strText(staged.payloads(condition)[0]));
    const compare = staged.payloads(condition)[1];
    try std.testing.expectEqualStrings("Binop", staged.tagName(compare));
    try std.testing.expectEqualStrings("is_eq", staged.strText(staged.payloads(compare)[0]));
}

test "a string a description names twice is one node" {
    // A description names the same few strings over and over: one module name
    // per `Region`, one operator name per arithmetic node, one field name per
    // read of that field. A node id is a shared reference, so the second
    // mention is the first node.
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| input.time + input.uv + input.time
    );
    defer staged.destroy();

    // `+` is left associative, so the outer node's left operand is the inner.
    const outer = staged.payloads(try staged.body());
    const inner = staged.payloads(outer[1]);
    try std.testing.expectEqualStrings("plus", staged.strText(outer[0]));
    try std.testing.expectEqual(outer[0], inner[0]);
    try std.testing.expectEqual(staged.metaModule(outer[3]), staged.metaModule(inner[3]));

    // `input.time` is read twice, and both reads name the field through one
    // node.
    const first = staged.payloads(inner[1]);
    const second = staged.payloads(outer[2]);
    try std.testing.expectEqualStrings("time", staged.strText(first[1]));
    try std.testing.expectEqual(first[1], second[1]);
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

    const condition = staged.payloads(try staged.body())[0];
    try std.testing.expectEqualStrings("Binop", staged.tagName(condition));
    try std.testing.expectEqualStrings("and", staged.strText(staged.payloads(condition)[0]));

    for (staged.payloads(condition)[1..3], 0..) |compare, index| {
        try std.testing.expectEqualStrings("Binop", staged.tagName(compare));
        try std.testing.expectEqualStrings("is_eq", staged.strText(staged.payloads(compare)[0]));

        const left = staged.payloads(compare)[1];
        const right = staged.payloads(compare)[2];
        try std.testing.expectEqualStrings("Field", staged.tagName(left));
        try std.testing.expectEqualStrings("Field", staged.tagName(right));
        const field = if (index == 0) "time" else "uv";
        try std.testing.expectEqualStrings(field, staged.strText(staged.payloads(left)[1]));
        try std.testing.expectEqualStrings(field, staged.strText(staged.payloads(right)[1]));
        try std.testing.expectEqualStrings("Param", staged.tagName(staged.payloads(left)[0]));
        try std.testing.expectEqualStrings("MakeRecord", staged.tagName(staged.payloads(right)[0]));
    }
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

    const condition = staged.payloads(try staged.body())[0];
    try std.testing.expectEqualStrings("Binop", staged.tagName(condition));
    try std.testing.expectEqualStrings("and", staged.strText(staged.payloads(condition)[0]));

    for (staged.payloads(condition)[1..3]) |compare| {
        try std.testing.expectEqualStrings("Binop", staged.tagName(compare));
        try std.testing.expectEqualStrings("is_eq", staged.strText(staged.payloads(compare)[0]));
        try std.testing.expectEqualStrings("Index", staged.tagName(staged.payloads(compare)[1]));
        try std.testing.expectEqualStrings("Index", staged.tagName(staged.payloads(compare)[2]));
    }
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

    // The outer call feeds the last component, so the inner one is the first.
    const outer = try staged.body();
    try std.testing.expectEqualStrings("Call", staged.tagName(outer));
    try std.testing.expectEqualStrings("Builtin.Hasher.write_f32", staged.strText(staged.payloads(outer)[0]));

    const outer_args = staged.listNodes(staged.payloads(outer)[1]);
    try std.testing.expectEqual(@as(usize, 2), outer_args.len);
    try std.testing.expectEqualStrings("b", staged.strText(staged.payloads(outer_args[1])[1]));

    const inner = outer_args[0];
    try std.testing.expectEqualStrings("Call", staged.tagName(inner));
    try std.testing.expectEqualStrings("Builtin.Hasher.write_u64", staged.strText(staged.payloads(inner)[0]));

    const inner_args = staged.listNodes(staged.payloads(inner)[1]);
    try std.testing.expectEqualStrings("Field", staged.tagName(inner_args[0]));
    try std.testing.expectEqualStrings("hasher", staged.strText(staged.payloads(inner_args[0])[1]));
    try std.testing.expectEqualStrings("a", staged.strText(staged.payloads(inner_args[1])[1]));
}

test "a derived to_hash the walk cannot reach stays a Derived node" {
    // `List` writes its own `to_hash`, so the compiler dispatches to it rather
    // than walking the list's representation. The reifier cannot see that
    // method, so it describes none of the derivation instead of part of it.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : { keys : List(U64), hasher : Hasher } -> Hasher
        \\wobble = |input| { a: input.keys }.to_hash(input.hasher)
    , "");
    defer staged.destroy();

    const body = try staged.body();
    try std.testing.expectEqualStrings("Derived", staged.tagName(body));
    try std.testing.expectEqualStrings("to_hash", staged.strText(staged.payloads(body)[0]));

    // The subject is the type derived over, which no argument carries.
    const subject = staged.payloads(body)[1];
    try std.testing.expectEqualStrings("Record", staged.tagName(subject));
    const subject_fields = staged.listNodes(staged.payloads(subject)[0]);
    try std.testing.expectEqual(@as(usize, 1), subject_fields.len);
    try std.testing.expectEqualStrings("a", staged.strText(staged.recordFields(subject_fields[0])[0]));

    const args = staged.listNodes(staged.payloads(body)[2]);
    try std.testing.expectEqual(@as(usize, 2), args.len);
    try std.testing.expectEqualStrings("MakeRecord", staged.tagName(args[0]));
    try std.testing.expectEqualStrings("hasher", staged.strText(staged.payloads(args[1])[1]));

    // `Hasher` is opaque, so its `Ty` names it without its backing.
    const ty = staged.metaTy(staged.payloads(body)[3]);
    try std.testing.expectEqualStrings("Opaque", staged.tagName(ty));
    try std.testing.expectEqualStrings("Builtin.Hasher", staged.strText(staged.payloads(ty)[0]));
    try std.testing.expectEqual(@as(usize, 0), staged.listNodes(staged.payloads(ty)[1]).len);
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

    const condition = staged.payloads(try staged.body())[0];
    try std.testing.expectEqualStrings("Binop", staged.tagName(condition));
    try std.testing.expectEqualStrings("is_eq", staged.strText(staged.payloads(condition)[0]));
    try std.testing.expectEqualStrings("Field", staged.tagName(staged.payloads(condition)[1]));
}

test "a derived == through a nominal component that writes its own is_eq calls it" {
    // The comparison Roc performs is the method, not the backing, so the
    // description is the call and the method's body goes into the table the way
    // any other callee's does.
    const staged = try Staged.create(std.testing.allocator,
        \\Meters := { m: F32 }.{
        \\    is_eq : Meters, Meters -> Bool
        \\    is_eq = |a, b| a.m == b.m
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input|
        \\    if { w: Meters.({ m: input.time }) } == { w: Meters.({ m: 0.0.F32 }) } input.uv else input.time
    );
    defer staged.destroy();

    const condition = staged.payloads(try staged.body())[0];
    try std.testing.expectEqualStrings("Call", staged.tagName(condition));
    try std.testing.expectEqualStrings("Meters.is_eq", staged.strText(staged.payloads(condition)[0]));
    try std.testing.expectEqual(@as(usize, 2), staged.listNodes(staged.payloads(condition)[1]).len);

    var written: ?ConstNodeId = null;
    for (try staged.definitions()) |row| {
        const fields = staged.recordFields(row);
        if (std.mem.eql(u8, "Meters.is_eq", staged.strText(fields[1]))) written = fields[0];
    }
    try std.testing.expectEqualStrings("Lambda", staged.tagName(written.?));
    try std.testing.expectEqualStrings("Binop", staged.tagName(staged.payloads(written.?)[1]));
}

test "a derived to_hash through a nominal component that writes its own to_hash calls it" {
    // The same question, asked of the other derivation: a written `to_hash` is
    // the one Roc threads the hasher through, so the recipe stops at the call.
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

    const body = try staged.body();
    try std.testing.expectEqualStrings("Call", staged.tagName(body));
    try std.testing.expectEqualStrings("Meters.to_hash", staged.strText(staged.payloads(body)[0]));

    // `to_hash : value, Hasher -> Hasher`, so the value comes first.
    const args = staged.listNodes(staged.payloads(body)[1]);
    try std.testing.expectEqual(@as(usize, 2), args.len);
    try std.testing.expectEqualStrings("a", staged.strText(staged.payloads(args[0])[1]));
    try std.testing.expectEqualStrings("hasher", staged.strText(staged.payloads(args[1])[1]));
}

test "a generic nominal component's own is_eq describes at the instantiation its receiver fixes" {
    // A derivation reaches the method with no call site, so no dispatch edge
    // says what the method's quantified variables stand for. The receiver says
    // it: the method's first parameter is the value the derivation compares,
    // and pairing the two binds the scheme by shape. Without that pairing the
    // call keeps its name and the table holds no row for it.
    const staged = try Staged.create(std.testing.allocator,
        \\Boxed(a) := { v : a, tag : U64 }.{
        \\    is_eq : Boxed(a), Boxed(a) -> Bool
        \\    is_eq = |x, y| x.tag == y.tag
        \\}
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input|
        \\    if { w: Boxed.({ v: input.time, tag: 1.U64 }) } == { w: Boxed.({ v: 0.0.F32, tag: 2.U64 }) } input.uv else input.time
    );
    defer staged.destroy();

    const condition = staged.payloads(try staged.body())[0];
    try std.testing.expectEqualStrings("Call", staged.tagName(condition));
    try std.testing.expectEqualStrings("Boxed.is_eq", staged.strText(staged.payloads(condition)[0]));

    var written: ?ConstNodeId = null;
    for (try staged.definitions()) |row| {
        const fields = staged.recordFields(row);
        if (std.mem.eql(u8, "Boxed.is_eq", staged.strText(fields[1]))) written = fields[0];
    }
    try std.testing.expectEqualStrings("Lambda", staged.tagName(written.?));
    try std.testing.expectEqualStrings("Binop", staged.tagName(staged.payloads(written.?)[1]));
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

    const condition = staged.payloads(try staged.body())[0];
    try std.testing.expectEqualStrings("Call", staged.tagName(condition));
    try std.testing.expectEqualStrings("List.is_eq", staged.strText(staged.payloads(condition)[0]));
    try std.testing.expectEqual(@as(usize, 2), staged.listNodes(staged.payloads(condition)[1]).len);
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

    const body = try staged.body();
    try std.testing.expectEqualStrings("Call", staged.tagName(body));
    try std.testing.expectEqualStrings("Builtin.Dict.to_inspect", staged.strText(staged.payloads(body)[0]));
    const args = staged.listNodes(staged.payloads(body)[1]);
    try std.testing.expectEqual(@as(usize, 1), args.len);
    try std.testing.expectEqualStrings("d", staged.strText(staged.payloads(args[0])[1]));
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

    const body = try staged.body();
    try std.testing.expectEqualStrings("Derived", staged.tagName(body));
    try std.testing.expectEqualStrings("to_inspect", staged.strText(staged.payloads(body)[0]));

    const subject = staged.payloads(body)[1];
    try std.testing.expectEqualStrings("Record", staged.tagName(subject));
    const subject_fields = staged.listNodes(staged.payloads(subject)[0]);
    try std.testing.expectEqual(@as(usize, 1), subject_fields.len);
    try std.testing.expectEqualStrings("d", staged.strText(staged.recordFields(subject_fields[0])[0]));

    const args = staged.listNodes(staged.payloads(body)[2]);
    try std.testing.expectEqual(@as(usize, 1), args.len);
    try std.testing.expectEqualStrings("MakeRecord", staged.tagName(args[0]));
}

test "Str.inspect of a nominal that writes an eligible to_inspect calls it" {
    // The written method is the rendering, so its body goes into the table
    // the way any other callee's does.
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

    const body = try staged.body();
    try std.testing.expectEqualStrings("Call", staged.tagName(body));
    try std.testing.expectEqualStrings("Meters.to_inspect", staged.strText(staged.payloads(body)[0]));

    var written: ?ConstNodeId = null;
    for (try staged.definitions()) |row| {
        const fields = staged.recordFields(row);
        if (std.mem.eql(u8, "Meters.to_inspect", staged.strText(fields[1]))) written = fields[0];
    }
    try std.testing.expectEqualStrings("Lambda", staged.tagName(written.?));
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

    const body = try staged.body();
    try std.testing.expectEqualStrings("Derived", staged.tagName(body));
    try std.testing.expectEqualStrings("to_inspect", staged.strText(staged.payloads(body)[0]));
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

    try std.testing.expectError(error.StagedBodyRejected, staged.body());
}

test "a derived == on a type with one inhabitant is True" {
    // The fold over zero components has no comparison to make, and both
    // operands hold the only value the type has.
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| if {} == {} input.uv else input.time
    );
    defer staged.destroy();

    const condition = staged.payloads(try staged.body())[0];
    try std.testing.expectEqualStrings("Lit", staged.tagName(condition));
    const literal = staged.payloads(condition)[0];
    try std.testing.expectEqualStrings("Bool", staged.tagName(literal));
    try std.testing.expectEqualStrings("True", staged.tagName(staged.payloads(literal)[0]));
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

    try std.testing.expectError(error.StagedBodyRejected, staged.body());
}

test "a top-level constant folds into the description where its name stands" {
    // The value is written where the name was, so a translator never learns a
    // name stood between the body and the value. The fold is by value: no
    // capture, no closure environment, and no new `Ir` node.
    const staged = try Staged.create(std.testing.allocator,
        \\threshold = 0.5.F32
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| input.uv * threshold
    );
    defer staged.destroy();

    const body = try staged.body();
    try std.testing.expectEqualStrings("Binop", staged.tagName(body));

    const rhs = staged.payloads(body)[2];
    try std.testing.expectEqualStrings("Lit", staged.tagName(rhs));
    const literal = staged.payloads(rhs)[0];
    try std.testing.expectEqualStrings("Frac", staged.tagName(literal));
    const bits = staged.store.get(staged.payloads(literal)[0]).scalar.f64_bits;
    try std.testing.expectEqual(@as(f64, 0.5), @as(f64, @bitCast(bits)));
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

    const body = try staged.body();
    const rhs = staged.payloads(body)[2];
    try std.testing.expectEqualStrings("Lit", staged.tagName(rhs));
    const literal = staged.payloads(rhs)[0];
    const bits = staged.store.get(staged.payloads(literal)[0]).scalar.f64_bits;
    try std.testing.expectEqual(@as(f64, 3.5), @as(f64, @bitCast(bits)));
}

test "a top-level name the compiler cannot fix stays refused" {
    // The boundary is the one a template argument already drew: a value the
    // compiler fixes folds, and a value the running program computes does not.
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

    try std.testing.expectError(error.StagedBodyRejected, staged.body());
}

test "a default operand describes as the match it desugars to" {
    // `??` canonicalizes to a match with an `Ok` passthrough branch, and the
    // name that branch binds is the compiler's. The walk gives it one of its
    // own rather than refusing the branch.
    const staged = try Staged.create(std.testing.allocator,
        \\pick : Try(F32, [Bad]), F32 -> F32
        \\pick = |t, fallback| t ?? fallback
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| pick(Ok(input.time), input.uv)
    );
    defer staged.destroy();

    // `pick` describes as a row of its own, and the call in `wobble` names it.
    const body = try staged.body();
    try std.testing.expectEqualStrings("Call", staged.tagName(body));
}

test "an as pattern keeps the name it binds beside the pattern it renames" {
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| match { v: input.time } {
        \\    { v: _ } as whole => whole.v
        \\}
    );
    defer staged.destroy();

    const body = try staged.body();
    try std.testing.expectEqualStrings("Match", staged.tagName(body));
    const branches = staged.listNodes(staged.payloads(body)[1]);
    try std.testing.expectEqual(@as(usize, 1), branches.len);
    // A `Branch` is `{ guard, patterns, value }` in label order.
    const patterns = staged.listNodes(staged.recordFields(branches[0])[1]);
    try std.testing.expectEqualStrings("PatAs", staged.tagName(patterns[0]));
    try std.testing.expectEqualStrings("PatRecord", staged.tagName(staged.payloads(patterns[0])[0]));
    try std.testing.expectEqualStrings("whole", staged.strText(staged.payloads(patterns[0])[1]));
}

test "a `?` written inside an expression lifts the match out past the expression" {
    // `?` desugars to the same match `??` does, with the `Err` branch
    // returning early instead of holding a default. Written inside an
    // expression the transfer would skip that expression, and the `Ir` has
    // no node that skips work. Lifting the match out past it leaves the
    // surviving branch holding the whole expression, and no transfer at all.
    const staged = try Staged.create(std.testing.allocator,
        \\pick : Try(F32, [Bad]) -> Try(F32, [Bad])
        \\pick = |t| Ok(t? * 2.0.F32)
        \\
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| match pick(Ok(input.time)) {
        \\    Ok(v) => v
        \\    Err(_) => input.uv
        \\}
    );
    defer staged.destroy();

    var lambda: ?ConstNodeId = null;
    for (try staged.definitions()) |row| {
        const fields = staged.recordFields(row);
        if (std.mem.eql(u8, "main.pick", staged.strText(fields[1]))) lambda = fields[0];
    }
    const pick = staged.payloads(lambda.?)[1];
    try std.testing.expectEqualStrings("Match", staged.tagName(pick));
    const branches = staged.listNodes(staged.payloads(pick)[1]);
    try std.testing.expectEqual(@as(usize, 2), branches.len);
    // `Ok(v) => Ok(v * 2.0)`: the branch holds what the `?` was written
    // inside, and the `Err` branch forwards the error it matched.
    const ok = staged.recordFields(branches[0])[2];
    try std.testing.expectEqualStrings("MakeTag", staged.tagName(ok));
    try std.testing.expectEqualStrings("Binop", staged.tagName(staged.listNodes(staged.payloads(ok)[1])[0]));
    const err = staged.recordFields(branches[1])[2];
    try std.testing.expectEqualStrings("MakeTag", staged.tagName(err));
    try std.testing.expectEqualStrings("Err", staged.strText(staged.payloads(err)[0]));
}

test "a numeral of the author's own type describes as the conversion that makes it" {
    // The operand `from_numeral` receives is a `Num.Numeral`, an opaque the
    // compiler threads to plumb the conversion. The description carries the
    // number the author wrote and names the conversion beside it.
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

    const body = try staged.body();
    try std.testing.expectEqualStrings("Meters.scale", staged.strText(staged.payloads(body)[0]));

    const conversion = staged.listNodes(staged.payloads(body)[1])[0];
    try std.testing.expectEqualStrings("Call", staged.tagName(conversion));
    try std.testing.expectEqualStrings(
        "Meters.from_numeral",
        staged.strText(staged.payloads(conversion)[0]),
    );
    // The call carries the nominal it makes, so a translator reads `Meters`
    // from the conversion rather than from the literal under it.
    try std.testing.expectEqualStrings(
        "Named",
        staged.tagName(staged.metaTy(staged.payloads(conversion)[2])),
    );

    const literal = staged.listNodes(staged.payloads(conversion)[1])[0];
    try std.testing.expectEqualStrings("Lit", staged.tagName(literal));
    const value = staged.payloads(literal)[0];
    try std.testing.expectEqualStrings("Frac", staged.tagName(value));
    try std.testing.expectEqualStrings("F64", staged.tagName(staged.payloads(value)[1]));
    const bits = staged.store.get(staged.payloads(value)[0]).scalar.f64_bits;
    try std.testing.expectEqual(@as(f64, 3.0), @as(f64, @bitCast(bits)));

    // `from_numeral` reads `Numeral` internals, so the walk cannot describe
    // its body and the name stands alone, the way a builtin's does.
    for (try staged.definitions()) |row| {
        try std.testing.expect(!std.mem.eql(u8, "Meters.from_numeral", staged.strText(staged.recordFields(row)[1])));
    }
}

test "a whole numeral of the author's own type takes the widest integer the union holds" {
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

    const body = try staged.body();
    const conversion = staged.listNodes(staged.payloads(body)[1])[0];
    const literal = staged.listNodes(staged.payloads(conversion)[1])[0];
    const value = staged.payloads(literal)[0];
    try std.testing.expectEqualStrings("Int", staged.tagName(value));
    try std.testing.expectEqualStrings("I128", staged.tagName(staged.payloads(value)[1]));
    try std.testing.expectEqual(@as(i128, 7), staged.store.get(staged.payloads(value)[0]).scalar.i128);
}

test "a quoted literal of the author's own type describes as its conversion" {
    // `from_quote` receives the post-escape bytes, so the description carries
    // them as a `Str` and names the conversion that reads them.
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

    const body = try staged.body();
    const conversion = staged.listNodes(staged.payloads(body)[1])[0];
    try std.testing.expectEqualStrings("Call", staged.tagName(conversion));
    try std.testing.expectEqualStrings(
        "Name.from_quote",
        staged.strText(staged.payloads(conversion)[0]),
    );

    const literal = staged.listNodes(staged.payloads(conversion)[1])[0];
    const value = staged.payloads(literal)[0];
    try std.testing.expectEqualStrings("Str", staged.tagName(value));
    try std.testing.expectEqualStrings("hi", staged.strText(staged.payloads(value)[0]));
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

    const body = try staged.body();
    const branches = staged.listNodes(staged.payloads(body)[1]);
    // A `Branch` is `{ guard, patterns, value }` in label order.
    const patterns = staged.listNodes(staged.recordFields(branches[0])[1]);
    try std.testing.expectEqualStrings("PatGuard", staged.tagName(patterns[0]));

    // The pattern binds the matched value under a name the walk invented,
    // because `7` is no name an author could have written.
    const bound = staged.payloads(patterns[0])[0];
    try std.testing.expectEqualStrings("Bind", staged.tagName(bound));
    try std.testing.expectEqualStrings("bind#0", staged.strText(staged.payloads(bound)[0]));

    const condition = staged.payloads(patterns[0])[1];
    try std.testing.expectEqualStrings("Binop", staged.tagName(condition));
    try std.testing.expectEqualStrings("is_eq", staged.strText(staged.payloads(condition)[0]));

    const lhs = staged.payloads(condition)[1];
    try std.testing.expectEqualStrings("Local", staged.tagName(lhs));
    try std.testing.expectEqualStrings("bind#0", staged.strText(staged.payloads(lhs)[0]));

    const rhs = staged.payloads(condition)[2];
    try std.testing.expectEqualStrings("Call", staged.tagName(rhs));
    try std.testing.expectEqualStrings("Count.from_numeral", staged.strText(staged.payloads(rhs)[0]));
    const literal = staged.listNodes(staged.payloads(rhs)[1])[0];
    try std.testing.expectEqual(
        @as(i128, 7),
        staged.store.get(staged.payloads(staged.payloads(literal)[0])[0]).scalar.i128,
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

    const body = try staged.body();
    const branches = staged.listNodes(staged.payloads(body)[1]);
    const patterns = staged.listNodes(staged.recordFields(branches[0])[1]);
    try std.testing.expectEqual(@as(usize, 2), patterns.len);

    // The branch keeps one branch and one value, and no guard of its own.
    try std.testing.expectEqualStrings("NoGuard", staged.tagName(staged.recordFields(branches[0])[0]));

    var names: [2][]const u8 = undefined;
    for (patterns, 0..) |pattern, index| {
        try std.testing.expectEqualStrings("PatGuard", staged.tagName(pattern));
        names[index] = staged.strText(staged.payloads(staged.payloads(pattern)[0])[0]);
        const condition = staged.payloads(pattern)[1];
        try std.testing.expectEqualStrings(names[index], staged.strText(staged.payloads(staged.payloads(condition)[1])[0]));
    }
    try std.testing.expect(!std.mem.eql(u8, names[0], names[1]));
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

    const body = try staged.body();
    const branches = staged.listNodes(staged.payloads(body)[1]);
    const patterns = staged.listNodes(staged.recordFields(branches[0])[1]);
    try std.testing.expectEqualStrings("Variant", staged.tagName(patterns[0]));
    const payload = staged.listNodes(staged.payloads(patterns[0])[1])[0];
    try std.testing.expectEqualStrings("PatGuard", staged.tagName(payload));
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

    const body = try staged.body();
    const branches = staged.listNodes(staged.payloads(body)[1]);
    const patterns = staged.listNodes(staged.recordFields(branches[0])[1]);
    try std.testing.expectEqualStrings("PatGuard", staged.tagName(patterns[0]));
    const condition = staged.payloads(patterns[0])[1];
    const rhs = staged.payloads(condition)[2];
    try std.testing.expectEqualStrings("Name.from_quote", staged.strText(staged.payloads(rhs)[0]));
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

    const body = try staged.body();
    const branches = staged.listNodes(staged.payloads(body)[1]);
    const patterns = staged.listNodes(staged.recordFields(branches[0])[1]);
    const condition = staged.payloads(patterns[0])[1];
    try std.testing.expectEqualStrings("is_eq", staged.strText(staged.payloads(condition)[0]));
    try std.testing.expectEqualStrings("Field", staged.tagName(staged.payloads(condition)[1]));
    try std.testing.expectEqualStrings("Field", staged.tagName(staged.payloads(condition)[2]));
}

test "a string of more than one segment describes as the concatenation it is" {
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| if "p${input.uv.to_str()}q".is_empty() input.uv else input.time
    );
    defer staged.destroy();

    // The checker binds each interpolated value, so a `Let` stands between
    // the call and the joins it wraps.
    const cond = staged.payloads(try staged.body())[0];
    try std.testing.expectEqualStrings("Call", staged.tagName(cond));
    try std.testing.expectEqualStrings("Builtin.Str.is_empty", staged.strText(staged.payloads(cond)[0]));
    const bound = staged.listNodes(staged.payloads(cond)[1])[0];
    try std.testing.expectEqualStrings("Let", staged.tagName(bound));

    // `concat(concat("p", bind), "q")`, under the name a written `a.concat(b)`
    // takes.
    const outer = staged.payloads(bound)[2];
    try std.testing.expectEqualStrings("Builtin.Str.concat", staged.strText(staged.payloads(outer)[0]));
    const outer_args = staged.listNodes(staged.payloads(outer)[1]);
    try std.testing.expectEqualStrings("q", staged.strText(staged.payloads(staged.payloads(outer_args[1])[0])[0]));

    const inner = outer_args[0];
    try std.testing.expectEqualStrings("Builtin.Str.concat", staged.strText(staged.payloads(inner)[0]));
    const inner_args = staged.listNodes(staged.payloads(inner)[1]);
    try std.testing.expectEqualStrings("p", staged.strText(staged.payloads(staged.payloads(inner_args[0])[0])[0]));
    try std.testing.expectEqualStrings("Local", staged.tagName(inner_args[1]));
}

test "an empty segment of an interpolated string joins nothing" {
    // `"${v}"` carries a segment on each side that the author wrote no text
    // in, so the literal describes as the value alone.
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| if "${input.uv.to_str()}".is_empty() input.uv else input.time
    );
    defer staged.destroy();

    const cond = staged.payloads(try staged.body())[0];
    const bound = staged.listNodes(staged.payloads(cond)[1])[0];
    try std.testing.expectEqualStrings("Local", staged.tagName(staged.payloads(bound)[2]));
}

test "a record update reads a subject that is already a name" {
    // `input` describes as a `Param`, which a translator repeats as it
    // stands, so the walk reads it once per field rather than binding it.
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv : F32 } -> F32
        \\wobble = |input| { ..input, uv: 1.0.F32 }.time
    );
    defer staged.destroy();

    const access = try staged.body();
    try std.testing.expectEqualStrings("Field", staged.tagName(access));

    const built = staged.payloads(access)[0];
    try std.testing.expectEqualStrings("MakeRecord", staged.tagName(built));

    // One entry per field of the record type, the written one holding what
    // the update wrote and the other a read of the subject.
    const entries = staged.listNodes(staged.payloads(built)[0]);
    try std.testing.expectEqual(@as(usize, 2), entries.len);
    for (entries) |entry| {
        const fields = staged.recordFields(entry);
        const value = fields[1];
        if (std.mem.eql(u8, staged.strText(fields[0]), "uv")) {
            try std.testing.expectEqualStrings("Lit", staged.tagName(value));
            continue;
        }
        try std.testing.expectEqualStrings("Field", staged.tagName(value));
        try std.testing.expectEqualStrings("Param", staged.tagName(staged.payloads(value)[0]));
    }
}

test "a record type says which of its fields may be absent" {
    const staged = try Staged.create(std.testing.allocator,
        \\wobble : { time : F32, uv ?: F32 } -> F32
        \\wobble = |input| input.time
    );
    defer staged.destroy();

    const params = staged.listNodes(staged.payloads(try staged.root())[0]);
    const record = staged.recordFields(params[0])[1];
    try std.testing.expectEqualStrings("Record", staged.tagName(record));

    // `{ name, presence, ty }` in label order, so presence sits in the middle.
    for (staged.listNodes(staged.payloads(record)[0])) |entry| {
        const fields = staged.recordFields(entry);
        const presence = staged.tagName(fields[1]);
        if (std.mem.eql(u8, staged.strText(fields[0]), "uv")) {
            try std.testing.expectEqualStrings("Optional", presence);
            continue;
        }
        try std.testing.expectEqualStrings("Required", presence);
    }
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

    const branches = staged.listNodes(staged.payloads(try staged.body())[1]);
    const pattern = staged.listNodes(staged.recordFields(branches[0])[1])[0];
    try std.testing.expectEqualStrings("PatListRest", staged.tagName(pattern));

    // `[before, rest, after, meta]`: the rest is not one of the patterns, so
    // one written on each side of it leaves one in each list.
    const parts = staged.payloads(pattern);
    try std.testing.expectEqual(@as(usize, 1), staged.listNodes(parts[0]).len);
    try std.testing.expectEqual(@as(usize, 1), staged.listNodes(parts[2]).len);
    try std.testing.expectEqualStrings("Named", staged.tagName(parts[1]));
    try std.testing.expectEqualStrings("mid", staged.strText(staged.payloads(parts[1])[0]));
}

test "a string pattern's capture keeps the name the author wrote in it" {
    // The capture's region is the whole `${head}`, which is no name a target
    // accepts, so the walk reads the identifier out of it rather than
    // inventing one.
    const staged = try Staged.createRunning(std.testing.allocator,
        \\wobble : Str -> Str
        \\wobble = |input| match input {
        \\    "a${head}z" => head
        \\    _ => input
        \\}
    , "");
    defer staged.destroy();

    const branches = staged.listNodes(staged.payloads(try staged.body())[1]);
    const pattern = staged.listNodes(staged.recordFields(branches[0])[1])[0];
    try std.testing.expectEqualStrings("PatStr", staged.tagName(pattern));

    // `[prefix, steps, end, meta]`, each step `{ capture, delimiter }` in
    // label order.
    const parts = staged.payloads(pattern);
    try std.testing.expectEqualStrings("a", staged.strText(parts[0]));
    try std.testing.expectEqualStrings("Exact", staged.tagName(parts[2]));

    const steps = staged.listNodes(parts[1]);
    try std.testing.expectEqual(@as(usize, 1), steps.len);
    const step = staged.recordFields(steps[0]);
    try std.testing.expectEqualStrings("Named", staged.tagName(step[0]));
    try std.testing.expectEqualStrings("head", staged.strText(staged.payloads(step[0])[0]));
    try std.testing.expectEqualStrings("z", staged.strText(step[1]));
}
