//! The driver of the reification fuzzers L4 and L5
//! (`roc-reify-normalization-plan.md` 5.1), shared by the fixed seed set in
//! the compile tests and by the AFL target `test/fuzzing/fuzz-reify.zig`.
//!
//! One case is one input to `reify.fuzz_gen`: an app holding two prints of
//! one generated function and a constant Roc computes their answer in. The
//! app is compiled the way `roc build` compiles it, and each print is walked
//! as a site. The two prints must describe as one normal form, or both be
//! refused for one reason (L4). The normal form, run by `reify.eval` on the
//! case's input, must compute the value Roc computed for the constant, and
//! where Roc crashed computing it any outcome is allowed (L5, the C2 table
//! of the plan's 5.6).

const std = @import("std");
const base = @import("base");
const build_options = @import("build_options");
const can = @import("can");
const check = @import("check");
const reify = @import("reify");
const eval = @import("eval");
const roc_target = @import("roc_target");

const Coordinator = @import("coordinator.zig").Coordinator;
const CoordinatorError = @import("coordinator.zig").CoordinatorError;
const CoreCtx = @import("ctx").CoreCtx;

const Allocator = std.mem.Allocator;
const CodeReifier = check.CodeReifier;
const ConstStore = check.ConstStore.ConstStore;
const CheckedExprId = check.CheckedArtifact.CheckedExprId;
const ModuleEnv = can.ModuleEnv;

/// The platform every generated app runs on.
pub const platform_main =
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

/// The one hosted module `platform_main` exposes.
pub const platform_echo =
    \\Echo := [].{
    \\    line! : Str => {}
    \\}
;

/// The method registries the walk reads, for a walk over one app.
///
/// A fixture declares its nominals in the app module, and the walk asks the
/// registries whether such a nominal writes `is_eq` or `to_hash` or derives
/// it, and whether its `to_inspect` is an inspect override. Publication answers
/// both from every view it holds; a test holds the app it published, where its
/// fixtures' nominals are declared, and the builtin artifact, where a builtin
/// container declares its own.
///
/// A call reaches a builtin through the builtin artifact's export rows, the
/// way publication reaches one through the view it holds. The two other
/// questions keep the answer this harness has always given them, which is
/// none.
pub const Lookup = struct {
    /// The app the walk describes.
    artifact: *const check.CheckedArtifact.CheckedModuleArtifact,
    /// The builtin artifact, where a builtin container declares its methods.
    builtins: *const check.CheckedArtifact.CheckedModuleArtifact,
    /// The views of the modules the app imports, where a call to one of
    /// their definitions is resolved.
    imports: []const check.CheckedArtifact.ImportedModuleView = &.{},

    /// The walk's view of these registries.
    pub fn lookup(self: *const Lookup) CodeReifier.ForeignLookup {
        var asked = CodeReifier.ForeignLookup.none;
        asked.context = self;
        asked.resolve_method = resolveMethod;
        asked.resolve_exported = resolveExported;
        asked.resolve_exported_computed = resolveExportedComputed;
        asked.resolve_constant = resolveConstant;
        asked.resolve_inspect_override = resolveInspectOverride;
        return asked;
    }

    fn resolveExported(
        context: *const anyopaque,
        artifact: check.CanonicalNames.ArtifactRef,
        def: can.CIR.Def.Idx,
    ) ?CodeReifier.ForeignDefinition {
        const self: *const Lookup = @ptrCast(@alignCast(context));
        if (std.meta.eql(self.builtins.key.bytes, artifact.bytes)) {
            return check.CheckedArtifact.exportedDefinition(check.CheckedArtifact.importedView(self.builtins), def);
        }
        for (self.imports) |view| {
            if (std.meta.eql(view.key.bytes, artifact.bytes)) return check.CheckedArtifact.exportedDefinition(view, def);
        }
        return null;
    }

    fn resolveExportedComputed(
        context: *const anyopaque,
        artifact: check.CanonicalNames.ArtifactRef,
        def: can.CIR.Def.Idx,
    ) ?CodeReifier.ForeignComputed {
        const self: *const Lookup = @ptrCast(@alignCast(context));
        for (self.imports) |view| {
            if (std.meta.eql(view.key.bytes, artifact.bytes)) return check.CheckedArtifact.exportedComputed(view, def);
        }
        return null;
    }

    fn resolveConstant(
        context: *const anyopaque,
        const_ref: check.CheckedArtifact.ConstRef,
    ) ?CodeReifier.ForeignConstant {
        const self: *const Lookup = @ptrCast(@alignCast(context));
        for (self.imports) |view| {
            if (std.meta.eql(view.key.bytes, const_ref.artifact.bytes)) return check.CheckedArtifact.exportedConstant(view, const_ref);
        }
        return null;
    }

    fn resolveInspectOverride(
        context: *const anyopaque,
        owner: CodeReifier.ForeignNominal,
    ) ?check.StaticDispatchRegistry.MethodTarget {
        const self: *const Lookup = @ptrCast(@alignCast(context));
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
        const self: *const Lookup = @ptrCast(@alignCast(context));
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

/// The lambda whose first parameter is named `param`, so a site may take
/// more than one. The source-node map is build-only, so the test reads the
/// pattern's region the same way the reifier does.
pub fn lambdaByParam(
    artifact: *const check.CheckedArtifact.CheckedModuleArtifact,
    env: *const ModuleEnv,
    param: []const u8,
) ?CheckedExprId {
    for (0..artifact.checked_bodies.exprCount()) |raw| {
        const expr_id: CheckedExprId = @fromBackingInt(@intCast(@as(u32, @intCast(raw))));
        const data = artifact.checked_bodies.expr(expr_id).data;
        if (data != .lambda) continue;
        const lambda = data.lambda;
        if (lambda.args.len == 0) continue;
        const pattern = artifact.checked_bodies.pattern(lambda.args[0]);
        if (pattern.data != .assign) continue;
        if (!std.mem.eql(u8, env.getSource(pattern.source_region), param)) continue;
        return expr_id;
    }
    return null;
}

/// The procedure template one checked lambda is the body of, which says what
/// the definition quantifies over.
pub fn templateOf(
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

/// What one case can fail with. A disagreement the case exists to find is
/// one of the last group; the driver prints the case and both sides first.
pub const Error = Allocator.Error ||
    Coordinator.AppDiscoveryError ||
    CoordinatorError ||
    reify.eval.Error ||
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
        UnsupportedHeader,
        UnsupportedTarget,
        WriteFailed,
        GeneratedCaseDidNotCheck,
        SiteNotFound,
        SiteDoesNotVerify,
        AnswerWasNotStored,
        AnswerWasNotU64,
        NormalFormsDiffer,
        RefusalsDiffer,
        ValuesDiffer,
        IntervalMissed,
    };

/// How a case ended where nothing disagreed.
pub const Verdict = enum {
    /// One normal form, which computes Roc's answer.
    agree,
    /// Both prints refused, for one reason.
    refused,
    /// One normal form, and Roc crashed computing the answer, so C2 allows
    /// any outcome of it.
    reference_crashed,
};

/// One site of the app: the walk of the lambda with a named parameter, and
/// its dump where the walk described it.
const Site = struct {
    gpa: Allocator,
    store: ConstStore,
    walk: CodeReifier.Walk,
    outcome: CodeReifier.Outcome,
    dump: std.ArrayList(u8) = .empty,

    /// Walk the site in place, since the walk keeps a pointer to the store.
    fn describe(self: *Site, gpa: Allocator, lookup: *const Lookup, env: *const ModuleEnv, param: []const u8) Error!void {
        return self.describeIn(gpa, lookup, env, param, .graph);
    }

    /// `describe`, for a site whose declared type selects `view`.
    fn describeIn(self: *Site, gpa: Allocator, lookup: *const Lookup, env: *const ModuleEnv, param: []const u8, view: @TypeOf(@as(CodeReifier.Walk, undefined).view)) Error!void {
        const artifact = lookup.artifact;
        self.gpa = gpa;
        self.dump = .empty;
        self.store = ConstStore.init(gpa);
        self.walk = CodeReifier.Walk.init(gpa, &self.store, lookup.lookup());
        self.walk.view = view;
        const lambda = lambdaByParam(artifact, env, param) orelse return error.SiteNotFound;
        const reifier = try self.walk.reader(.{ .sources = CodeReifier.Reifier.artifactSources(artifact), .env = env });
        self.outcome = try reifier.reifyLambda(lambda, .{
            .scheme = reifier.templateScheme(templateOf(artifact, lambda) orelse return error.SiteNotFound),
            .in_block = false,
            .caller = reifier,
            .fixed = null,
            .region = base.Region.zero(),
        });
        if (self.outcome != .reified) return;
        const site = self.walk.site.?;
        var report = try reify.verify.verifyAll(gpa, &site.store, &site.types);
        defer report.deinit();
        if (!report.ok()) {
            for (report.messages.items) |message| std.debug.print("verifier: {s}\n", .{message});
            return error.SiteDoesNotVerify;
        }
        var out: std.Io.Writer.Allocating = .init(gpa);
        defer out.deinit();
        reify.dump.dumpSite(&out.writer, gpa, &site.store, &site.types, self.walk.root.?) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.WriteFailed => return error.WriteFailed,
        };
        try self.dump.appendSlice(gpa, out.written());
    }

    fn deinit(self: *Site) void {
        self.dump.deinit(self.gpa);
        self.walk.deinit();
        self.store.deinit();
    }
};

/// Run the case `bytes` generates, writing its app into `dir`. The
/// coordinator allocates from `ctx.arena`, which the caller releases.
pub fn runCase(ctx: CoreCtx, builtins: *eval.BuiltinModules, dir: std.Io.Dir, bytes: []const u8) Error!Verdict {
    return runCaseWith(ctx, builtins, dir, bytes, .{});
}

/// `runCase` on the case `bytes` generates with the constructs `options` allows.
pub fn runCaseWith(ctx: CoreCtx, builtins: *eval.BuiltinModules, dir: std.Io.Dir, bytes: []const u8, options: reify.fuzz_gen.Options) Error!Verdict {
    var case = try reify.fuzz_gen.generateWith(ctx.gpa, bytes, options);
    defer case.deinit(ctx.gpa);
    return runGenerated(ctx, builtins, dir, &case) catch |err| {
        std.debug.print("{t} on the generated case:\n{s}\nLib:\n{s}\n", .{ err, case.source, case.lib_source });
        return err;
    };
}

fn runGenerated(ctx: CoreCtx, builtins: *eval.BuiltinModules, dir: std.Io.Dir, case: *const reify.fuzz_gen.Case) Error!Verdict {
    const gpa = ctx.gpa;
    const io = ctx.std_io;

    try dir.createDirPath(io, ".roc_echo_platform");
    try dir.writeFile(io, .{ .sub_path = ".roc_echo_platform/main.roc", .data = platform_main });
    try dir.writeFile(io, .{ .sub_path = ".roc_echo_platform/Echo.roc", .data = platform_echo });
    // M13: the helpers the case put in another package, in its module `Lib`.
    const has_lib = case.lib_source.len != 0;
    if (has_lib) {
        try dir.createDirPath(io, "lib");
        try dir.writeFile(io, .{ .sub_path = "lib/main.roc", .data = "package [Lib] {}\n\nimport /Lib as Lib\n" });
        const lib_source = try std.fmt.allocPrint(gpa, "Lib := {{}}.{{\n{s}}}\n", .{case.lib_source});
        defer gpa.free(lib_source);
        try dir.writeFile(io, .{ .sub_path = "lib/Lib.roc", .data = lib_source });
    }
    const app_source = try std.fmt.allocPrint(gpa,
        \\app [main!] {{ pf: platform "./.roc_echo_platform/main.roc"{s} }}
        \\
        \\import pf.Echo{s}
        \\
        \\{s}
        \\
        \\main! = |_args| Ok({{}})
        \\
    , .{
        if (has_lib) ", lib: \"./lib/main.roc\"" else "",
        if (has_lib) "\nimport lib.Lib" else "",
        case.source,
    });
    defer gpa.free(app_source);
    try dir.writeFile(io, .{ .sub_path = "main.roc", .data = app_source });
    const app_path = try dir.realPathFileAlloc(io, "main.roc", gpa);
    defer gpa.free(app_path);

    const arena = ctx.arena;
    var coord = try Coordinator.init(
        gpa,
        .single_threaded,
        1,
        roc_target.RocTarget.detectNative(),
        builtins,
        build_options.compiler_compatibility_id,
        null,
        ctx,
    );
    defer coord.deinit();
    coord.enable_hosted_transform = true;
    try coord.start();
    try coord.discoverAppFromPath(arena, .{ .entry_path = app_path });
    try coord.coordinatorLoop();
    if (errorsBesideCrashes(&coord)) {
        printReports(&coord);
        return error.GeneratedCaseDidNotCheck;
    }

    const artifact = coord.appRootCheckedArtifact();
    const env = artifact.module_env.env();
    const lookup: Lookup = .{
        .artifact = artifact,
        .builtins = &builtins.checked_artifact,
        .imports = try coord.collectImportedArtifactViews(arena, artifact),
    };
    // A case with the constructs of M10 meets in the `lawful` view, where
    // layer L applies (L4, loop to builtin).
    const view: @TypeOf(@as(CodeReifier.Walk, undefined).view) = if (case.lawful) .lawful else .graph;
    var left: Site = undefined;
    try left.describeIn(gpa, &lookup, env, case.left_param, view);
    defer left.deinit();
    var right: Site = undefined;
    try right.describeIn(gpa, &lookup, env, case.right_param, view);
    defer right.deinit();

    // L4: one normal form, or one refusal.
    switch (left.outcome) {
        .rejected => |a| switch (right.outcome) {
            .rejected => |b| {
                if (std.mem.eql(u8, a.detail, b.detail)) return .refused;
                std.debug.print("the prints are refused for different reasons: {s} and {s}\n", .{ a.detail, b.detail });
                return error.RefusalsDiffer;
            },
            .reified => {
                std.debug.print("only the left print is refused: {t} {s}\n{s}\n", .{ a.kind, a.detail, right.dump.items });
                return error.RefusalsDiffer;
            },
        },
        .reified => switch (right.outcome) {
            .rejected => |b| {
                std.debug.print("only the right print is refused: {t} {s}\n{s}\n", .{ b.kind, b.detail, left.dump.items });
                return error.RefusalsDiffer;
            },
            .reified => if (!std.mem.eql(u8, left.dump.items, right.dump.items)) {
                std.debug.print("the prints describe as two normal forms:\n{s}\n{s}\n", .{ left.dump.items, right.dump.items });
                return error.NormalFormsDiffer;
            },
        },
    }

    // The other views are compared on cases without M10's constructs, whose
    // spellings meet only under layer L.
    var left_inline: Site = undefined;
    var left_outline: Site = undefined;
    var left_graph: Site = undefined;
    if (case.lawful) {
        // L5 for laws: the graph the site describes without layer L.
        try left_graph.describe(gpa, &lookup, env, case.left_param);
    } else try compareViews(gpa, &lookup, env, case, &left_inline, &left_outline);
    defer if (case.lawful) left_graph.deinit() else {
        left_inline.deinit();
        left_outline.deinit();
    };

    // L5: the normal form's value is the one Roc computed at compile time.
    try coord.finishCheckedProgram(.executable_artifacts);
    if (errorsBesideCrashes(&coord)) {
        printReports(&coord);
        return error.GeneratedCaseDidNotCheck;
    }
    const expected = try storedAnswer(&coord, case.answer) orelse return .reference_crashed;
    // The answer is the only definition Roc evaluates, so no other crashed.
    if (coord.hasUserErrors()) {
        printReports(&coord);
        return error.GeneratedCaseDidNotCheck;
    }

    var values_impl = std.heap.ArenaAllocator.init(gpa);
    defer values_impl.deinit();
    const values = values_impl.allocator();
    const items = try values.alloc(reify.eval.Value, case.input.items.len);
    for (items, case.input.items) |*item, value| item.* = .{ .int = value };
    const fields = [_]reify.eval.Value{ .{ .int = case.input.a }, .{ .int = case.input.b }, .{ .bool_ = case.input.flag }, .{ .list = items } };
    const args = [_]reify.eval.Value{.{ .agg = &fields }};
    // Views agree: `graph`, `inline` and `outline` each compute Roc's
    // answer, or `lawful` and `graph` for a case with M10's constructs.
    const views: [3]?*const Site = if (case.lawful) .{ &left, &left_graph, null } else .{ &left, &left_inline, &left_outline };
    for (views) |maybe| {
        const each = maybe orelse continue;
        if (each.outcome != .reified) continue;
        const site = each.walk.site.?;
        var evaluator = try reify.eval.Evaluator.init(values, &site.store, &site.types, .strict);
        // L2 for N13u and N8k: every interval holds every value computed.
        evaluator.check_ranges = true;
        const computed = try evaluator.run(each.walk.root.?, &args);
        if (!computed.eql(.{ .int = expected })) {
            std.debug.print("the normal form computes {any}, and Roc computes {d}\n{s}\n", .{ computed, expected, each.dump.items });
            return error.ValuesDiffer;
        }
        if (evaluator.range_miss) |miss| {
            std.debug.print("node {d} of row {d} computes {d}, outside its interval [{d}, {d}]\n{s}\n", .{ miss.node.index(), miss.row.index(), miss.value, miss.interval.lo, miss.interval.hi, each.dump.items });
            return error.IntervalMissed;
        }
    }
    return .agree;
}

// L4 for V5a and V3: the prints meet in the `inline` and `outline` views,
// and in `inline` every node of them has one digest. The left print's sites
// are left in `left_inline` and `left_outline`.
fn compareViews(gpa: Allocator, lookup: *const Lookup, env: *const ModuleEnv, case: *const reify.fuzz_gen.Case, left_inline: *Site, left_outline: *Site) Error!void {
    try left_inline.describeIn(gpa, lookup, env, case.left_param, .inline_);
    errdefer left_inline.deinit();
    {
        var right_inline: Site = undefined;
        try right_inline.describeIn(gpa, lookup, env, case.right_param, .inline_);
        defer right_inline.deinit();
        if (left_inline.outcome == .reified and right_inline.outcome == .reified) {
            if (!std.mem.eql(u8, left_inline.dump.items, right_inline.dump.items)) {
                std.debug.print("the prints describe as two normal forms in the inline view:\n{s}\n{s}\n", .{ left_inline.dump.items, right_inline.dump.items });
                return error.NormalFormsDiffer;
            }
            const ls = left_inline.walk.site.?;
            const rs = right_inline.walk.site.?;
            const ld = try reify.rows.siteDigests(gpa, &ls.store, &ls.types, left_inline.walk.root.?);
            defer reify.digest.freeSite(gpa, ld);
            const rd = try reify.rows.siteDigests(gpa, &rs.store, &rs.types, right_inline.walk.root.?);
            defer reify.digest.freeSite(gpa, rd);
            var equal_digests = ld.len == rd.len;
            if (equal_digests) for (ld, rd) |a, b| {
                if (!std.mem.eql(reify.digest.Digest, a, b)) equal_digests = false;
            };
            if (!equal_digests) {
                std.debug.print("the prints meet in the inline view and their nodes have different digests:\n{s}\n", .{left_inline.dump.items});
                return error.NormalFormsDiffer;
            }
        } else if ((left_inline.outcome == .reified) != (right_inline.outcome == .reified)) {
            // One print is refused in this view and the other is not.
            return error.RefusalsDiffer;
        }
    }

    // L4 for V3: in the `outline` view, the prints meet.
    try left_outline.describeIn(gpa, lookup, env, case.left_param, .outline);
    errdefer left_outline.deinit();
    {
        var right_outline: Site = undefined;
        try right_outline.describeIn(gpa, lookup, env, case.right_param, .outline);
        defer right_outline.deinit();
        if (left_outline.outcome == .reified and right_outline.outcome == .reified) {
            if (!std.mem.eql(u8, left_outline.dump.items, right_outline.dump.items)) {
                std.debug.print("the prints describe as two normal forms in the outline view:\n{s}\n{s}\n", .{ left_outline.dump.items, right_outline.dump.items });
                return error.NormalFormsDiffer;
            }
        } else if ((left_outline.outcome == .reified) != (right_outline.outcome == .reified)) {
            return error.RefusalsDiffer;
        }
    }
}

// Whether a report other than a warning or a compile-time crash was made.
// The coordinator names a report's problem only by its title, which
// `check/report.zig` sets.
fn errorsBesideCrashes(coord: *Coordinator) bool {
    var reports = coord.iterReports();
    while (reports.next()) |entry| switch (entry.report.severity) {
        .warning => {},
        .runtime_error, .fatal => if (!std.mem.eql(u8, entry.report.title, "Compile Time Crash")) return true,
    };
    return false;
}

fn printReports(coord: *Coordinator) void {
    var reports = coord.iterReports();
    while (reports.next()) |entry| std.debug.print("report: {s} in {s}\n", .{ entry.report.title, entry.module_name });
}

/// The `U64` Roc computed at compile time for the top-level constant `name`,
/// or null where computing it crashed.
fn storedAnswer(coord: *Coordinator, name: []const u8) error{ AnswerWasNotStored, AnswerWasNotU64 }!?u64 {
    const artifact = coord.appRootCheckedArtifact();
    const env = artifact.module_env.env();
    const view = check.CheckedArtifact.importedView(artifact);
    for (view.compile_time_roots.roots) |root| {
        if (root.kind != .constant) continue;
        const pattern = root.pattern orelse continue;
        if (!std.mem.eql(u8, env.getSource(artifact.checked_bodies.pattern(pattern).source_region), name)) continue;
        const node = switch (root.payload) {
            .const_node => |const_node| const_node,
            .pending, .unevaluated, .fn_value, .discarded, .expect, .runtime => return error.AnswerWasNotStored,
        };
        return switch (view.const_store.get(node)) {
            .scalar => |scalar| switch (scalar) {
                .u64 => |value| value,
                .i8, .i16, .i32, .i64, .i128, .u8, .u16, .u32, .u128, .f32_bits, .f64_bits, .dec_bits => error.AnswerWasNotU64,
            },
            .crash => null,
            .pending, .zst, .str, .list, .box, .tuple, .record, .tag, .nominal, .fn_value, .checked_error => error.AnswerWasNotU64,
        };
    }
    return error.AnswerWasNotStored;
}
