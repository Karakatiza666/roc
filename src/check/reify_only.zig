//! Reify-only definitions and the roots rule (design.md "Reify-Only
//! Definitions").
//!
//! A top-level definition is reify-only when code of it that runs at run
//! time references an intrinsic or another reify-only definition. Compile-time
//! evaluation counts as run time. This pass runs once, after the module is
//! checked. It reads only data that checking produced:
//!
//! - the checked bodies of the top-level definitions and `expect`s;
//! - the roots of the description-only subtrees (`description_only_roots`);
//! - the dispatch edges that selected a target, with their use sites and
//!   `runs` bits;
//! - the roots: the definitions whose code runs whatever references them.
//!
//! It then computes a breadth-first least fixpoint over the definitions that
//! are not roots. A definition that becomes reify-only in round `n` records as
//! its witness its first reference whose target is an intrinsic, a reify-only
//! definition of an imported module, or a definition of this module that
//! became reify-only before round `n`. So each chain of witnesses ends at an
//! intrinsic and has no cycle.
//!
//! A root is never reify-only. Each reference in a root that runs and whose
//! target is an intrinsic or a reify-only definition is a violation, which
//! checking reports and poisons. A reference to a root therefore makes no
//! definition reify-only.
//!
//! A dispatch whose site poisoning removed from the tree gives no edge. The
//! poisoned code crashes before it can reach the dispatch.

const std = @import("std");
const base = @import("base");
const can = @import("can");

const checking_interface = @import("checking_interface.zig");

const Allocator = std.mem.Allocator;
const ModuleEnv = can.ModuleEnv;
const CIR = can.CIR;
const DependencyGraph = can.DependencyGraph;
const Ident = base.Ident;
const Region = base.Region;
const Witness = ModuleEnv.ReifyOnlyWitness;

/// A top-level definition of some module.
pub const Target = struct {
    env: *const ModuleEnv,
    def: CIR.Def.Idx,
};

/// A dispatch edge that selected `target`, at its use site in this module.
/// `runs` is the final bit of the relation that dispatches at the site.
pub const Dispatch = struct {
    site_expr: CIR.Expr.Idx,
    runs: bool,
    target: Target,
    method_name: Ident.Idx,
};

/// A lookup that names an intrinsic, as checking saw it. A walk of the
/// checked bodies finds the same lookup unless poisoning removed it, and
/// debug builds check that the two agree on whether it runs.
pub const ValueReference = struct {
    target: Target,
    /// Whether no description-only body encloses the lookup.
    runs: bool,
};

/// How the pass finds the definitions that other modules' lookups name.
pub const Resolver = struct {
    context: *const anyopaque,
    /// The top-level definition that an external lookup names, or null when
    /// the name is not bound by a top-level definition.
    external: *const fn (context: *const anyopaque, import_idx: CIR.Import.Idx, target_node_idx: u32) Allocator.Error!?Target,
    /// The module that a resolved associated lookup names.
    associated: *const fn (context: *const anyopaque, module_identity: base.ModuleIdentity.Idx) *const ModuleEnv,
};

/// The data that checking produced for the pass.
pub const Input = struct {
    description_only_roots: *const std.AutoHashMapUnmanaged(CIR.Expr.Idx, void),
    dispatches: []const Dispatch,
    value_references: *const std.AutoHashMapUnmanaged(CIR.Expr.Idx, ValueReference),
    /// The top-level definitions whose code runs whatever references them:
    /// the provided entry points and platform requirements, the executable
    /// roots, and the top-level constants. Every top-level `expect` is a
    /// root too.
    roots: *const std.AutoHashMapUnmanaged(CIR.Def.Idx, void),
    resolver: Resolver,
    /// The checker's classification of a definition (`defReference`).
    classify: *const fn (*const ModuleEnv, CIR.Def) checking_interface.Definition,
};

/// A reify-only definition or `expect`, with its witness and the module of
/// the witness's target.
pub fn Entry(comptime Owner: type) type {
    return struct {
        owner: Owner,
        witness: Witness,
        target_env: *const ModuleEnv,
        /// As `Violation.via`, for a dispatch witness.
        via: ?Target,
    };
}

/// A reference in a root that runs and whose target is an intrinsic or a
/// reify-only definition.
pub const Violation = struct {
    /// The expression that checking reports and poisons: the call for a
    /// callee, else the reference itself.
    site: CIR.Expr.Idx,
    kind: Witness.Kind,
    target: Target,
    method_name: Ident.Idx,
    /// For a dispatch at a use of another definition, that definition: the
    /// dispatch resolves a requirement of it.
    via: ?Target,
};

/// The module's reify-only definitions, its violations, and the expressions
/// that reach code only reified code can use.
pub const Result = struct {
    /// The reify-only definitions that are not roots, in ascending order of
    /// definition id.
    defs: std.ArrayListUnmanaged(Entry(CIR.Def.Idx)) = .empty,
    /// The top-level `expect`s with a violation, in source order. The
    /// witness is the first violation.
    expects: std.ArrayListUnmanaged(Entry(CIR.Statement.Idx)) = .empty,
    /// The violations of the roots, in owner order, then in walk order.
    violations: std.ArrayListUnmanaged(Violation) = .empty,
    /// Each expression, inside a description-only subtree or not, that
    /// references an intrinsic or a reify-only definition, or that is the
    /// site of a dispatch that selected one. A compile-time root that holds
    /// one is not evaluated (design.md "Compile-Time Constants and Hoisted
    /// Roots").
    reaching_exprs: std.AutoHashMapUnmanaged(CIR.Expr.Idx, void) = .empty,

    pub fn deinit(self: *Result, gpa: Allocator) void {
        self.defs.deinit(gpa);
        self.expects.deinit(gpa);
        self.violations.deinit(gpa);
        self.reaching_exprs.deinit(gpa);
    }
};

const Edge = struct {
    /// The index of the definition or `expect` that holds the reference: a
    /// definition index first, then the `expect`s after all definitions.
    owner: u32,
    kind: Witness.Kind,
    /// The reference: the lookup, or the site of a dispatch.
    expr: CIR.Expr.Idx,
    /// The expression a violation reports and poisons: the call of a callee,
    /// else `expr`.
    site: CIR.Expr.Idx,
    region: Region,
    target: Target,
    method_name: Ident.Idx,
    /// As `Violation.via`.
    via: ?Target = null,
    /// Whether the reference is outside every description-only subtree.
    runs: bool,
};

/// Whether a walk is over code that runs, or over a description-only subtree.
/// The edges of a described walk feed only `Result.reaching_exprs`. Debug
/// builds also check there the invariants that relate the tree to the `runs`
/// bits.
const Mode = enum { run_time, described };

const Walker = struct {
    gpa: Allocator,
    cir: *const ModuleEnv,
    input: Input,
    pattern_to_def: std.AutoHashMapUnmanaged(CIR.Pattern.Idx, CIR.Def.Idx) = .empty,
    /// The first dispatch at each site, and the next dispatch at the same
    /// site of each dispatch (`std.math.maxInt(u32)` ends a chain).
    first_dispatch_at: std.AutoHashMapUnmanaged(CIR.Expr.Idx, u32) = .empty,
    next_dispatch: std.ArrayListUnmanaged(u32) = .empty,
    /// The callee of each call in the current walk, with its call.
    callees: std.AutoHashMapUnmanaged(CIR.Expr.Idx, CIR.Expr.Idx) = .empty,
    edges: std.ArrayListUnmanaged(Edge) = .empty,
    stack: std.ArrayListUnmanaged(CIR.Expr.Idx) = .empty,
    seen_defaults: std.AutoHashMapUnmanaged(CIR.Expr.Idx, void) = .empty,
    /// The description-only roots the current run-time walk skipped.
    skipped_roots: std.ArrayListUnmanaged(CIR.Expr.Idx) = .empty,
    /// The edges of the described walks.
    described_edges: std.ArrayListUnmanaged(Edge) = .empty,

    const no_dispatch = std.math.maxInt(u32);

    fn deinit(self: *Walker) void {
        self.pattern_to_def.deinit(self.gpa);
        self.first_dispatch_at.deinit(self.gpa);
        self.next_dispatch.deinit(self.gpa);
        self.callees.deinit(self.gpa);
        self.edges.deinit(self.gpa);
        self.stack.deinit(self.gpa);
        self.seen_defaults.deinit(self.gpa);
        self.skipped_roots.deinit(self.gpa);
        self.described_edges.deinit(self.gpa);
    }

    fn init(self: *Walker, defs: []const CIR.Def.Idx) Allocator.Error!void {
        var binders: std.ArrayList(CIR.Pattern.Idx) = .empty;
        defer binders.deinit(self.gpa);
        var scratch: std.ArrayList(CIR.Pattern.Idx) = .empty;
        defer scratch.deinit(self.gpa);
        for (defs) |def_idx| {
            binders.clearRetainingCapacity();
            try DependencyGraph.appendPatternBinders(self.cir, self.cir.store.getDef(def_idx).pattern, &binders, &scratch, self.gpa);
            for (binders.items) |binder| try self.pattern_to_def.put(self.gpa, binder, def_idx);
        }

        try self.next_dispatch.resize(self.gpa, self.input.dispatches.len);
        var index = self.input.dispatches.len;
        while (index > 0) {
            index -= 1;
            const entry = try self.first_dispatch_at.getOrPut(self.gpa, self.input.dispatches[index].site_expr);
            self.next_dispatch.items[index] = if (entry.found_existing) entry.value_ptr.* else no_dispatch;
            entry.value_ptr.* = @intCast(index);
        }
    }

    /// Collect the run-time references of the body `root` into `edges`, and
    /// the references of its description-only subtrees into
    /// `described_edges`.
    fn walkBody(self: *Walker, owner: u32, root: CIR.Expr.Idx) Allocator.Error!void {
        self.skipped_roots.clearRetainingCapacity();
        try self.walk(.run_time, owner, root);
        // A described walk skips no subtree, so it adds no root.
        const skipped = self.skipped_roots.items.len;
        for (0..skipped) |index| {
            try self.walk(.described, owner, self.skipped_roots.items[index]);
        }
        std.debug.assert(self.skipped_roots.items.len == skipped);
    }

    fn addEdge(self: *Walker, mode: Mode, edge: Edge) Allocator.Error!void {
        switch (mode) {
            .run_time => try self.edges.append(self.gpa, edge),
            .described => try self.described_edges.append(self.gpa, edge),
        }
    }

    fn walk(self: *Walker, mode: Mode, owner: u32, root: CIR.Expr.Idx) Allocator.Error!void {
        const store = &self.cir.store;
        self.stack.clearRetainingCapacity();
        self.seen_defaults.clearRetainingCapacity();
        self.callees.clearRetainingCapacity();
        try self.stack.append(self.gpa, root);
        while (self.stack.pop()) |expr_idx| {
            // A dispatch at a description-only root itself runs exactly when
            // its bit says so: the root is the place a description is built.
            try self.visitDispatchSites(mode, owner, expr_idx, expr_idx != root);
            if (mode == .run_time and self.input.description_only_roots.contains(expr_idx)) {
                try self.skipped_roots.append(self.gpa, expr_idx);
                continue;
            }
            // Checking recorded each lookup of an intrinsic. Where the walk
            // still reaches one, the two agree on whether it runs.
            if (self.input.value_references.get(expr_idx)) |reference| {
                std.debug.assert(reference.runs == (mode == .run_time));
            }
            // The argument of `Code.prim` is no use of the definition it
            // names: the call computes its id, and nothing reads its value.
            const target = if (store.isCodePrimArgument(ModuleEnv.nodeIdxFrom(expr_idx))) null else try self.referenceTarget(expr_idx);
            if (target) |found| {
                const call = self.callees.get(expr_idx);
                try self.addEdge(mode, .{
                    .owner = owner,
                    .kind = if (call != null or isStaticCall(store.getExpr(expr_idx))) .call else .lookup,
                    .expr = expr_idx,
                    .site = call orelse expr_idx,
                    .region = store.getExprRegion(expr_idx),
                    .target = found,
                    .method_name = Ident.Idx.NONE,
                    .runs = mode == .run_time,
                });
            }
            try self.pushChildren(expr_idx);
        }
    }

    /// Add an edge for each dispatch at `expr_idx`. In a run-time walk, only
    /// a dispatch that runs is an edge. In a description-only subtree, below
    /// its root, no dispatch runs. The dispatches at the root itself were
    /// visited by the run-time walk.
    fn visitDispatchSites(self: *Walker, mode: Mode, owner: u32, expr_idx: CIR.Expr.Idx, below_root: bool) Allocator.Error!void {
        var index = self.first_dispatch_at.get(expr_idx) orelse return;
        // A dispatch at a use of another definition, or at a call of one,
        // resolves a requirement of that definition.
        const site = self.cir.store.getExpr(expr_idx);
        const used_expr = if (site == .e_call) site.e_call.func else expr_idx;
        const used = if (self.cir.store.isCodePrimArgument(ModuleEnv.nodeIdxFrom(used_expr))) null else try self.referenceTarget(used_expr);
        while (index != no_dispatch) : (index = self.next_dispatch.items[index]) {
            const dispatch = self.input.dispatches[index];
            const via = if (used) |found|
                if (found.env == dispatch.target.env and found.def == dispatch.target.def) null else found
            else
                null;
            const edge: Edge = .{
                .owner = owner,
                .kind = .dispatch,
                .expr = expr_idx,
                .site = self.callees.get(expr_idx) orelse expr_idx,
                .region = self.cir.store.getExprRegion(expr_idx),
                .target = dispatch.target,
                .method_name = dispatch.method_name,
                .via = via,
                .runs = mode == .run_time,
            };
            switch (mode) {
                .described => {
                    std.debug.assert(!(below_root and dispatch.runs));
                    if (below_root) try self.addEdge(mode, edge);
                },
                .run_time => if (dispatch.runs) try self.addEdge(mode, edge),
            }
        }
    }

    /// The top-level definition that the expression names, when it is a
    /// lookup of one or a static call of a method of a local type.
    fn referenceTarget(self: *Walker, expr_idx: CIR.Expr.Idx) Allocator.Error!?Target {
        const local = struct {
            fn method(cir: *const ModuleEnv, stmt: CIR.Statement.Idx, name: Ident.Idx) ?Target {
                const binding = cir.lookupMethodBindingForOwnerConst(stmt, name) orelse return null;
                return .{ .env = cir, .def = binding.def_idx };
            }
        };
        return switch (self.cir.store.getExpr(expr_idx)) {
            .e_lookup_local => |lookup| if (self.pattern_to_def.get(lookup.pattern_idx)) |def_idx|
                .{ .env = self.cir, .def = def_idx }
            else
                null,
            .e_lookup_external => |lookup| try self.input.resolver.external(self.input.resolver.context, lookup.module_idx, lookup.target_node_idx),
            .e_lookup_associated_resolved => |lookup| .{
                .env = if (lookup.module_identity == self.cir.selfModuleIdentity())
                    self.cir
                else
                    self.input.resolver.associated(self.input.resolver.context, lookup.module_identity),
                .def = lookup.target_def_idx,
            },
            .e_type_method_call => |call| local.method(self.cir, call.type_dispatch_stmt, call.method_name),
            .e_type_dispatch_call => |call| switch (call.owner) {
                .statement => |stmt| local.method(self.cir, stmt, call.method_name),
                .dispatcher => null,
            },
            .e_num,
            .e_frac_f32,
            .e_frac_f64,
            .e_dec,
            .e_dec_small,
            .e_num_from_numeral,
            .e_typed_int,
            .e_typed_frac,
            .e_typed_num_from_numeral,
            .e_str_segment,
            .e_str,
            .e_bytes_literal,
            .e_deferred_import_ref,
            .e_lookup_associated_local,
            .e_lookup_associated,
            .e_lookup_required,
            .e_list,
            .e_empty_list,
            .e_tuple,
            .e_match,
            .e_if,
            .e_call,
            .e_record,
            .e_empty_record,
            .e_block,
            .e_tag,
            .e_nominal,
            .e_nominal_external,
            .e_zero_argument_tag,
            .e_closure,
            .e_lambda,
            .e_binop,
            .e_unary_minus,
            .e_field_access,
            .e_method_call,
            .e_dispatch_call,
            .e_interpolation,
            .e_structural_eq,
            .e_structural_hash,
            .e_method_eq,
            .e_tuple_access,
            .e_runtime_error,
            .e_crash,
            .e_dbg,
            .e_expect_err,
            .e_expect,
            .e_ellipsis,
            .e_anno_only,
            .e_derived_method,
            .e_return,
            .e_break,
            .e_for,
            .e_hosted_lambda,
            .e_run_low_level,
            => null,
        };
    }

    /// A static call of a method (`T.m(x)`) is a call of the method it names.
    fn isStaticCall(expr: CIR.Expr) bool {
        return expr == .e_type_method_call or expr == .e_type_dispatch_call;
    }

    fn push(self: *Walker, expr_idx: CIR.Expr.Idx) Allocator.Error!void {
        try self.stack.append(self.gpa, expr_idx);
    }

    fn pushSpan(self: *Walker, span: CIR.Expr.Span) Allocator.Error!void {
        try self.stack.appendSlice(self.gpa, self.cir.store.sliceExpr(span));
    }

    /// Push each child expression that runs when `expr_idx` runs, as
    /// `DependencyGraph.collectNameReferences` enumerates them.
    fn pushChildren(self: *Walker, expr_idx: CIR.Expr.Idx) Allocator.Error!void {
        const cir = self.cir;
        switch (cir.store.getExpr(expr_idx)) {
            .e_call => |call| {
                try self.callees.put(self.gpa, call.func, expr_idx);
                try self.push(call.func);
                try self.pushSpan(call.args);
            },
            .e_type_method_call => |call| try self.pushSpan(call.args),
            .e_type_dispatch_call => |call| try self.pushSpan(call.args),
            .e_lambda => |lambda| try self.push(lambda.body),
            .e_closure => |closure| try self.push(closure.lambda_idx),
            .e_if => |if_expr| {
                try self.push(if_expr.final_else);
                for (cir.store.sliceIfBranches(if_expr.branches)) |branch_idx| {
                    const branch = cir.store.getIfBranch(branch_idx);
                    try self.push(branch.cond);
                    try self.push(branch.body);
                }
            },
            .e_match => |match_expr| {
                try self.push(match_expr.cond);
                for (cir.store.sliceMatchBranches(match_expr.branches)) |branch_idx| {
                    const branch = cir.store.getMatchBranch(branch_idx);
                    if (branch.guard) |guard_idx| try self.push(guard_idx);
                    try self.push(branch.value);
                }
            },
            .e_list => |list| try self.pushSpan(list.elems),
            .e_record => |record| {
                if (record.ext) |ext_idx| try self.push(ext_idx);
                for (cir.store.sliceRecordFields(record.fields)) |field_idx| {
                    try self.push(cir.store.getRecordField(field_idx).value);
                }
            },
            .e_field_access => |access| try self.push(access.receiver),
            inline .e_method_call, .e_dispatch_call => |call| {
                try self.push(call.receiver);
                try self.pushSpan(call.args);
            },
            .e_interpolation => |interpolation| {
                try self.push(interpolation.first);
                try self.pushSpan(interpolation.parts);
            },
            .e_structural_eq => |eq| {
                try self.push(eq.lhs);
                try self.push(eq.rhs);
            },
            .e_structural_hash => |h| {
                try self.push(h.hasher);
                try self.push(h.value);
            },
            .e_method_eq => |eq| {
                try self.push(eq.lhs);
                try self.push(eq.rhs);
            },
            .e_tuple_access => |tuple_access| try self.push(tuple_access.tuple),
            .e_tuple => |tuple| try self.pushSpan(tuple.elems),
            .e_binop => |binop| {
                try self.push(binop.lhs);
                try self.push(binop.rhs);
            },
            .e_unary_minus => |unop| try self.push(unop.expr),
            .e_block => |block| {
                for (cir.store.sliceStatements(block.stmts)) |stmt_idx| {
                    switch (cir.store.getStatement(stmt_idx)) {
                        .s_decl => |decl| try self.push(decl.expr),
                        .s_var => |var_stmt| try self.push(var_stmt.expr),
                        .s_var_uninitialized => {},
                        inline .s_reassign, .s_dbg, .s_expr => |stmt| try self.push(stmt.expr),
                        .s_expect => |expect| try self.push(expect.body),
                        .s_for => |for_stmt| {
                            try self.push(for_stmt.expr);
                            try self.push(for_stmt.body);
                        },
                        .s_while => |while_stmt| {
                            try self.push(while_stmt.cond);
                            try self.push(while_stmt.body);
                        },
                        .s_infinite_loop => |loop_stmt| {
                            try self.push(loop_stmt.cond);
                            try self.push(loop_stmt.body);
                        },
                        .s_breakable_loop => |loop_stmt| {
                            try self.push(loop_stmt.cond);
                            try self.push(loop_stmt.body);
                        },
                        .s_return => |ret| try self.push(ret.expr),
                        .s_runtime_error => |runtime_error| try self.pushSpan(runtime_error.evaluated),
                        .s_import, .s_alias_decl, .s_nominal_decl, .s_where_alias_decl, .s_type_anno, .s_type_var_alias, .s_crash, .s_break => {},
                    }
                }
                try self.push(block.final_expr);
            },
            .e_tag => |tag| try self.pushSpan(tag.args),
            .e_nominal => |nominal| {
                // An omitted defaulted field is computed at this construction,
                // so its default expression runs here.
                var omissions = can.default_omissions.omittedDefaults(cir, nominal.nominal_type_decl, nominal.backing_expr);
                while (omissions.next()) |omitted| {
                    const entry = try self.seen_defaults.getOrPut(self.gpa, omitted.default_expr);
                    if (entry.found_existing) continue;
                    try self.push(omitted.default_expr);
                }
                try self.push(nominal.backing_expr);
            },
            // An imported type's defaults are in its own module. Only the
            // supplied values are this module's code.
            .e_nominal_external => |nominal| try self.push(nominal.backing_expr),
            .e_deferred_import_ref => |deferred| {
                if (deferred.backing) |backing| try self.push(backing.expr);
            },
            .e_run_low_level => |run_ll| try self.pushSpan(run_ll.args),
            .e_dbg => |dbg| try self.push(dbg.expr),
            .e_expect_err => |expect_err| try self.push(expect_err.expr),
            .e_expect => |expect| try self.push(expect.body),
            // `ret.lambda` refers back to the enclosing lambda. It is not a child.
            .e_return => |ret| try self.push(ret.expr),
            .e_for => |for_expr| {
                try self.push(for_expr.expr);
                try self.push(for_expr.body);
            },
            .e_runtime_error => |runtime_error| try self.pushSpan(runtime_error.evaluated),
            .e_break,
            .e_num,
            .e_frac_f32,
            .e_frac_f64,
            .e_dec,
            .e_dec_small,
            .e_num_from_numeral,
            .e_typed_int,
            .e_typed_frac,
            .e_typed_num_from_numeral,
            .e_str,
            .e_str_segment,
            .e_bytes_literal,
            .e_empty_list,
            .e_empty_record,
            .e_zero_argument_tag,
            .e_ellipsis,
            .e_anno_only,
            .e_derived_method,
            .e_hosted_lambda,
            .e_lookup_local,
            .e_lookup_external,
            .e_lookup_associated_local,
            .e_lookup_associated,
            .e_lookup_associated_resolved,
            .e_lookup_required,
            .e_crash,
            => {},
        }
    }
};

/// Compute the module's reify-only definitions, the violations of its roots,
/// and the expressions that reach code only reified code can use.
pub fn compute(gpa: Allocator, cir: *ModuleEnv, input: Input) Allocator.Error!Result {
    const defs = cir.store.sliceDefs(cir.all_defs);

    var expects: std.ArrayListUnmanaged(CIR.Statement.Idx) = .empty;
    defer expects.deinit(gpa);
    for (cir.store.sliceStatements(cir.all_statements)) |stmt_idx| {
        if (cir.store.getStatement(stmt_idx) == .s_expect) try expects.append(gpa, stmt_idx);
    }

    var walker = Walker{ .gpa = gpa, .cir = cir, .input = input };
    defer walker.deinit();
    try walker.init(defs);

    // Each owner's edges are contiguous, in walk order.
    const owner_count = defs.len + expects.items.len;
    var owner_edges_start = try gpa.alloc(u32, owner_count + 1);
    defer gpa.free(owner_edges_start);
    const is_root = try gpa.alloc(bool, owner_count);
    defer gpa.free(is_root);
    for (defs, 0..) |def_idx, owner| {
        owner_edges_start[owner] = @intCast(walker.edges.items.len);
        is_root[owner] = input.roots.contains(def_idx);
        try walker.walkBody(@intCast(owner), cir.store.getDef(def_idx).expr);
    }
    for (expects.items, 0..) |stmt_idx, index| {
        const owner = defs.len + index;
        owner_edges_start[owner] = @intCast(walker.edges.items.len);
        is_root[owner] = true;
        try walker.walkBody(@intCast(owner), cir.store.getStatement(stmt_idx).s_expect.body);
    }
    owner_edges_start[owner_count] = @intCast(walker.edges.items.len);

    var def_position: std.AutoHashMapUnmanaged(CIR.Def.Idx, u32) = .empty;
    defer def_position.deinit(gpa);
    for (defs, 0..) |def_idx, position| try def_position.put(gpa, def_idx, @intCast(position));

    // The round each definition that is not a root became reify-only in,
    // and its witness edge.
    const round = try gpa.alloc(?u32, owner_count);
    defer gpa.free(round);
    @memset(round, null);
    const witness_edge = try gpa.alloc(u32, owner_count);
    defer gpa.free(witness_edge);

    // Round 0: the definitions with an edge to an intrinsic, or to a
    // reify-only definition of another module.
    for (0..owner_count) |owner| {
        if (is_root[owner]) continue;
        for (owner_edges_start[owner]..owner_edges_start[owner + 1]) |edge_index| {
            if (!edgeReachesSeed(input, cir, walker.edges.items[edge_index].target)) continue;
            round[owner] = 0;
            witness_edge[owner] = @intCast(edge_index);
            break;
        }
    }
    // Round n: the definitions with an edge to a definition of this module
    // that became reify-only in an earlier round.
    var current: u32 = 1;
    var changed = true;
    while (changed) : (current += 1) {
        changed = false;
        for (0..owner_count) |owner| {
            if (is_root[owner] or round[owner] != null) continue;
            for (owner_edges_start[owner]..owner_edges_start[owner + 1]) |edge_index| {
                const target_round = localRound(cir, &def_position, round, walker.edges.items[edge_index].target) orelse continue;
                if (target_round >= current) continue;
                round[owner] = current;
                witness_edge[owner] = @intCast(edge_index);
                changed = true;
                break;
            }
        }
    }

    var result = Result{};
    errdefer result.deinit(gpa);
    for (defs, 0..) |def_idx, owner| {
        if (round[owner] == null) continue;
        const edge = walker.edges.items[witness_edge[owner]];
        try result.defs.append(gpa, .{
            .owner = def_idx,
            .witness = try witnessOf(cir, edge),
            .target_env = edge.target.env,
            .via = edge.via,
        });
    }
    std.mem.sort(Entry(CIR.Def.Idx), result.defs.items, {}, struct {
        fn lessThan(_: void, a: Entry(CIR.Def.Idx), b: Entry(CIR.Def.Idx)) bool {
            return @backingInt(a.owner) < @backingInt(b.owner);
        }
    }.lessThan);

    // The violations: each edge of a root to an intrinsic or a reify-only
    // definition, once for each site and target.
    var reported: std.AutoHashMapUnmanaged(struct { CIR.Expr.Idx, *const ModuleEnv, CIR.Def.Idx }, void) = .empty;
    defer reported.deinit(gpa);
    for (0..owner_count) |owner| {
        if (!is_root[owner]) continue;
        var first: ?u32 = null;
        for (owner_edges_start[owner]..owner_edges_start[owner + 1]) |edge_index| {
            const edge = walker.edges.items[edge_index];
            if (!edgeReaches(input, cir, &def_position, round, edge.target)) continue;
            if (first == null) first = @intCast(edge_index);
            if ((try reported.getOrPut(gpa, .{ edge.site, edge.target.env, edge.target.def })).found_existing) continue;
            try result.violations.append(gpa, .{
                .site = edge.site,
                .kind = edge.kind,
                .target = edge.target,
                .method_name = edge.method_name,
                .via = edge.via,
            });
        }
        if (owner < defs.len) continue;
        const edge_index = first orelse continue;
        const edge = walker.edges.items[edge_index];
        try result.expects.append(gpa, .{
            .owner = expects.items[owner - defs.len],
            .witness = try witnessOf(cir, edge),
            .target_env = edge.target.env,
            .via = edge.via,
        });
    }
    // In source order, so the reports read top to bottom.
    std.mem.sort(Violation, result.violations.items, cir, struct {
        fn lessThan(env: *const ModuleEnv, a: Violation, b: Violation) bool {
            const a_start = env.store.getExprRegion(a.site).start.offset;
            const b_start = env.store.getExprRegion(b.site).start.offset;
            if (a_start != b_start) return a_start < b_start;
            return @backingInt(a.site) < @backingInt(b.site);
        }
    }.lessThan);

    // Each run-time edge to an intrinsic is a witness's reason or a
    // violation: none survives into lowering unreported.
    if (std.debug.runtime_safety) {
        for (walker.edges.items) |edge| {
            if (input.classify(edge.target.env, edge.target.env.store.getDef(edge.target.def)) != .intrinsic) continue;
            std.debug.assert(is_root[edge.owner] or round[edge.owner] != null);
        }
    }

    for ([_][]const Edge{ walker.edges.items, walker.described_edges.items }) |edges| {
        for (edges) |edge| {
            if (!edgeReaches(input, cir, &def_position, round, edge.target)) continue;
            try result.reaching_exprs.put(gpa, edge.expr, {});
            try result.reaching_exprs.put(gpa, edge.site, {});
        }
    }
    return result;
}

/// The round in which the target, a definition of this module, became
/// reify-only, or null when it is not reify-only or is in another module.
fn localRound(
    cir: *const ModuleEnv,
    def_position: *const std.AutoHashMapUnmanaged(CIR.Def.Idx, u32),
    round: []const ?u32,
    target: Target,
) ?u32 {
    if (target.env != cir) return null;
    const position = def_position.get(target.def) orelse return null;
    return round[position];
}

/// Whether the target is an intrinsic or a reify-only definition.
fn edgeReaches(
    input: Input,
    cir: *const ModuleEnv,
    def_position: *const std.AutoHashMapUnmanaged(CIR.Def.Idx, u32),
    round: []const ?u32,
    target: Target,
) bool {
    return edgeReachesSeed(input, cir, target) or localRound(cir, def_position, round, target) != null;
}

/// Whether a reference to `target` makes its holder reify-only without any
/// other definition of this module: the target is an intrinsic, or a
/// reify-only definition of another module.
fn edgeReachesSeed(input: Input, cir: *const ModuleEnv, target: Target) bool {
    if (input.classify(target.env, target.env.store.getDef(target.def)) == .intrinsic) return true;
    if (target.env == cir) return false;
    return target.env.reifyOnlyWitness(target.def) != null;
}

fn witnessOf(cir: *ModuleEnv, edge: Edge) Allocator.Error!Witness {
    const target_module = if (edge.target.env == @as(*const ModuleEnv, cir))
        cir.selfModuleIdentity()
    else blk: {
        const hash = edge.target.env.contentIdentityHash() orelse
            base.invariant("a checked module's import has a content identity", .{});
        if (cir.lookupModuleIdentity(hash)) |existing| break :blk existing;
        const display = try cir.insertIdent(Ident.for_text(edge.target.env.module_name));
        break :blk try cir.internModuleIdentity(hash, display);
    };
    return .{
        .kind = edge.kind,
        .region_start = edge.region.start.offset,
        .region_end = edge.region.end.offset,
        .target_module = target_module,
        .target_def = edge.target.def,
        .method_name = edge.method_name,
    };
}
