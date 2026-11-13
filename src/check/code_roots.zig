//! Compile-time roots of code reification sites that read run-time values
//! (roc-reify-proposal.md section 10.1, design.md "Code Reification").
//!
//! A lambda at a `Code` position is a description, which never holds a
//! run-time value. What it reads at run time does not make its own value
//! depend on run time. This module owns what such a read becomes:
//!
//! - which hoist frame is a lambda site with run-time reads (a pending site);
//! - which call passes the pending sites below it on to what holds it;
//! - which call binds the pending sites below it as input slots, and so is a
//!   compile-time root of its own;
//! - the mark on each bound site (`CodeReificationSite.bound_call`), and on
//!   each site that no call binds, what stopped it
//!   (`CodeReificationSite.chain_stop`);
//! - the queries that pruning and root output ask about bound sites and roots.
//!
//! The checker owns the hoist frames, the pending site list and its partition
//! by frame. It calls `selectFrame` once for each hoist frame that finishes,
//! applies the result to the frame, and calls `Selection.commit` when nothing
//! below can fail. This module writes no solved type and no dispatch plan.

const std = @import("std");
const can = @import("can");
const types_mod = @import("types");
const hoist_roots = @import("can").HoistRoots;
const canonical_type_keys = @import("canonical_type_keys.zig");

const Allocator = std.mem.Allocator;
const CIR = can.CIR;
const ModuleEnv = can.ModuleEnv;
const CodeReificationSite = can.NodeStore.CodeReificationSite;
const ChainStop = CodeReificationSite.ChainStop;

/// A lambda site with run-time reads that no call has bound yet.
pub const PendingSite = struct {
    /// The lambda.
    site: CIR.Expr.Idx,
    /// The child of the frame being finished that holds the site: the lambda
    /// itself, or the last call that passed it on.
    carrier: CIR.Expr.Idx,
};

/// The pending sites of the children of one hoist frame, in the order their
/// frames finished.
pub const PendingSites = std.ArrayListUnmanaged(PendingSite);

/// What a finished hoist frame does with code reification sites.
pub const Selection = struct {
    /// The frame is a lambda site with run-time reads. It joins the pending
    /// sites of its parent.
    pending_site: bool,
    /// The frame is a call that binds the pending sites of its children as
    /// input slots.
    binds_inputs: bool,
    /// The frame is a call that gives the pending sites of its children to
    /// its parent. It is no root, and the root that binds the sites covers
    /// what it holds, so its child candidates go to its parent.
    passes_sites: bool,
    /// The run-time dependency of the frame after this selection.
    has_runtime_dependency: bool,
    /// The frame is an expression root of its own, never a binding root, and
    /// a run-time dependency of what holds it.
    self_root_only: bool,
    /// What the frame is to the pending sites of its children when it
    /// neither binds them nor passes them on, or `none`.
    chain_stop: ChainStop,
    /// The frame is the last call of the chain that `chain_stop` stops.
    /// Otherwise the chain of each site ended in its carrier.
    chain_ends_here: bool,

    /// Mark the sites the frame binds or stops, give the children's sites to
    /// the parent or remove them from `pending`, and add the frame itself
    /// when it is a pending site. Capacity for that is reserved by `selectFrame`, so
    /// this cannot fail. `expr_root_candidate` tells that the frame became
    /// an expression root candidate that reads no local binding root.
    pub fn commit(
        self: Selection,
        cir: *ModuleEnv,
        pending: *PendingSites,
        site_start: usize,
        expr: CIR.Expr.Idx,
        expr_root_candidate: bool,
    ) void {
        if (self.binds_inputs) {
            // Such a call has a root wherever its type is fixed: here, or,
            // in a generic function, at each closing use.
            const reads: CodeReificationSite.BoundReads = if (self.self_root_only and expr_root_candidate) .sites_only else .other;
            // A call that reads a run-time value outside its sites is never a
            // root. Pruning names the open type of one that is.
            const root: CodeReificationSite.BoundRoot = if (self.self_root_only) .other else .runtime_value;
            for (pending.items[site_start..]) |pending_site| {
                cir.markCodeSiteBound(ModuleEnv.nodeIdxFrom(pending_site.site), ModuleEnv.nodeIdxFrom(expr), reads, root);
            }
        }
        if (self.chain_stop != .none) {
            for (pending.items[site_start..]) |pending_site| {
                const end = if (self.chain_ends_here) expr else pending_site.carrier;
                cir.markCodeSiteStopped(ModuleEnv.nodeIdxFrom(pending_site.site), self.chain_stop, ModuleEnv.nodeIdxFrom(end));
            }
        }
        if (self.passes_sites) {
            for (pending.items[site_start..]) |*pending_site| pending_site.carrier = expr;
        } else {
            pending.shrinkRetainingCapacity(site_start);
        }
        if (self.pending_site) pending.appendAssumeCapacity(.{ .site = expr, .carrier = expr });
    }
};

/// Select what the hoist frame of `expr` does with code reification sites.
/// `pending[site_start..]` are the pending sites of its children.
/// `binding_rhs` tells that the frame is the right side of a binding, and
/// `has_parent` that a frame holds it.
pub fn selectFrame(
    gpa: Allocator,
    cir: *const ModuleEnv,
    types: *const types_mod.Store,
    pending: *PendingSites,
    site_start: usize,
    expr: CIR.Expr.Idx,
    has_runtime_dependency: bool,
    binding_rhs: bool,
    has_parent: bool,
) Allocator.Error!Selection {
    var runtime_dependency = has_runtime_dependency;
    var binds_inputs = false;
    var passes_sites = false;
    var chain_stop: ChainStop = .none;
    var chain_ends_here = false;
    const sites = pending.items[site_start..];
    if (sites.len != 0) {
        // Only a call that takes each site, or a call that passed it on, as
        // an argument or as its receiver carries the sites further.
        const carries = callCarriesSites(cir, expr, sites);
        // A call whose result is a `Code.Bound`, or a nominal type built on
        // it, binds what its sites read at run time as input slots: the call is a root of its own, evaluated
        // while the compiler runs, and the value the program reads is that
        // root's result with the run-time values the site lowering adds, so
        // what holds the call depends on run time.
        binds_inputs = carries and try exprIsCodeBound(gpa, cir, types, expr);
        // Any other call gives the sites to what holds it, unless it is the
        // right side of a binding: a site never follows a binder.
        passes_sites = carries and !binds_inputs and !binding_rhs and has_parent;
        // Any other holder depends on run time as it always did, and the
        // walk refuses the read.
        if (!binds_inputs and !passes_sites) {
            runtime_dependency = true;
            chain_stop = if (carries and binding_rhs) .binding else stopKind(cir, expr);
            chain_ends_here = carries;
        }
    }
    const pending_site = runtime_dependency and isInlineSite(cir, expr);
    if (pending_site) {
        try pending.ensureUnusedCapacity(gpa, 1);
        runtime_dependency = false;
    }
    return .{
        .pending_site = pending_site,
        .binds_inputs = binds_inputs,
        .passes_sites = passes_sites,
        .has_runtime_dependency = runtime_dependency,
        .self_root_only = binds_inputs and !runtime_dependency,
        .chain_stop = chain_stop,
        .chain_ends_here = chain_ends_here,
    };
}

/// What `expr` is to the pending sites it stops, other than the right side
/// of a binding.
fn stopKind(cir: *const ModuleEnv, expr: CIR.Expr.Idx) ChainStop {
    return switch (cir.store.getExpr(expr)) {
        .e_if, .e_match => .branch,
        .e_record, .e_tuple, .e_list, .e_tag, .e_zero_argument_tag, .e_nominal, .e_nominal_external => .value,
        .e_anno_only,
        .e_binop,
        .e_block,
        .e_break,
        .e_bytes_literal,
        .e_call,
        .e_closure,
        .e_crash,
        .e_dbg,
        .e_dec,
        .e_dec_small,
        .e_derived_method,
        .e_dispatch_call,
        .e_ellipsis,
        .e_empty_list,
        .e_empty_record,
        .e_expect,
        .e_expect_err,
        .e_field_access,
        .e_for,
        .e_frac_f32,
        .e_frac_f64,
        .e_hosted_lambda,
        .e_interpolation,
        .e_lambda,
        .e_lookup_associated,
        .e_lookup_associated_local,
        .e_lookup_associated_resolved,
        .e_lookup_external,
        .e_lookup_local,
        .e_lookup_required,
        .e_method_call,
        .e_method_eq,
        .e_num,
        .e_num_from_numeral,
        .e_return,
        .e_run_low_level,
        .e_runtime_error,
        .e_str,
        .e_str_segment,
        .e_structural_eq,
        .e_structural_hash,
        .e_tuple_access,
        .e_type_dispatch_call,
        .e_type_method_call,
        .e_typed_frac,
        .e_typed_int,
        .e_typed_num_from_numeral,
        .e_unary_minus,
        => .end,
        .e_deferred_import_ref => unreachable, // import resolution replaced every deferred import reference before checking
    };
}

/// Whether `expr` is a lambda written at a `Code` position whose run-time
/// reads a call binds as input slots, or a value at a `Code` position that a
/// call binds as one input slot.
pub fn isBoundSite(cir: *const ModuleEnv, expr: CIR.Expr.Idx) bool {
    const site = cir.codeReificationSiteForNode(ModuleEnv.nodeIdxFrom(expr)) orelse return false;
    return (site.kind == .inline_lambda or site.kind == .value) and site.bound_call != CodeReificationSite.no_bound_call;
}

/// Whether `expr` is a value written at a `Code` position (R12).
pub fn isValueSite(cir: *const ModuleEnv, expr: CIR.Expr.Idx) bool {
    const site = cir.codeReificationSiteForNode(ModuleEnv.nodeIdxFrom(expr)) orelse return false;
    return site.kind == .value;
}

/// Whether a selected root is a call that binds the run-time reads of a lambda
/// site as input slots. The program reads such a call only through its root,
/// so the root is part of what the program means, at any depth.
pub fn rootBindsInputs(cir: *const ModuleEnv, root: hoist_roots.SelectedHoistedRoot) bool {
    return root.body == .expr and root.pattern == null and exprBindsInputs(cir, root.expr);
}

/// Whether `expr` is a call that binds the run-time reads of a lambda site as
/// input slots. The program reads its root only through the bound-call
/// lowering, at the type publication fixed for the call, so no use relates
/// the callables of its value: it is a context-free compile-time request,
/// evaluated, and its refusals reported, with the module's roots.
pub fn exprBindsInputs(cir: *const ModuleEnv, expr: CIR.Expr.Idx) bool {
    return cir.codeSiteBindsCall(ModuleEnv.nodeIdxFrom(expr));
}

/// Whether a selected root's stored value may hold functions that its
/// concrete type fixes. A root that binds inputs may: the program reads its
/// value only through the bound-call lowering at that one call, so no other
/// reader copies it into independently restored callables (design.md
/// "Checking Effects And Const Roots").
pub fn rootValueMayHoldFunctions(cir: *const ModuleEnv, root: hoist_roots.SelectedHoistedRoot) bool {
    return rootBindsInputs(cir, root);
}

/// Whether `expr` is a lambda or a value written at a `Code` position: a site
/// whose run-time reads a call can bind as input slots.
fn isInlineSite(cir: *const ModuleEnv, expr: CIR.Expr.Idx) bool {
    const site = cir.codeReificationSiteForNode(ModuleEnv.nodeIdxFrom(expr)) orelse return false;
    return site.kind == .inline_lambda or site.kind == .value;
}

/// Whether `expr` is a call that holds the carrier of each of `sites` as an
/// argument or as its receiver.
fn callCarriesSites(cir: *const ModuleEnv, expr: CIR.Expr.Idx, sites: []const PendingSite) bool {
    const receiver: ?CIR.Expr.Idx, const args: CIR.Expr.Span = switch (cir.store.getExpr(expr)) {
        .e_call => |call| .{ null, call.args },
        .e_method_call => |call| .{ call.receiver, call.args },
        .e_dispatch_call => |call| .{ call.receiver, call.args },
        .e_type_method_call => |call| .{ null, call.args },
        .e_type_dispatch_call => |call| .{ null, call.args },
        .e_anno_only,
        .e_binop,
        .e_block,
        .e_break,
        .e_bytes_literal,
        .e_closure,
        .e_crash,
        .e_dbg,
        .e_dec,
        .e_dec_small,
        .e_derived_method,
        .e_ellipsis,
        .e_empty_list,
        .e_empty_record,
        .e_expect,
        .e_expect_err,
        .e_field_access,
        .e_for,
        .e_frac_f32,
        .e_frac_f64,
        .e_hosted_lambda,
        .e_if,
        .e_interpolation,
        .e_lambda,
        .e_list,
        .e_lookup_associated,
        .e_lookup_associated_local,
        .e_lookup_associated_resolved,
        .e_lookup_external,
        .e_lookup_local,
        .e_lookup_required,
        .e_match,
        .e_method_eq,
        .e_nominal,
        .e_nominal_external,
        .e_num,
        .e_num_from_numeral,
        .e_record,
        .e_return,
        .e_run_low_level,
        .e_runtime_error,
        .e_str,
        .e_str_segment,
        .e_structural_eq,
        .e_structural_hash,
        .e_tag,
        .e_tuple,
        .e_tuple_access,
        .e_typed_frac,
        .e_typed_int,
        .e_typed_num_from_numeral,
        .e_unary_minus,
        .e_zero_argument_tag,
        => return false,
        .e_deferred_import_ref => unreachable, // import resolution replaced every deferred import reference before checking
    };
    const arg_exprs = cir.store.sliceExpr(args);
    for (sites) |pending_site| {
        if (receiver != null and receiver.? == pending_site.carrier) continue;
        const is_arg = for (arg_exprs) |arg| {
            if (arg == pending_site.carrier) break true;
        } else false;
        if (!is_arg) return false;
    }
    return true;
}

/// Whether the solved type of `expr` is the opt-in of a call that binds
/// inputs: the builtin `Code.Bound`, or a nominal type whose backing, read
/// through aliases and further nominals, is `Code.Bound` (R5 option A',
/// design.md "Code Reification"). Only the whole type counts: a type that
/// holds such a type in a tag, a field or a list item is no opt-in.
fn exprIsCodeBound(gpa: Allocator, cir: *const ModuleEnv, types: *const types_mod.Store, expr: CIR.Expr.Idx) Allocator.Error!bool {
    // One entry for each nominal declaration entered: its formals, and the
    // arguments the application gave them, which belong to the entry below.
    const Scope = struct { formals: types_mod.Var.SafeList.Range, args: types_mod.Var.SafeList.Range };
    var scopes: std.ArrayListUnmanaged(Scope) = .empty;
    defer scopes.deinit(gpa);
    var current = ModuleEnv.varFrom(expr);
    var guard = types_mod.debug.IterationGuard.init("exprIsCodeBound");
    while (true) {
        guard.tick();
        const resolved = types.resolveVar(current);
        switch (resolved.desc.content) {
            .structure => |structure| switch (structure) {
                .nominal_type => |nominal| {
                    if (nominal.originIsBuiltin() and nominal.ident.ident_idx.eql(cir.idents.builtin_code_bound)) return true;
                    // Every nominal the checker makes names its declaration.
                    const decl = types.getNominalDecl(types.lookupNominalDecl(nominal).?);
                    // The checker reported the invalid declaration.
                    if (!decl.isValid()) return false;
                    try scopes.append(gpa, .{ .formals = decl.formals, .args = nominal.args });
                    current = decl.backing;
                },
                .record, .tuple, .fn_pure, .fn_effectful, .fn_unbound, .empty_record, .tag_union, .empty_tag_union => return false,
            },
            .alias => |alias| current = types.getAliasBackingVar(alias),
            // A formal of the declaration entered last stands for the
            // argument its application gave it.
            .rigid => {
                const scope = scopes.pop() orelse return false;
                const formals = types.sliceVars(scope.formals);
                const position = for (formals, 0..) |formal, index| {
                    if (types.resolveVar(formal).var_ == resolved.var_) break index;
                } else return false;
                current = types.getVarAt(scope.args, @intCast(position));
            },
            .flex, .field_presence, .err => return false,
        }
    }
}

/// The function type a bound call `expr` instantiated its callee at: its
/// arguments, its receiver included, and its result. A call is a generic
/// bound call when this type mentions a variable that a scheme around it
/// quantifies (design.md "Bound Instance Roots").
pub fn boundCallFnVar(cir: *const ModuleEnv, expr: CIR.Expr.Idx) types_mod.Var {
    return switch (cir.store.getExpr(expr)) {
        .e_call => |call| call.constraint_fn_var orelse unreachable, // a checked call has its function type
        .e_dispatch_call => |call| call.constraint_fn_var,
        .e_type_dispatch_call => |call| call.constraint_fn_var,
        // Checking gives each method call that binds inputs its dispatch.
        .e_method_call, .e_type_method_call => unreachable, // checking replaces each method call node with its dispatch call
        .e_anno_only,
        .e_binop,
        .e_block,
        .e_break,
        .e_bytes_literal,
        .e_closure,
        .e_crash,
        .e_dbg,
        .e_dec,
        .e_dec_small,
        .e_derived_method,
        .e_ellipsis,
        .e_empty_list,
        .e_empty_record,
        .e_expect,
        .e_expect_err,
        .e_field_access,
        .e_for,
        .e_frac_f32,
        .e_frac_f64,
        .e_hosted_lambda,
        .e_if,
        .e_interpolation,
        .e_lambda,
        .e_list,
        .e_lookup_associated,
        .e_lookup_associated_local,
        .e_lookup_associated_resolved,
        .e_lookup_external,
        .e_lookup_local,
        .e_lookup_required,
        .e_match,
        .e_method_eq,
        .e_nominal,
        .e_nominal_external,
        .e_num,
        .e_num_from_numeral,
        .e_record,
        .e_return,
        .e_run_low_level,
        .e_runtime_error,
        .e_str,
        .e_str_segment,
        .e_structural_eq,
        .e_structural_hash,
        .e_tag,
        .e_tuple,
        .e_tuple_access,
        .e_typed_frac,
        .e_typed_int,
        .e_typed_num_from_numeral,
        .e_unary_minus,
        .e_zero_argument_tag,
        .e_deferred_import_ref,
        => unreachable, // only a call binds inputs
    };
}

/// Whether the type of `var_` mentions a variable that the scheme rooted at
/// `scheme_root` quantifies: a generalized identity variable of both, field
/// kinds and method requirements included. A call that binds inputs and
/// mentions one is no root of its own: it binds at each closing use of its
/// function (design.md "Bound Instance Roots").
pub fn typeMentionsSchemeVars(
    gpa: Allocator,
    types: *const types_mod.Store,
    env: *const ModuleEnv,
    var_: types_mod.Var,
    scheme_root: types_mod.Var,
) Allocator.Error!bool {
    const scheme_vars = try canonical_type_keys.identityVarsFromVar(gpa, types, env, scheme_root);
    defer gpa.free(scheme_vars);
    var quantified: std.AutoHashMapUnmanaged(types_mod.Var, void) = .empty;
    defer quantified.deinit(gpa);
    for (scheme_vars) |scheme_var| {
        const resolved = types.resolveVar(scheme_var);
        if (resolved.desc.rank != .generalized) continue;
        try quantified.put(gpa, resolved.var_, {});
    }
    if (quantified.count() == 0) return false;
    const mentioned = try canonical_type_keys.identityVarsFromVar(gpa, types, env, var_);
    defer gpa.free(mentioned);
    for (mentioned) |variable| {
        if (quantified.contains(types.resolveVar(variable).var_)) return true;
    }
    return false;
}
