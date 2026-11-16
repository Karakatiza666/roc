//! What a name at a reifying site refers to.
//!
//! A name at a `Code` position, or the argument of `Code.prim`, is checked as
//! a `Code` value or as the parameter of `Code.prim`, not as the value it
//! names. Hover shows the definition the name refers to instead. This is the
//! only part of the server that reads the reifying records of the checked
//! module (`NodeStore.codeReificationSiteForNode`,
//! `NodeStore.isCodePrimArgument`).

const std = @import("std");
const base = @import("base");
const can = @import("can");
const types = @import("types");
const cir_queries = @import("cir_queries.zig");
const doc_comments = @import("doc_comments.zig");
const docs = @import("docs.zig");
const lookup_target = @import("lookup_target.zig");
const scope_map = @import("scope_map.zig");
const BuildEnvHandle = @import("build_env_handle.zig").BuildEnvHandle;

const Allocator = std.mem.Allocator;
const CIR = can.CIR;
const ModuleEnv = can.ModuleEnv;

/// The definition that a name at a reifying site refers to, read from the
/// module that declares it.
pub const Definition = struct {
    env: *ModuleEnv,
    /// The type var of the definition's pattern, which hover on the
    /// definition itself also shows.
    type_var: types.Var,
    doc: Doc,

    /// Where the definition's doc comment is.
    const Doc = union(enum) {
        /// A binding of `env`, which is the hovered module.
        binding: scope_map.Binding.Owner,
        /// An exposed-value node of `env`.
        value_node: u32,
        /// A binding with no declaration of its own.
        none,
    };
};

/// The lookup expression of `lookup_result_opt` when the checker recorded it
/// as a reference at a reifying site: a name at a `Code` position, or the
/// argument of a `Code.prim` call.
pub fn referenceAt(module_env: *ModuleEnv, lookup_result_opt: ?cir_queries.LookupResult) ?CIR.Expr.Idx {
    const lookup_result = lookup_result_opt orelse return null;
    const expr_idx = switch (lookup_result) {
        .expr => |idx| idx,
        .field_access => return null,
    };
    const node_idx = ModuleEnv.nodeIdxFrom(expr_idx);
    const store = &module_env.store;
    if (store.isCodePrimArgument(node_idx)) return expr_idx;
    const site = store.codeReificationSiteForNode(node_idx) orelse return null;
    return switch (site.kind) {
        // A name of a value at a `Code` position is checked as `Code`, as a
        // named function is.
        .named_function, .value => expr_idx,
        .inline_lambda, .template, .template_call, .template_callee => null,
    };
}

/// The definition that the reference `expr_idx` at a reifying site names, or
/// null when the build does not have its module. The checker accepts only
/// lookups of definitions there.
pub fn definition(
    handle: *BuildEnvHandle,
    ctx: lookup_target.Context,
    expr_idx: CIR.Expr.Idx,
) Allocator.Error!?Definition {
    const target = switch (lookup_target.resolve(ctx, expr_idx)) {
        .target => |target| target,
        .unresolved => return null,
        .not_a_reference => base.invariant("compiler invariant violated: a reference at a reifying site is not a lookup of a definition", .{}),
    };
    switch (target) {
        .local => |pattern_idx| {
            for (try handle.scopeBindings(ctx.module_env)) |binding| {
                if (binding.pattern_idx != pattern_idx) continue;
                return .{ .env = ctx.module_env, .type_var = ModuleEnv.varFrom(pattern_idx), .doc = .{ .binding = binding.owner } };
            }
            return .{ .env = ctx.module_env, .type_var = ModuleEnv.varFrom(pattern_idx), .doc = .none };
        },
        .external => |external| {
            const target_env = external.env;
            const node_idx: CIR.Node.Idx = @fromBackingInt(@intCast(external.node));
            // The node is a def, or a name bound by destructuring in a def's pattern.
            const pattern_idx: CIR.Pattern.Idx = if (target_env.store.nodes.get(node_idx).tag == .def)
                target_env.store.getDef(@fromBackingInt(external.node)).pattern
            else
                @fromBackingInt(external.node);
            return .{ .env = target_env, .type_var = ModuleEnv.varFrom(pattern_idx), .doc = .{ .value_node = external.node } };
        },
        .associated => |associated| {
            const def = associated.env.store.getDef(associated.def);
            return .{ .env = associated.env, .type_var = ModuleEnv.varFrom(def.pattern), .doc = .{ .value_node = @backingInt(associated.def) } };
        },
        .method => base.invariant("compiler invariant violated: a reference at a reifying site is not a lookup of a definition", .{}),
    }
}

/// The doc comment of the definition a reifying site names. A definition
/// without one has no doc here: the doc of its type is not shown.
pub fn definitionDoc(allocator: Allocator, def: Definition) Allocator.Error!?[]const u8 {
    const target_env = def.env;
    return switch (def.doc) {
        .binding => |owner| try doc_comments.extractDocForBinding(allocator, target_env.common.source, &target_env.store, owner),
        .value_node => |node| try docs.forValueNode(allocator, target_env, node),
        .none => null,
    };
}
