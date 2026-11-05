//! The doc comment that a hover or completion shows for a declaration.
//!
//! `doc_comments.zig` reads a doc comment from source text above an offset.
//! This module decides which declaration's comment that is, and finds the
//! module that holds it.

const std = @import("std");
const can = @import("can");
const types = @import("types");
const compile = @import("compile");
const doc_comments = @import("doc_comments.zig");
const module_envs = @import("module_envs.zig");
const lookup_target = @import("lookup_target.zig");
const cir_queries = @import("cir_queries.zig");
const scope_map = @import("scope_map.zig");
const BuildEnvHandle = @import("build_env_handle.zig").BuildEnvHandle;

const Allocator = std.mem.Allocator;
const CIR = can.CIR;
const ModuleEnv = can.ModuleEnv;
const BuildEnv = compile.BuildEnv;

/// The doc of a binding of type `type_var`: the doc comment of the
/// declaration that owns it, or, when it has none, the doc of its type.
pub fn forBinding(
    allocator: Allocator,
    build_env: *BuildEnv,
    module_env: *ModuleEnv,
    owner: scope_map.Binding.Owner,
    type_var: types.Var,
) Allocator.Error!?[]const u8 {
    if (try doc_comments.extractDocForBinding(allocator, module_env.common.source, &module_env.store, owner)) |doc| return doc;
    return try forTypeOf(allocator, build_env, module_env, type_var);
}

/// The doc of the binding that `pattern` names in the document module
/// `module_env`, as `forBinding` gives it. Null when no scope binding has the
/// pattern.
pub fn forLocalPattern(
    allocator: Allocator,
    build_env: *BuildEnv,
    handle: *BuildEnvHandle,
    module_env: *ModuleEnv,
    pattern: CIR.Pattern.Idx,
    type_var: types.Var,
) Allocator.Error!?[]const u8 {
    for (try handle.scopeBindings(module_env)) |binding| {
        if (binding.pattern_idx == pattern) return try forBinding(allocator, build_env, module_env, binding.owner, type_var);
    }
    return null;
}

/// The doc of the alias or nominal type declaration that `type_var` resolves
/// to, read from the module that declares it.
pub fn forTypeOf(allocator: Allocator, build_env: *BuildEnv, module_env: *ModuleEnv, type_var: types.Var) Allocator.Error!?[]const u8 {
    const type_owner = lookup_target.typeOwner(module_env, type_var) orelse return null;
    const owner_env = module_envs.forTypeOrigin(build_env, module_env, type_owner.origin_module, type_owner.builtin_origin) orelse return null;
    const owner_store = &owner_env.store;
    return try doc_comments.extractDocForStatement(
        allocator,
        owner_env.common.source,
        owner_store,
        owner_store.getSourceStatement(type_owner.owner),
        type_owner.owner,
    );
}

/// The doc of the binding whose name is at `offset`, as `forBinding` gives it.
pub fn forDeclarationNameAt(
    allocator: Allocator,
    build_env: *BuildEnv,
    handle: *BuildEnvHandle,
    module_env: *ModuleEnv,
    offset: u32,
    type_var: types.Var,
) Allocator.Error!?[]const u8 {
    for (try handle.scopeBindings(module_env)) |binding| {
        if (cir_queries.regionContainsOffset(module_env.store.getPatternRegion(binding.pattern_idx), offset)) {
            return try forBinding(allocator, build_env, module_env, binding.owner, type_var);
        }
    }
    return null;
}

/// The doc of what a lookup or method call refers to. A looked-up value whose
/// declaration has no doc comment shows the doc of its type.
pub fn forLookup(
    allocator: Allocator,
    handle: *BuildEnvHandle,
    ctx: lookup_target.Context,
    lookup_result: cir_queries.LookupResult,
    type_var: types.Var,
) Allocator.Error!?[]const u8 {
    const build_env = ctx.build_env;
    const module_env = ctx.module_env;
    const expr_idx = switch (lookup_result) {
        .expr => |idx| idx,
        .field_access => return null,
    };
    const target = switch (lookup_target.resolve(ctx, expr_idx)) {
        .target => |target| target,
        .unresolved, .not_a_reference => return null,
    };
    return switch (target) {
        .local => |pattern_idx| try forLocalPattern(allocator, build_env, handle, module_env, pattern_idx, type_var),
        .external => |external| try forValueNode(allocator, external.env, external.node) orelse
            try forTypeOf(allocator, build_env, module_env, type_var),
        .associated => |associated| try doc_comments.extractDocForDef(allocator, associated.env.common.source, &associated.env.store, associated.env.store.getDef(associated.def)) orelse
            try forTypeOf(allocator, build_env, module_env, type_var),
        .method => |method| try forMethod(allocator, method),
    };
}

/// The doc of the value an exposed-value node names: a def, or a name bound
/// by destructuring in a def's pattern.
pub fn forValueNode(allocator: Allocator, module_env: *ModuleEnv, value_node: u32) Allocator.Error!?[]const u8 {
    const source = module_env.common.source;
    const store = &module_env.store;
    const node_idx: CIR.Node.Idx = @fromBackingInt(@intCast(value_node));
    if (store.nodes.get(node_idx).tag == .def) {
        const def_idx: CIR.Def.Idx = @fromBackingInt(value_node);
        return try doc_comments.extractDocForDef(allocator, source, store, store.getDef(def_idx));
    }

    const binder: CIR.Pattern.Idx = @fromBackingInt(value_node);
    var binders: std.ArrayList(CIR.Pattern.Idx) = .empty;
    defer binders.deinit(allocator);
    var binder_scratch: std.ArrayList(CIR.Pattern.Idx) = .empty;
    defer binder_scratch.deinit(allocator);
    for (store.sliceDefs(module_env.all_defs)) |def_idx| {
        const def = store.getDef(def_idx);
        binders.clearRetainingCapacity();
        try can.DependencyGraph.appendPatternBinders(module_env, def.pattern, &binders, &binder_scratch, allocator);
        if (std.mem.findScalar(CIR.Pattern.Idx, binders.items, binder) != null) {
            return try doc_comments.extractDocForDef(allocator, source, store, def);
        }
    }
    return null;
}

/// The doc of the def a method call dispatches to.
pub fn forMethod(allocator: Allocator, method: lookup_target.MethodTarget) Allocator.Error!?[]const u8 {
    const env = method.env;
    return try doc_comments.extractDocForDef(allocator, env.common.source, &env.store, env.store.getDef(method.binding.def_idx));
}
