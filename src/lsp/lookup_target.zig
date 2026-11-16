//! What a reference in a checked module refers to.
//!
//! One dispatch over the reference forms the canonicalizer and checker leave:
//! a local lookup, an external lookup, a resolved associated item, and a
//! method or dispatch call. Hover, documentation, the intrinsic badge and
//! go-to-definition all start from a `Target`.

const std = @import("std");
const base = @import("base");
const can = @import("can");
const types = @import("types");
const compile = @import("compile");
const module_envs = @import("module_envs.zig");

const CIR = can.CIR;
const ModuleEnv = can.ModuleEnv;
const BuildEnv = compile.BuildEnv;
const Region = base.Region;

/// The module a reference is resolved from.
pub const Context = struct {
    build_env: *BuildEnv,
    module_env: *ModuleEnv,
    /// The path the build knows `module_env` by.
    module_path: []const u8,
};

/// The declaration that owns a type: an alias or a nominal type.
pub const TypeOwner = struct {
    owner: CIR.Statement.Idx,
    type_ident: base.Ident.Idx,
    origin_module: base.ModuleIdentity.Idx,
    builtin_origin: bool,
};

/// The method a call dispatches to.
pub const MethodTarget = struct {
    /// The module that declares the receiver's type and its methods.
    env: *ModuleEnv,
    owner: CIR.Statement.Idx,
    /// The method's table entry in `env`: its def and the node that holds
    /// its checked type.
    binding: ModuleEnv.MethodBinding,
    /// The method name in the calling module's source.
    name_region: Region,
};

/// What a reference refers to.
pub const Target = union(enum) {
    /// A binding of the module itself.
    local: CIR.Pattern.Idx,
    /// A value another module exposes. `node` is a def, or a name bound by
    /// destructuring in a def's pattern.
    external: struct {
        env: *ModuleEnv,
        node: u32,
        /// The lookup in the calling module's source, with its qualifier.
        region: Region,
    },
    /// A resolved associated item.
    associated: struct { env: *ModuleEnv, def: CIR.Def.Idx },
    method: MethodTarget,
};

/// The result of resolving a reference expression.
pub const Resolution = union(enum) {
    target: Target,
    /// A reference whose module or method the build does not have.
    unresolved,
    /// An expression that is not a reference.
    not_a_reference,
};

/// What the expression `expr_idx` of the context's module refers to.
pub fn resolve(ctx: Context, expr_idx: CIR.Expr.Idx) Resolution {
    const module_env = ctx.module_env;
    return switch (module_env.store.getSourceExpr(expr_idx)) {
        .e_lookup_local => |lookup| .{ .target = .{ .local = lookup.pattern_idx } },
        .e_lookup_external => |lookup| .{ .target = .{ .external = .{
            .env = module_envs.forImport(ctx.build_env, module_env, ctx.module_path, lookup.module_idx) orelse return .unresolved,
            .node = lookup.target_node_idx,
            .region = lookup.region,
        } } },
        .e_lookup_associated_resolved => |resolved| .{ .target = .{ .associated = .{
            .env = module_envs.forIdentity(ctx.build_env, module_env, resolved.module_identity) orelse return .unresolved,
            .def = resolved.target_def_idx,
        } } },
        .e_method_call => |call| methodResolution(ctx, call.receiver, call.method_name, call.method_name_region),
        .e_dispatch_call => |call| methodResolution(ctx, call.receiver, call.method_name, call.method_name_region),
        .e_num, .e_frac_f32, .e_frac_f64, .e_dec, .e_dec_small, .e_num_from_numeral, .e_typed_int, .e_typed_frac, .e_typed_num_from_numeral, .e_str_segment, .e_str, .e_bytes_literal, .e_deferred_import_ref, .e_lookup_associated_local, .e_lookup_associated, .e_lookup_required, .e_list, .e_empty_list, .e_tuple, .e_match, .e_if, .e_call, .e_record, .e_empty_record, .e_block, .e_tag, .e_nominal, .e_nominal_external, .e_zero_argument_tag, .e_closure, .e_lambda, .e_binop, .e_unary_minus, .e_field_access, .e_interpolation, .e_structural_eq, .e_structural_hash, .e_method_eq, .e_type_method_call, .e_type_dispatch_call, .e_tuple_access, .e_runtime_error, .e_crash, .e_dbg, .e_expect_err, .e_expect, .e_ellipsis, .e_anno_only, .e_derived_method, .e_return, .e_break, .e_for, .e_hosted_lambda, .e_run_low_level => .not_a_reference,
    };
}

fn methodResolution(ctx: Context, receiver: CIR.Expr.Idx, method_name: base.Ident.Idx, name_region: Region) Resolution {
    const method = resolveMethod(ctx, receiver, method_name, name_region) orelse return .unresolved;
    return .{ .target = .{ .method = method } };
}

/// The method that a call of `method_name` (an ident of the context's module)
/// on `receiver` dispatches to, found through the method table of the
/// module that declares the receiver's checked type.
pub fn resolveMethod(ctx: Context, receiver: CIR.Expr.Idx, method_name: base.Ident.Idx, name_region: Region) ?MethodTarget {
    const module_env = ctx.module_env;
    const owner = typeOwner(module_env, ModuleEnv.varFrom(receiver)) orelse return null;
    const owner_env = module_envs.forTypeOrigin(ctx.build_env, module_env, owner.origin_module, owner.builtin_origin) orelse return null;
    const owner_method_name = owner_env.common.findIdentFrom(&module_env.common, method_name) orelse return null;
    const binding = owner_env.lookupMethodBindingForOwnerConst(owner.owner, owner_method_name) orelse return null;
    return .{
        .env = owner_env,
        .owner = owner.owner,
        .binding = binding,
        .name_region = name_region,
    };
}

/// The declaration that owns `type_var`'s type, when it resolves to an alias
/// or a nominal type with a source declaration.
pub fn typeOwner(module_env: *ModuleEnv, type_var: types.Var) ?TypeOwner {
    const content = module_env.types.resolveVar(type_var).desc.content;
    if (std.meta.activeTag(content) == .alias) {
        const source_decl = content.alias.source_decl.toOptional() orelse return null;
        return .{
            .owner = @fromBackingInt(@intCast(source_decl)),
            .type_ident = content.alias.ident.ident_idx,
            .origin_module = content.alias.origin_module,
            .builtin_origin = content.alias.source_decl.originIsBuiltin(),
        };
    }
    if (std.meta.activeTag(content) != .structure or std.meta.activeTag(content.structure) != .nominal_type) return null;
    const nominal = content.structure.nominal_type;
    const source_decl = nominal.sourceDeclOptional() orelse return null;
    return .{
        .owner = @fromBackingInt(@intCast(source_decl)),
        .type_ident = nominal.ident.ident_idx,
        .origin_module = nominal.origin_module,
        .builtin_origin = nominal.originIsBuiltin(),
    };
}

/// Whether the target is an intrinsic (`ModuleEnv.isIntrinsicDef`). A local
/// binding or a destructured binder that no def binds directly is not one.
pub fn isIntrinsic(ctx: Context, target: Target) bool {
    return switch (target) {
        .local => |pattern| defIsIntrinsic(ctx.module_env, pattern),
        .external => |external| {
            const node_idx: CIR.Node.Idx = @fromBackingInt(@intCast(external.node));
            if (external.env.store.nodes.get(node_idx).tag != .def) return false;
            const def_idx: CIR.Def.Idx = @fromBackingInt(external.node);
            return external.env.isIntrinsicDef(external.env.store.getDef(def_idx));
        },
        .associated => |associated| associated.env.isIntrinsicDef(associated.env.store.getDef(associated.def)),
        .method => |method| method.env.isIntrinsicDef(method.env.store.getDef(method.binding.def_idx)),
    };
}

/// Whether the top-level def that binds `pattern` is an intrinsic.
fn defIsIntrinsic(module_env: *ModuleEnv, pattern: CIR.Pattern.Idx) bool {
    for (module_env.store.sliceDefs(module_env.all_defs)) |def_idx| {
        const def = module_env.store.getDef(def_idx);
        if (def.pattern == pattern) return module_env.isIntrinsicDef(def);
    }
    return false;
}
