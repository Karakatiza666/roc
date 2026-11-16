//! `textDocument/hover`: find what the name at an offset is, then render its
//! markdown. The caller maps the returned region to the document.

const std = @import("std");
const base = @import("base");
const can = @import("can");
const types = @import("types");
const cir_queries = @import("cir_queries.zig");
const module_lookup = @import("module_lookup.zig");
const lookup_target = @import("lookup_target.zig");
const anno_targets = @import("anno_targets.zig");
const reify_sites = @import("reify_sites.zig");
const docs = @import("docs.zig");
const doc_comments = @import("doc_comments.zig");
const BuildEnvHandle = @import("build_env_handle.zig").BuildEnvHandle;

const Allocator = std.mem.Allocator;
const ModuleEnv = can.ModuleEnv;
const Region = base.Region;

/// Hover allocates, and writes types with a `TypeWriter`.
pub const Error = Allocator.Error || error{WriteFailed};

/// The badge that hover and documentation show on an intrinsic.
const intrinsic_badge = "intrinsic: no Roc body";

/// A rendered hover over `region` of the document's module.
pub const Hover = struct {
    /// Owned by the caller.
    markdown: []u8,
    region: Region,
};

/// A value hover: the expression at the offset, and the lookup there if any.
const Value = struct {
    region: Region,
    type_var: types.Var,
    lookup: ?cir_queries.LookupResult,
    offset: u32,
};

/// What the name at an offset is.
const Target = union(enum) {
    /// The name on a type annotation line.
    annotation_name: cir_queries.AnnotationName,
    /// A type name that refers to an alias or nominal declaration.
    type_decl: anno_targets.TypeTarget,
    /// A record field label or a where-clause method name.
    member: anno_targets.MemberTarget,
    /// The name in a method call.
    method: lookup_target.MethodTarget,
    /// A name at a reifying site, shown as the definition it names.
    reifying: struct { value: Value, definition: reify_sites.Definition },
    /// Any other expression.
    value: Value,
};

/// The hover for the name at `offset` in `ctx.module_env`.
pub fn at(allocator: Allocator, handle: *BuildEnvHandle, ctx: lookup_target.Context, offset: u32) Error!?Hover {
    const target = (try classify(handle, ctx, offset)) orelse return null;
    return try render(allocator, handle, ctx, target);
}

fn classify(handle: *BuildEnvHandle, ctx: lookup_target.Context, offset: u32) Allocator.Error!?Target {
    const module_env = ctx.module_env;

    // The name on an annotation line has no CIR node of its own.
    if (cir_queries.findAnnotationNameAtOffset(module_env, offset)) |name| return .{ .annotation_name = name };

    // Names in the header and body of a type declaration. A type variable
    // alias has no declaration text of its own.
    if (anno_targets.at(ctx, offset)) |found| switch (found) {
        .decl => |decl| if (module_lookup.typeDeclParts(decl.env.store.getSourceStatement(decl.decl)) != null) return .{ .type_decl = decl },
        .member => |member| return .{ .member = member },
    };

    const result = cir_queries.findTypeAtOffset(module_env, offset) orelse return null;

    // Prefer lookup expression semantics when hovering over identifiers in
    // calls (e.g. `multiply(…)`): callers expect the callee's function type
    // and docs, not the enclosing call expression's return type.
    var lookup = cir_queries.findLookupNoWiderThan(module_env, offset, result.region);
    if (lookup == null and result.region.start.offset != offset) {
        lookup = cir_queries.findLookupNoWiderThan(module_env, result.region.start.offset, result.region);
    }

    // The name in a method call shows the method it dispatches to.
    if (lookup) |found| if (methodAt(ctx, found, offset)) |method| return .{ .method = method };

    const value = Value{
        .region = result.region,
        .type_var = if (lookup) |found| found.typeVar() else result.type_var,
        .lookup = lookup,
        .offset = offset,
    };

    // A name at a reifying site is typed as a `Code` or as the parameter
    // of `Code.prim`. Hover shows the definition it names instead.
    if (reify_sites.referenceAt(module_env, lookup)) |expr_idx| {
        const definition = (try reify_sites.definition(handle, ctx, expr_idx)) orelse return null;
        return .{ .reifying = .{ .value = value, .definition = definition } };
    }
    return .{ .value = value };
}

/// The method a method call names, when `offset` is on its name.
fn methodAt(ctx: lookup_target.Context, lookup: cir_queries.LookupResult, offset: u32) ?lookup_target.MethodTarget {
    const expr_idx = switch (lookup) {
        .expr => |idx| idx,
        .field_access => return null,
    };
    const method = switch (lookup_target.resolve(ctx, expr_idx)) {
        .target => |target| switch (target) {
            .method => |method| method,
            .local, .external, .associated => return null,
        },
        .unresolved, .not_a_reference => return null,
    };
    if (!cir_queries.regionContainsOffset(method.name_region, offset)) return null;
    return method;
}

fn render(allocator: Allocator, handle: *BuildEnvHandle, ctx: lookup_target.Context, target: Target) Error!Hover {
    const module_env = ctx.module_env;
    switch (target) {
        .annotation_name => |name| {
            // The type and doc that hover on the definition line shows.
            const type_var = ModuleEnv.varFrom(name.pattern);
            const documentation = try docs.forLocalPattern(allocator, ctx.build_env, handle, module_env, name.pattern, type_var);
            defer if (documentation) |doc| allocator.free(doc);

            var is_intrinsic = false;
            for (module_env.store.sliceDefs(module_env.all_defs)) |def_idx| {
                const def = module_env.store.getDef(def_idx);
                if (def.pattern == name.pattern) is_intrinsic = module_env.isIntrinsicDef(def);
            }
            return try typeHover(allocator, module_env, type_var, documentation, is_intrinsic, name.region);
        },
        .type_decl => |decl| {
            const store = &decl.env.store;
            const stmt = store.getSourceStatement(decl.decl);
            const declaration = anno_targets.declarationText(decl.env, module_lookup.typeDeclParts(stmt).?);
            const documentation = try doc_comments.extractDocForStatement(allocator, decl.env.common.source, store, stmt, decl.decl);
            defer if (documentation) |doc| allocator.free(doc);
            return .{ .markdown = try markdown(allocator, documentation, declaration, false), .region = decl.region };
        },
        .member => |member| {
            // The member as written, and the doc comment above it.
            const text = module_env.common.source[member.text.start.offset..member.text.end.offset];
            const documentation = try doc_comments.extractDocCommentBefore(allocator, module_env.common.source, member.text.start.offset);
            defer if (documentation) |doc| allocator.free(doc);
            return .{ .markdown = try markdown(allocator, documentation, text, false), .region = member.label };
        },
        .method => |method| {
            const documentation = try docs.forMethod(allocator, method);
            defer if (documentation) |doc| allocator.free(doc);
            const is_intrinsic = method.env.isIntrinsicDef(method.env.store.getDef(method.binding.def_idx));
            return try typeHover(allocator, method.env, ModuleEnv.varFrom(method.binding.type_node_idx), documentation, is_intrinsic, method.name_region);
        },
        .reifying => |reifying| {
            const documentation = try reify_sites.definitionDoc(allocator, reifying.definition);
            defer if (documentation) |doc| allocator.free(doc);
            const is_intrinsic = hoveredIntrinsic(ctx, reifying.value.lookup, reifying.value.offset);
            return try typeHover(allocator, reifying.definition.env, reifying.definition.type_var, documentation, is_intrinsic, reifying.value.region);
        },
        .value => |value| {
            // With a lookup, resolve it directly to avoid region and offset
            // ambiguity around delimiters.
            const documentation = if (value.lookup) |lookup|
                try docs.forLookup(allocator, handle, ctx, lookup, value.type_var)
            else
                try docs.forDeclarationNameAt(allocator, ctx.build_env, handle, module_env, value.offset, value.type_var);
            defer if (documentation) |doc| allocator.free(doc);
            const is_intrinsic = hoveredIntrinsic(ctx, value.lookup, value.offset);
            return try typeHover(allocator, module_env, value.type_var, documentation, is_intrinsic, value.region);
        },
    }
}

/// A hover that shows `type_var` as written by `type_env`.
fn typeHover(
    allocator: Allocator,
    type_env: *ModuleEnv,
    type_var: types.Var,
    documentation: ?[]const u8,
    is_intrinsic: bool,
    region: Region,
) Error!Hover {
    var type_writer = try type_env.initTypeWriter();
    defer type_writer.deinit();
    try type_writer.write(type_var, .one_line);
    return .{ .markdown = try markdown(allocator, documentation, type_writer.get(), is_intrinsic), .region = region };
}

/// Markdown for a hover: the doc comment, then the code in a code block, then
/// the intrinsic badge.
fn markdown(allocator: Allocator, documentation: ?[]const u8, code: []const u8, is_intrinsic: bool) Allocator.Error![]u8 {
    const badge = if (is_intrinsic) "\n\n" ++ intrinsic_badge else "";
    if (documentation) |doc| {
        return std.fmt.allocPrint(allocator, "{s}\n\n```roc\n{s}\n```{s}", .{ doc, code, badge });
    }
    return std.fmt.allocPrint(allocator, "```roc\n{s}\n```{s}", .{ code, badge });
}

/// Whether the declaration that hover names is an intrinsic: the
/// declaration of the name at `offset`, or the target of the lookup or
/// method call there. Canonicalization marks an intrinsic, and the mark
/// is the only thing read.
fn hoveredIntrinsic(ctx: lookup_target.Context, lookup: ?cir_queries.LookupResult, offset: u32) bool {
    const module_env = ctx.module_env;
    const found = lookup orelse {
        for (module_env.store.sliceDefs(module_env.all_defs)) |def_idx| {
            const def = module_env.store.getDef(def_idx);
            if (!cir_queries.regionContainsOffset(module_env.store.getPatternRegion(def.pattern), offset)) continue;
            return module_env.isIntrinsicDef(def);
        }
        return false;
    };
    const expr_idx = switch (found) {
        .expr => |idx| idx,
        .field_access => return false,
    };
    return switch (lookup_target.resolve(ctx, expr_idx)) {
        .target => |target| lookup_target.isIntrinsic(ctx, target),
        .unresolved, .not_a_reference => false,
    };
}
