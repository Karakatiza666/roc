//! What a name in a type annotation refers to.
//!
//! Hover and goto definition both ask this module. It finds a type name, a
//! record field label or a where-clause method name in:
//!   - a type declaration's header and body;
//!   - the annotation and where clauses of a top-level def or statement;
//!   - the annotation and where clauses of a statement nested anywhere in a
//!     def's body.

const base = @import("base");
const can = @import("can");
const compile = @import("compile");
const compiled_builtins = @import("compiled_builtins");
const cir_queries = @import("cir_queries.zig");
const module_envs = @import("module_envs.zig");
const module_lookup = @import("module_lookup.zig");
const lookup_target = @import("lookup_target.zig");
const CirVisitor = @import("cir_visitor.zig").CirVisitor;
const VisitAction = @import("cir_visitor.zig").VisitAction;

const CIR = can.CIR;
const ModuleEnv = can.ModuleEnv;
const BuildEnv = compile.BuildEnv;
const Region = base.Region;

/// The target at `offset` in the context's module: the declaration whose
/// header holds the offset, or what a name in an annotation there names.
pub fn at(ctx: lookup_target.Context, offset: u32) ?AnnoTarget {
    const env = ctx.build_env;
    const module_env = ctx.module_env;
    const store = &module_env.store;
    for (store.sliceStatements(module_env.all_statements)) |stmt_idx| {
        const stmt = store.getSourceStatement(stmt_idx);
        if (module_lookup.typeDeclParts(stmt)) |parts| {
            const header_region = store.getRegionAt(@fromBackingInt(@backingInt(parts.header)));
            if (cir_queries.regionContainsOffset(header_region, offset)) {
                return .{ .decl = .{ .env = module_env, .decl = stmt_idx, .region = header_region } };
            }
        }
        if (statementAnnoTargetAt(env, module_env, ctx.module_path, stmt, offset)) |found| return found;
    }
    for (store.sliceDefs(module_env.all_defs)) |def_idx| {
        const anno_idx = store.getDef(def_idx).annotation orelse continue;
        const annotation = store.getAnnotation(anno_idx);
        if (typeAnnoTargetAt(env, module_env, ctx.module_path, annotation.anno, offset)) |found| return found;
        if (annotation.where) |where| {
            if (whereTargetAt(env, module_env, ctx.module_path, where, offset)) |found| return found;
        }
    }
    return nestedTypeAnnoTargetAt(env, module_env, ctx.module_path, offset);
}

/// A type declaration that a name in a type annotation refers to.
pub const TypeTarget = struct {
    env: *ModuleEnv,
    decl: CIR.Statement.Idx,
    /// The annotation node that names the declaration.
    region: Region,
};

/// A name inside an annotation that is not a type: a record field label
/// or the method name of a where clause.
pub const MemberTarget = struct {
    /// The name.
    label: Region,
    /// The member as written, from its name to the end of its type.
    text: Region,
};

/// What a name in an annotation refers to.
pub const AnnoTarget = union(enum) {
    decl: TypeTarget,
    member: MemberTarget,
};

/// The target at `offset` in the annotation or where clauses of `stmt`.
fn statementAnnoTargetAt(
    build_env: *BuildEnv,
    module_env: *ModuleEnv,
    doc_path: []const u8,
    stmt: CIR.Statement,
    offset: u32,
) ?AnnoTarget {
    if (module_lookup.statementTypeAnno(&module_env.store, stmt)) |anno| {
        if (typeAnnoTargetAt(build_env, module_env, doc_path, anno, offset)) |target| return target;
    }
    const where = module_lookup.statementWhere(&module_env.store, stmt) orelse return null;
    return whereTargetAt(build_env, module_env, doc_path, where, offset);
}

/// The target at `offset` in a list of where clauses: the method name of
/// a clause, or a type in its signature.
fn whereTargetAt(
    build_env: *BuildEnv,
    module_env: *ModuleEnv,
    doc_path: []const u8,
    where: CIR.WhereClause.Span,
    offset: u32,
) ?AnnoTarget {
    const store = &module_env.store;
    for (store.sliceWhereClauses(where)) |clause_idx| {
        const method = switch (store.getWhereClause(clause_idx)) {
            .w_method => |w_method| w_method,
            .w_alias, .w_malformed => continue,
        };
        if (cir_queries.regionContainsOffset(method.method_name_region, offset)) {
            return .{ .member = .{
                .label = method.method_name_region,
                .text = .{ .start = store.getRegionAt(@fromBackingInt(@backingInt(clause_idx))).start, .end = store.getTypeAnnoRegion(method.anno).end },
            } };
        }
        if (typeAnnoTargetAt(build_env, module_env, doc_path, method.anno, offset)) |target| return target;
    }
    return null;
}

/// The declaration a type annotation's base names.
fn typeBaseTarget(
    build_env: *BuildEnv,
    module_env: *ModuleEnv,
    doc_path: []const u8,
    base_info: CIR.TypeAnno.LocalOrExternal,
    region: Region,
) ?AnnoTarget {
    return switch (base_info) {
        .local => |local| .{ .decl = .{ .env = module_env, .decl = local.decl_idx, .region = region } },
        .external => |ext| .{ .decl = .{
            .env = module_envs.forImport(build_env, module_env, doc_path, ext.module_idx) orelse return null,
            .decl = @fromBackingInt(ext.target_node_idx),
            .region = region,
        } },
        .external_identity => |ext| .{ .decl = .{
            .env = module_envs.forIdentity(build_env, module_env, ext.module_identity) orelse return null,
            .decl = @fromBackingInt(ext.target_node_idx),
            .region = region,
        } },
        .builtin => |builtin_type| .{ .decl = .{ .env = build_env.builtin_modules.builtin_module.env, .decl = builtinTypeDeclaration(builtin_type), .region = region } },
        .pending => base.invariant("compiler invariant violated: deferred import reference reached a stage that runs after import resolution", .{}),
    };
}

/// The Builtin module's declaration of a builtin type annotation base.
fn builtinTypeDeclaration(builtin_type: CIR.TypeAnno.Builtin) CIR.Statement.Idx {
    const builtin_indices = compiled_builtins.builtinIndices(CIR);
    inline for (CIR.builtin_type_specs) |spec| {
        const tag_name = spec.type_field[0 .. spec.type_field.len - "_type".len];
        if (@hasField(CIR.TypeAnno.Builtin, tag_name) and builtin_type == @field(CIR.TypeAnno.Builtin, tag_name)) {
            return @field(builtin_indices, spec.type_field);
        }
    }
    base.invariant("compiler invariant violated: builtin type annotation {s} has no Builtin declaration", .{@tagName(builtin_type)});
}

/// Find the type declaration named at the given offset of a type annotation.
/// This recursively walks type annotation trees to find the most specific type at the cursor.
fn typeAnnoTargetAt(
    build_env: *BuildEnv,
    module_env: *ModuleEnv,
    doc_path: []const u8,
    type_anno_idx: CIR.TypeAnno.Idx,
    target_offset: u32,
) ?AnnoTarget {
    const region = module_env.store.getTypeAnnoRegion(type_anno_idx);
    if (!cir_queries.regionContainsOffset(region, target_offset)) return null;

    const type_anno = module_env.store.getTypeAnno(type_anno_idx);
    switch (type_anno) {
        .lookup => |lookup| {
            return typeBaseTarget(build_env, module_env, doc_path, lookup.base, region);
        },
        .apply => |apply| {
            // Type with args like `List(Str)` - check args first, then the base type
            const args_slice = module_env.store.sliceTypeAnnos(apply.args);
            for (args_slice) |arg_idx| {
                if (typeAnnoTargetAt(build_env, module_env, doc_path, arg_idx, target_offset)) |result| {
                    return result;
                }
            }
            // If not in args, return the base type
            return typeBaseTarget(build_env, module_env, doc_path, apply.base, region);
        },
        .record => |rec| {
            // Check record field types
            const fields_slice = module_env.store.sliceAnnoRecordFields(rec.fields);
            for (fields_slice) |field_idx| {
                const field = module_env.store.getAnnoRecordField(field_idx);
                if (!field.is_unnamed and cir_queries.regionContainsOffset(field.label_region, target_offset)) {
                    return .{ .member = .{
                        .label = field.label_region,
                        .text = .{ .start = field.label_region.start, .end = module_env.store.getTypeAnnoRegion(field.ty).end },
                    } };
                }
                if (typeAnnoTargetAt(build_env, module_env, doc_path, field.ty, target_offset)) |result| {
                    return result;
                }
            }
            return null;
        },
        .tag_union => |tu| {
            // Check tag types
            const tags_slice = module_env.store.sliceTypeAnnos(tu.tags);
            for (tags_slice) |tag_idx| {
                if (typeAnnoTargetAt(build_env, module_env, doc_path, tag_idx, target_offset)) |result| {
                    return result;
                }
            }
            if (tu.ext) |ext_idx| {
                if (typeAnnoTargetAt(build_env, module_env, doc_path, ext_idx, target_offset)) |result| {
                    return result;
                }
            }
            return null;
        },
        .tag => |t| {
            // Check tag argument types
            const args_slice = module_env.store.sliceTypeAnnos(t.args);
            for (args_slice) |arg_idx| {
                if (typeAnnoTargetAt(build_env, module_env, doc_path, arg_idx, target_offset)) |result| {
                    return result;
                }
            }
            return null;
        },
        .@"fn" => |f| {
            // Check function argument and return types
            const args_slice = module_env.store.sliceTypeAnnos(f.args);
            for (args_slice) |arg_idx| {
                if (typeAnnoTargetAt(build_env, module_env, doc_path, arg_idx, target_offset)) |result| {
                    return result;
                }
            }
            if (typeAnnoTargetAt(build_env, module_env, doc_path, f.ret, target_offset)) |result| {
                return result;
            }
            return null;
        },
        .tuple => |t| {
            // Check tuple element types
            const elems_slice = module_env.store.sliceTypeAnnos(t.elems);
            for (elems_slice) |elem_idx| {
                if (typeAnnoTargetAt(build_env, module_env, doc_path, elem_idx, target_offset)) |result| {
                    return result;
                }
            }
            return null;
        },
        .parens => |p| {
            // Unwrap and recurse
            return typeAnnoTargetAt(build_env, module_env, doc_path, p.anno, target_offset);
        },
        .rigid_var, .rigid_var_lookup, .underscore, .malformed => {
            // These don't have type definitions to navigate to
            return null;
        },
    }
}

/// The declaration or member named by a type in an annotation, or by a
/// where clause, on a statement inside a definition's body, such as a
/// typed local in a block.
fn nestedTypeAnnoTargetAt(
    env: *BuildEnv,
    module_env: *ModuleEnv,
    doc_path: []const u8,
    offset: u32,
) ?AnnoTarget {
    const Search = struct {
        env: *BuildEnv,
        module_env: *ModuleEnv,
        doc_path: []const u8,
        offset: u32,
        result: ?AnnoTarget = null,

        fn visitStmt(search: *@This(), _: CIR.Statement.Idx, stmt: CIR.Statement) VisitAction {
            search.result = statementAnnoTargetAt(search.env, search.module_env, search.doc_path, stmt, search.offset) orelse return .continue_traversal;
            return .stop;
        }
    };
    var search = Search{ .env = env, .module_env = module_env, .doc_path = doc_path, .offset = offset };
    var visitor = CirVisitor(Search).init(&search, .{ .visit_stmt_pre = Search.visitStmt });
    for (module_env.store.sliceDefs(module_env.all_defs)) |def_idx| {
        visitor.walkExpr(&module_env.store, module_env.store.getDef(def_idx).expr);
        if (visitor.stopped) break;
    }
    return search.result;
}

/// The source of a type declaration from its name to the end of its body.
pub fn declarationText(target_env: *ModuleEnv, parts: module_lookup.TypeDeclParts) []const u8 {
    const store = &target_env.store;
    const start = store.getRegionAt(@fromBackingInt(@backingInt(parts.header))).start.offset;
    const end = store.getTypeAnnoRegion(parts.anno).end.offset;
    return target_env.common.source[start..end];
}
