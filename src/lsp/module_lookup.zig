//! Module lookup utilities for LSP operations.
//!
//! This module consolidates definition/pattern search patterns that are repeated
//! throughout the LSP codebase, particularly in syntax.zig and completion/builder.zig.
//! It provides common functions for:
//! - Extracting identifiers from patterns
//! - Finding definitions by name
//! - Getting type variables for patterns
//! - Extracting statement parts

const std = @import("std");
const can = @import("can");
const base = @import("base");

const CIR = can.CIR;
const ModuleEnv = can.ModuleEnv;
const NodeStore = can.NodeStore;
const Ident = base.Ident;

/// Information about a found definition.
pub const DefinitionInfo = struct {
    /// The pattern index where the definition is bound
    pattern_idx: CIR.Pattern.Idx,
    /// The expression index (if the definition has an expression)
    expr_idx: ?CIR.Expr.Idx,
    /// The identifier for the definition
    ident_idx: Ident.Idx,
};

/// Parts extracted from a statement for common processing.
/// Used to access pattern, expression(s), and annotation from any statement type.
pub const StatementParts = struct {
    /// The pattern bound by this statement (if any)
    pattern: ?CIR.Pattern.Idx,
    /// The primary expression (if any)
    expr: ?CIR.Expr.Idx,
    /// Secondary expression for statements that have multiple (e.g., while has cond + body)
    expr2: ?CIR.Expr.Idx,
};

// Pattern Extraction Functions

/// Extract the identifier from a binding pattern.
/// Returns null for patterns that don't directly bind an identifier
/// (e.g., record destructures, literals, underscore).
pub fn extractIdentFromPattern(store: *const NodeStore, pattern_idx: CIR.Pattern.Idx) ?Ident.Idx {
    const pattern = store.getSourcePattern(pattern_idx);
    if (std.meta.activeTag(pattern) == .assign) return pattern.assign.ident;
    if (std.meta.activeTag(pattern) == .var_assign) return pattern.var_assign.ident;
    if (std.meta.activeTag(pattern) == .as) return pattern.as.ident;
    return null;
}

/// Return the binding pattern for declaration-like statements.
pub fn getDeclarationPattern(statement: CIR.Statement) ?CIR.Pattern.Idx {
    return switch (statement) {
        .s_decl => |decl| decl.pattern,
        .s_var => |var_stmt| var_stmt.pattern_idx,
        .s_var_uninitialized => |var_stmt| var_stmt.pattern_idx,
        .s_reassign,
        .s_crash,
        .s_dbg,
        .s_expr,
        .s_expect,
        .s_for,
        .s_while,
        .s_infinite_loop,
        .s_breakable_loop,
        .s_break,
        .s_return,
        .s_import,
        .s_alias_decl,
        .s_nominal_decl,
        .s_where_alias_decl,
        .s_type_anno,
        .s_type_var_alias,
        .s_runtime_error,
        => null,
    };
}

/// The pattern a statement binds new names with: a declaration's or a `for`
/// loop's. A reassignment binds no new name.
pub fn boundPattern(statement: CIR.Statement) ?CIR.Pattern.Idx {
    if (statement == .s_for) return statement.s_for.patt;
    return getDeclarationPattern(statement);
}

/// The annotation written on a value declaration.
pub fn statementAnnotation(statement: CIR.Statement) ?CIR.Annotation.Idx {
    return switch (statement) {
        inline .s_decl, .s_var, .s_var_uninitialized => |decl| decl.anno,
        .s_reassign,
        .s_crash,
        .s_dbg,
        .s_expr,
        .s_expect,
        .s_for,
        .s_while,
        .s_infinite_loop,
        .s_breakable_loop,
        .s_break,
        .s_return,
        .s_import,
        .s_alias_decl,
        .s_nominal_decl,
        .s_where_alias_decl,
        .s_type_anno,
        .s_type_var_alias,
        .s_runtime_error,
        => null,
    };
}

/// The type annotation a statement writes: a value declaration's annotation,
/// a standalone annotation, or the body of an alias or nominal declaration.
pub fn statementTypeAnno(store: *const NodeStore, statement: CIR.Statement) ?CIR.TypeAnno.Idx {
    if (statementAnnotation(statement)) |anno_idx| return store.getAnnotation(anno_idx).anno;
    return switch (statement) {
        inline .s_type_anno, .s_alias_decl, .s_nominal_decl => |type_anno| type_anno.anno,
        .s_decl,
        .s_var,
        .s_var_uninitialized,
        .s_reassign,
        .s_crash,
        .s_dbg,
        .s_expr,
        .s_expect,
        .s_for,
        .s_while,
        .s_infinite_loop,
        .s_breakable_loop,
        .s_break,
        .s_return,
        .s_import,
        .s_where_alias_decl,
        .s_type_var_alias,
        .s_runtime_error,
        => null,
    };
}

/// The where clauses written on a statement's annotation or declaration.
pub fn statementWhere(store: *const NodeStore, statement: CIR.Statement) ?CIR.WhereClause.Span {
    if (statementAnnotation(statement)) |anno_idx| return store.getAnnotation(anno_idx).where;
    return switch (statement) {
        .s_type_anno => |type_anno| type_anno.where,
        .s_where_alias_decl => |where_alias| where_alias.where,
        .s_decl,
        .s_var,
        .s_var_uninitialized,
        .s_alias_decl,
        .s_nominal_decl,
        .s_reassign,
        .s_crash,
        .s_dbg,
        .s_expr,
        .s_expect,
        .s_for,
        .s_while,
        .s_infinite_loop,
        .s_breakable_loop,
        .s_break,
        .s_return,
        .s_import,
        .s_type_var_alias,
        .s_runtime_error,
        => null,
    };
}

/// The header and body of an alias or nominal declaration.
pub const TypeDeclParts = struct {
    header: CIR.TypeHeader.Idx,
    anno: CIR.TypeAnno.Idx,
};

/// The parts of a statement that is an alias or nominal declaration.
pub fn typeDeclParts(statement: CIR.Statement) ?TypeDeclParts {
    return switch (statement) {
        inline .s_alias_decl, .s_nominal_decl => |decl| .{ .header = decl.header, .anno = decl.anno },
        .s_decl,
        .s_var,
        .s_var_uninitialized,
        .s_reassign,
        .s_crash,
        .s_dbg,
        .s_expr,
        .s_expect,
        .s_for,
        .s_while,
        .s_infinite_loop,
        .s_breakable_loop,
        .s_break,
        .s_return,
        .s_import,
        .s_where_alias_decl,
        .s_type_anno,
        .s_type_var_alias,
        .s_runtime_error,
        => null,
    };
}

/// The header of a type declaration: an alias, nominal or where-alias.
pub fn typeDeclHeader(statement: CIR.Statement) ?CIR.TypeHeader.Idx {
    return switch (statement) {
        inline .s_alias_decl, .s_nominal_decl, .s_where_alias_decl => |decl| decl.header,
        .s_decl,
        .s_var,
        .s_var_uninitialized,
        .s_reassign,
        .s_crash,
        .s_dbg,
        .s_expr,
        .s_expect,
        .s_for,
        .s_while,
        .s_infinite_loop,
        .s_breakable_loop,
        .s_break,
        .s_return,
        .s_import,
        .s_type_anno,
        .s_type_var_alias,
        .s_runtime_error,
        => null,
    };
}

// Definition Search Functions

/// The method table key of the associated item bound as `ident`: its owner
/// type and its member name. Null for a binding that is not an associated item.
pub fn associatedItemKey(module_env: *const ModuleEnv, ident: Ident.Idx) ?ModuleEnv.MethodKey {
    for (module_env.method_idents.entries.items) |entry| {
        if (entry.value.eql(ident)) return entry.key;
    }
    return null;
}

/// The name a binding is written with at its declaration: the member name of
/// an associated item, otherwise the bound name.
pub fn declaredName(module_env: *const ModuleEnv, ident: Ident.Idx) []const u8 {
    const key = associatedItemKey(module_env, ident) orelse return module_env.getIdentText(ident);
    return module_env.getIdentText(key.methodIdent());
}

/// Find a definition by name, searching through all_defs and all_statements.
/// Returns information about the first matching definition found.
pub fn findDefinitionByName(module_env: *ModuleEnv, name: []const u8) ?DefinitionInfo {
    return findDefinitionByModuleMember(module_env, module_env.module_name, name);
}

/// Find a definition by an explicit module/type name and member name.
/// This is useful for qualified definitions such as `List.append` in Builtin.roc,
/// whose containing module is `Builtin` rather than `List`.
pub fn findDefinitionByModuleMember(module_env: *ModuleEnv, module_name: []const u8, name: []const u8) ?DefinitionInfo {
    const matches_name = struct {
        fn check(ident_name: []const u8, qualifier: []const u8, member: []const u8) bool {
            if (std.mem.eql(u8, ident_name, member)) return true;
            if (qualifier.len == 0) return false;

            const qualified_len = qualifier.len + 1 + member.len;
            return ident_name.len == qualified_len and
                std.mem.startsWith(u8, ident_name, qualifier) and
                ident_name[qualifier.len] == '.' and
                std.mem.eql(u8, ident_name[qualifier.len + 1 ..], member);
        }
    }.check;

    // Search through all_defs first
    const defs_slice = module_env.store.sliceDefs(module_env.all_defs);
    for (defs_slice) |def_idx| {
        const def = module_env.store.getDef(def_idx);
        if (extractIdentFromPattern(&module_env.store, def.pattern)) |ident_idx| {
            const ident_name = module_env.getIdentText(ident_idx);
            if (matches_name(ident_name, module_name, name)) {
                return DefinitionInfo{
                    .pattern_idx = def.pattern,
                    .expr_idx = def.expr,
                    .ident_idx = ident_idx,
                };
            }
        }
    }

    // Search through all_statements
    const statements_slice = module_env.store.sliceStatements(module_env.all_statements);
    for (statements_slice) |stmt_idx| {
        const stmt = module_env.store.getSourceStatement(stmt_idx);
        const parts = getStatementParts(stmt);

        if (parts.pattern) |pattern_idx| {
            if (extractIdentFromPattern(&module_env.store, pattern_idx)) |ident_idx| {
                const ident_name = module_env.getIdentText(ident_idx);
                if (matches_name(ident_name, module_name, name)) {
                    return DefinitionInfo{
                        .pattern_idx = pattern_idx,
                        .expr_idx = parts.expr,
                        .ident_idx = ident_idx,
                    };
                }
            }
        }
    }

    return null;
}

// Module Lookup Functions

// Type Variable Functions

// Statement Parts Extraction

/// Extract the common parts from a statement (pattern, expression(s)).
/// This consolidates the repeated switch logic found throughout the LSP codebase.
/// Note: For type annotations, use getStatementAnnotation() separately.
pub fn getStatementParts(stmt: CIR.Statement) StatementParts {
    return switch (stmt) {
        .s_decl => |d| .{
            .pattern = d.pattern,
            .expr = d.expr,
            .expr2 = null,
        },

        .s_var => |d| .{
            .pattern = d.pattern_idx,
            .expr = d.expr,
            .expr2 = null,
        },
        .s_var_uninitialized => |d| .{
            .pattern = d.pattern_idx,
            .expr = null,
            .expr2 = null,
        },
        .s_reassign => |d| .{
            .pattern = d.pattern_idx,
            .expr = d.expr,
            .expr2 = null,
        },
        .s_expr => |e| .{
            .pattern = null,
            .expr = e.expr,
            .expr2 = null,
        },
        .s_for => |f| .{
            .pattern = f.patt,
            .expr = f.expr,
            .expr2 = f.body,
        },
        inline .s_while, .s_infinite_loop, .s_breakable_loop => |w| .{
            .pattern = null,
            .expr = w.cond,
            .expr2 = w.body,
        },
        .s_dbg => |d| .{
            .pattern = null,
            .expr = d.expr,
            .expr2 = null,
        },
        .s_expect => |e| .{
            .pattern = null,
            .expr = e.body,
            .expr2 = null,
        },
        .s_crash, .s_break, .s_import, .s_alias_decl, .s_nominal_decl, .s_where_alias_decl, .s_type_anno, .s_type_var_alias, .s_runtime_error => .{
            .pattern = null,
            .expr = null,
            .expr2 = null,
        },
        .s_return => |r| .{
            .pattern = null,
            .expr = r.expr,
            .expr2 = null,
        },
    };
}

// Binding Search Functions

// Iterator Helpers

/// Iterator over all definitions in a module (from both all_defs and all_statements).
pub const DefinitionIterator = struct {
    module_env: *ModuleEnv,
    defs_slice: []const CIR.Def.Idx,
    statements_slice: []const CIR.Statement.Idx,
    defs_index: usize = 0,
    statements_index: usize = 0,

    pub fn init(module_env: *ModuleEnv) DefinitionIterator {
        return .{
            .module_env = module_env,
            .defs_slice = module_env.store.sliceDefs(module_env.all_defs),
            .statements_slice = module_env.store.sliceStatements(module_env.all_statements),
        };
    }

    pub fn next(self: *DefinitionIterator) ?DefinitionInfo {
        // First iterate through defs
        while (self.defs_index < self.defs_slice.len) {
            const def_idx = self.defs_slice[self.defs_index];
            self.defs_index += 1;

            const def = self.module_env.store.getDef(def_idx);
            if (extractIdentFromPattern(&self.module_env.store, def.pattern)) |ident_idx| {
                return DefinitionInfo{
                    .pattern_idx = def.pattern,
                    .expr_idx = def.expr,
                    .ident_idx = ident_idx,
                };
            }
        }

        // Then iterate through statements
        while (self.statements_index < self.statements_slice.len) {
            const stmt_idx = self.statements_slice[self.statements_index];
            self.statements_index += 1;

            const stmt = self.module_env.store.getSourceStatement(stmt_idx);
            const parts = getStatementParts(stmt);

            if (parts.pattern) |pattern_idx| {
                if (extractIdentFromPattern(&self.module_env.store, pattern_idx)) |ident_idx| {
                    return DefinitionInfo{
                        .pattern_idx = pattern_idx,
                        .expr_idx = parts.expr,
                        .ident_idx = ident_idx,
                    };
                }
            }
        }

        return null;
    }
};

/// Create an iterator over all definitions in a module.
pub fn iterateDefinitions(module_env: *ModuleEnv) DefinitionIterator {
    return DefinitionIterator.init(module_env);
}

// Tests

test "getStatementParts returns correct parts for s_break" {
    // This is a compile-time test to verify the switch handles all cases
    const stmt = CIR.Statement{ .s_break = .{} };
    const parts = getStatementParts(stmt);
    try std.testing.expect(parts.pattern == null);
    try std.testing.expect(parts.expr == null);
    try std.testing.expect(parts.expr2 == null);
}
