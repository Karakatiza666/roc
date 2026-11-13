//! CompletionBuilder - centralized completion item building.
//!
//! This module provides a builder pattern for constructing LSP completion items.
//! It handles deduplication, type formatting, and completion item creation for:
//! - Local variables and function definitions
//! - Module names and module members
//! - Type names (for type annotations)
//! - Record fields (for dot access)
//! - Methods (for static dispatch)

const std = @import("std");
const base = @import("base");
const can = @import("can");
const types = @import("types");
const compile = @import("compile");
const Check = @import("check").Check;

const completion_handler = @import("../handlers/completion.zig");
const builtin_completion = @import("builtins.zig");
const scope_map = @import("../scope_map.zig");
const module_lookup = @import("../module_lookup.zig");
const module_envs = @import("../module_envs.zig");
const doc_comments = @import("../doc_comments.zig");
const record_row = @import("../record_row.zig");

const Allocator = std.mem.Allocator;
const CIR = can.CIR;
const ModuleEnv = can.ModuleEnv;
const BuildEnv = compile.BuildEnv;
const DebugFlags = @import("../debug.zig").DebugFlags;
const BuildEnvHandle = @import("../build_env_handle.zig").BuildEnvHandle;

const CompletionItem = completion_handler.CompletionItem;
const CompletionItemKind = completion_handler.CompletionItemKind;

const MethodOwnerLookup = struct {
    owner: CIR.Statement.Idx,
    type_name: []const u8,
    builtin_origin: bool,
    origin_module: base.ModuleIdentity.Idx,
};

fn patternIdent(pattern: CIR.Pattern) ?base.Ident.Idx {
    return switch (pattern) {
        inline .assign, .var_assign, .as => |p| p.ident,
        .applied_tag,
        .nominal,
        .nominal_external,
        .record_destructure,
        .list,
        .tuple,
        .num_literal,
        .frac_f32_literal,
        .frac_f64_literal,
        .small_dec_literal,
        .dec_literal,
        .num_from_numeral_literal,
        .str_literal,
        .str_interpolation,
        .underscore,
        .runtime_error,
        => null,
        .deferred_import_ref => base.invariant("compiler invariant violated: deferred import reference pattern reached a stage that runs after import resolution", .{}),
    };
}

fn completionKindForExpr(expr: CIR.Expr) u32 {
    const tag = std.meta.activeTag(expr);
    return if (tag == .e_closure or tag == .e_lambda or tag == .e_hosted_lambda)
        @backingInt(CompletionItemKind.function)
    else
        @backingInt(CompletionItemKind.variable);
}

/// Builder for constructing completion item lists.
/// Handles deduplication and provides methods for adding different types of completions.
pub const CompletionBuilder = struct {
    allocator: Allocator,
    /// Allocates the accepted items and every string they hold. Owned by the
    /// request, which frees them together once the response is sent.
    strings: Allocator,
    std_io: std.Io,
    items: *std.ArrayList(CompletionItem),
    /// Accepted labels of every kind but `method`, borrowing the copies in
    /// `strings`.
    seen_labels: std.StringHashMapUnmanaged(void) = .empty,
    /// Accepted method labels. After a value and a dot, `value.name` reads a
    /// field and `value.name()` calls a method, so a field and a method of one
    /// name are two items.
    seen_methods: std.StringHashMapUnmanaged(void) = .empty,
    builtin_module_env: ?*ModuleEnv,
    /// The handle owning the document module the completions are built for,
    /// which holds that module's scope map.
    module_handle: *BuildEnvHandle,
    debug: DebugFlags = .{},
    log_file: ?std.Io.File = null,
    /// The document module the completions are for. Value-dot completions
    /// offer only what this module may write after the dot.
    requester_env: ?*ModuleEnv = null,

    /// Initialize a new CompletionBuilder with debug logging. `items` and all
    /// strings in it are allocated from `strings`.
    pub fn initWithDebug(
        allocator: Allocator,
        strings: Allocator,
        std_io: std.Io,
        items: *std.ArrayList(CompletionItem),
        builtin_module_env: ?*ModuleEnv,
        module_handle: *BuildEnvHandle,
        debug: DebugFlags,
        log_file: ?std.Io.File,
    ) CompletionBuilder {
        return .{
            .allocator = allocator,
            .strings = strings,
            .std_io = std_io,
            .items = items,
            .builtin_module_env = builtin_module_env,
            .module_handle = module_handle,
            .debug = debug,
            .log_file = log_file,
        };
    }

    /// Set the document module that value-dot completions are for.
    pub fn setRequester(self: *CompletionBuilder, module_env: *ModuleEnv) void {
        self.requester_env = module_env;
    }

    /// Whether the document module may see the backing of `nominal`, a type
    /// of `store_env`'s type store. This is the checker's rule
    /// `NominalType.canLiftInner`: a `::` opaque type opens only in its own
    /// module. For a type of another module's store, the module identities
    /// are compared by content hash, as the checker matches origin modules.
    fn backingVisibleToRequester(self: *const CompletionBuilder, store_env: *ModuleEnv, nominal: types.NominalType) bool {
        if (!nominal.isOpaque()) return true;
        const requester = self.requester_env.?; // value-dot completion runs only for a document module
        if (store_env == requester) return nominal.canLiftInner(requester.selfModuleIdentity());
        const requester_hash = requester.moduleIdentityHash(requester.selfModuleIdentity());
        return std.mem.eql(u8, store_env.moduleIdentityHash(nominal.origin_module), requester_hash);
    }

    /// Clean up resources used by the builder.
    pub fn deinit(self: *CompletionBuilder) void {
        self.seen_labels.deinit(self.allocator);
        self.seen_methods.deinit(self.allocator);
    }

    /// The scope bindings of the document module `module_env`.
    pub fn scopeBindings(self: *CompletionBuilder, module_env: *ModuleEnv) Allocator.Error![]const scope_map.Binding {
        return self.module_handle.scopeBindings(module_env);
    }

    fn logDebug(self: *CompletionBuilder, comptime fmt: []const u8, args: anytype) void {
        if (!self.debug.completion) return;
        var log_file = self.log_file orelse return;
        var buffer: [256]u8 = undefined;
        const msg = std.fmt.bufPrint(&buffer, fmt, args) catch return;
        log_file.writeStreamingAll(self.std_io, msg) catch return;
        log_file.writeStreamingAll(self.std_io, "\n") catch {};
        log_file.sync(self.std_io) catch {};
    }

    /// Add a completion item, returning true if it was added (not a duplicate).
    /// A method is a duplicate only of another method of its label.
    ///
    /// The item's optional strings must be allocated from `strings`; the label
    /// may be borrowed, since an accepted label is copied there.
    pub fn addItem(self: *CompletionBuilder, item: CompletionItem) Allocator.Error!bool {
        const seen = if (item.kind == @backingInt(CompletionItemKind.method)) &self.seen_methods else &self.seen_labels;
        const gop = try seen.getOrPut(self.allocator, item.label);
        if (gop.found_existing) return false;
        errdefer seen.removeByPtr(gop.key_ptr);

        const owned_label = try self.strings.dupe(u8, item.label);
        gop.key_ptr.* = owned_label;

        var stored_item = item;
        stored_item.label = owned_label;
        try self.items.append(self.strings, stored_item);
        return true;
    }

    // Module Name Completions

    /// Add module name completions from all loaded packages/modules in BuildEnv.
    pub fn addModuleNameCompletionsFromEnv(self: *CompletionBuilder, env: *BuildEnv) Allocator.Error!void {
        // Surface builtin modules (Str, List, etc.) even when they are not
        // present in coordinator state. This keeps completions available while
        // preserving real backing data for members/types.
        try self.addBuiltinModuleNameCompletions();

        const coord = env.coordinator orelse return;
        var pkg_it = coord.packages.iterator();
        while (pkg_it.next()) |entry| {
            const pkg = entry.value_ptr.*;
            for (pkg.modules.items) |module_state| {
                const name = module_state.name;
                if (name.len == 0) continue;

                _ = try self.addItem(.{
                    .label = name,
                    .kind = @backingInt(CompletionItemKind.module),
                    .detail = null,
                });
            }
        }
    }

    /// Add module name completions from the current module's import statements.
    pub fn addModuleNameCompletions(self: *CompletionBuilder, module_env: *ModuleEnv) Allocator.Error!void {
        // Add imported module names from import statements
        const import_statements_slice = module_env.store.sliceStatements(module_env.all_statements);
        for (import_statements_slice) |stmt_idx| {
            const stmt = module_env.store.getSourceStatement(stmt_idx);
            if (stmt == .s_import) {
                const import_stmt = stmt.s_import;
                // Use alias if available, otherwise use the module name
                const name_idx = import_stmt.alias_tok orelse import_stmt.module_name_tok;
                const name = module_env.common.idents.getText(name_idx);

                if (name.len > 0) {
                    _ = try self.addItem(.{
                        .label = name,
                        .kind = @backingInt(CompletionItemKind.module),
                        .detail = null,
                    });
                }
            }
        }
    }

    // Module Member Completions

    /// Add completions for members after `qualifier.` (e.g., Str.concat).
    /// `imported_env` is the module the qualifier names, if it names one.
    pub fn addModuleMemberCompletions(
        self: *CompletionBuilder,
        env: *BuildEnv,
        qualifier: []const u8,
        imported_env: ?*ModuleEnv,
        module_env_opt: ?*ModuleEnv,
    ) Allocator.Error!void {
        if (imported_env) |target_env| {
            // Builtins are backed by a single Builtin module env, where a
            // builtin type's members are qualified by the type's name.
            const member_prefix = if (target_env == env.builtin_modules.builtin_module.env) qualifier else target_env.module_name;
            try self.addModuleMemberCompletionsFromModuleEnv(target_env, member_prefix);
            return;
        }

        // Fall back to local module env for nominal type associated values.
        // Don't require module_name to match module_env.module_name - this
        // handles Record2.ttt where Record2 is a nominal type in the current module.
        if (module_env_opt) |module_env| {
            try self.addModuleMemberCompletionsFromModuleEnv(module_env, qualifier);
        }
    }

    /// Add builtin module name completions (Str, List, Bool, etc.).
    fn addBuiltinModuleNameCompletions(self: *CompletionBuilder) Allocator.Error!void {
        // We use the builtin type list as module names, because builtin modules
        // are surfaced as top-level namespaces for completion.
        for (builtin_completion.BUILTIN_TYPES) |builtin_name| {
            _ = try self.addItem(.{
                .label = builtin_name,
                .kind = @backingInt(CompletionItemKind.module),
                .detail = null,
            });
        }
    }

    /// Add module member completions from a specific ModuleEnv.
    pub fn addModuleMemberCompletionsFromModuleEnv(
        self: *CompletionBuilder,
        module_env: *ModuleEnv,
        module_name: []const u8,
    ) Allocator.Error!void {
        var type_writer: ?types.TypeWriter = try module_env.initTypeWriter();
        defer if (type_writer) |*tw| tw.deinit();

        const exposed = &module_env.common.exposed_items;
        var iter = exposed.iterator();
        while (iter.next()) |exp_entry| {
            const ident_idx: base.Ident.Idx = @bitCast(exp_entry.ident_idx);
            const name = module_env.common.idents.getText(ident_idx);
            if (name.len == 0) continue;

            const without_module = stripModulePrefix(name, module_env.module_name);
            const label = blk: {
                // Module exports can be qualified (Module.member) or unqualified (member).
                // Prefer matching the actual module name to avoid leaking unrelated items,
                // but allow unqualified names when we are completing the module itself.
                const dot_index = std.mem.findScalar(u8, without_module, '.');
                if (dot_index == null) {
                    if (!std.mem.eql(u8, module_env.module_name, module_name)) continue;
                    break :blk without_module;
                }

                if (!std.mem.startsWith(u8, without_module, module_name)) continue;
                if (without_module.len <= module_name.len or without_module[module_name.len] != '.') continue;

                const remainder = without_module[module_name.len + 1 ..];
                break :blk firstSegment(remainder);
            };
            if (label.len == 0) continue;

            const kind: u32 = if (label.len > 0 and std.ascii.isUpper(label[0]))
                @backingInt(CompletionItemKind.class)
            else
                @backingInt(CompletionItemKind.function);

            var detail: ?[]const u8 = null;
            var documentation: ?[]const u8 = null;
            if (type_writer) |*tw| {
                if (module_env.common.getValueNodeIndexById(self.allocator, ident_idx)) |node_idx| {
                    if (module_env.store.isDefNode(node_idx)) {
                        const def_idx: CIR.Def.Idx = @fromBackingInt(@intCast(node_idx));
                        const def = module_env.store.getDef(def_idx);
                        const type_var = ModuleEnv.varFrom(def.pattern);
                        // Type formatting is best-effort; missing type info is acceptable
                        tw.write(type_var, .one_line) catch |err| switch (err) {
                            error.OutOfMemory => return error.OutOfMemory,
                            error.WriteFailed => {},
                        };
                        const type_str = tw.get();
                        if (type_str.len > 0) {
                            detail = try self.strings.dupe(u8, type_str);
                        }
                        tw.reset();

                        documentation = try doc_comments.extractDocForDef(
                            self.strings,
                            module_env.common.source,
                            &module_env.store,
                            def,
                        );
                    }
                }
            }

            const added = try self.addItem(.{
                .label = label,
                .kind = kind,
                .detail = detail,
                .documentation = documentation,
            });
            if (added) {} else {}
        }
    }

    /// Add completions for members under a qualified namespace chain.
    ///
    /// This handles nested nominal/module-like chains that are represented in
    /// CIR as fully qualified identifiers, e.g. `pkg.MyType.Sub.ta` while the
    /// cursor chain is `MyType.Sub.`.
    pub fn addNamespaceMemberCompletions(
        self: *CompletionBuilder,
        module_env: *ModuleEnv,
        namespace_chain: []const u8,
    ) Allocator.Error!bool {
        var added_any = false;

        // Top-level defs.
        const defs_slice = module_env.store.sliceDefs(module_env.all_defs);
        for (defs_slice) |def_idx| {
            const def = module_env.store.getDef(def_idx);
            const ident_idx = module_lookup.extractIdentFromPattern(&module_env.store, def.pattern) orelse continue;
            const full_name = module_env.getIdentText(ident_idx);
            const label = namespaceMemberLabel(full_name, namespace_chain) orelse continue;
            if (label.len == 0) continue;

            const kind: u32 = if (std.ascii.isUpper(label[0]))
                @backingInt(CompletionItemKind.class)
            else
                @backingInt(CompletionItemKind.field);

            if (try self.addItem(.{ .label = label, .kind = kind, .detail = null })) {
                added_any = true;
            }
        }

        // Statement-bound defs (app-style declarations).
        const statements_slice = module_env.store.sliceStatements(module_env.all_statements);
        for (statements_slice) |stmt_idx| {
            const stmt = module_env.store.getSourceStatement(stmt_idx);
            const pattern_idx = module_lookup.boundPattern(stmt) orelse continue;
            const ident_idx = module_lookup.extractIdentFromPattern(&module_env.store, pattern_idx) orelse continue;
            const full_name = module_env.getIdentText(ident_idx);
            const label = namespaceMemberLabel(full_name, namespace_chain) orelse continue;
            if (label.len == 0) continue;

            const kind: u32 = if (std.ascii.isUpper(label[0]))
                @backingInt(CompletionItemKind.class)
            else
                @backingInt(CompletionItemKind.field);

            if (try self.addItem(.{ .label = label, .kind = kind, .detail = null })) {
                added_any = true;
            }
        }

        return added_any;
    }

    // Type Completions

    /// Add type completions for type annotation context.
    pub fn addTypeCompletions(self: *CompletionBuilder, module_env: *ModuleEnv) Allocator.Error!void {
        try self.addTypeNamesFromModuleEnv(module_env);
    }

    /// Add type completions from all modules in BuildEnv.
    pub fn addTypeCompletionsFromEnv(self: *CompletionBuilder, env: *BuildEnv) Allocator.Error!void {
        const coord = env.coordinator orelse return;
        var pkg_it = coord.packages.iterator();
        while (pkg_it.next()) |entry| {
            const pkg = entry.value_ptr.*;
            for (pkg.modules.items) |*module_state| {
                if (module_state.moduleEnv()) |module_env| {
                    try self.addTypeNamesFromModuleEnv(module_env);
                }
            }
        }
    }

    /// Add type names (aliases and nominals) from a ModuleEnv.
    fn addTypeNamesFromModuleEnv(self: *CompletionBuilder, module_env: *ModuleEnv) Allocator.Error!void {
        const statements_slice = module_env.store.sliceStatements(module_env.all_statements);
        for (statements_slice) |stmt_idx| {
            const stmt = module_env.store.getSourceStatement(stmt_idx);
            const header_idx = module_lookup.typeDeclHeader(stmt) orelse continue;
            const header = module_env.store.getTypeHeader(header_idx);
            const name = module_env.getIdentText(header.name);
            if (name.len == 0) continue;

            const documentation = try doc_comments.extractDocForStatement(
                self.strings,
                module_env.common.source,
                &module_env.store,
                stmt,
                stmt_idx,
            );

            _ = try self.addItem(.{
                .label = name,
                .kind = @backingInt(CompletionItemKind.class),
                .detail = null,
                .documentation = documentation,
            });
        }
    }

    // Local Completions

    /// Add local definition completions (variables, functions in scope).
    pub fn addLocalCompletions(self: *CompletionBuilder, module_env: *ModuleEnv, cursor_offset: u32) Allocator.Error!void {
        // Initialize type writer for formatting types
        var type_writer: ?types.TypeWriter = try module_env.initTypeWriter();
        defer if (type_writer) |*tw| tw.deinit();

        const bindings = try self.scopeBindings(module_env);

        // Add local variables in scope at cursor position
        for (bindings) |binding| {
            if (!scope_map.ScopeMap.isVisibleAt(binding, cursor_offset)) continue;

            const name = module_env.getIdentText(binding.ident);
            if (name.len == 0) continue;

            const label = module_lookup.declaredName(module_env, binding.ident);

            // Determine kind - parameters and local variables
            const kind: u32 = @backingInt(CompletionItemKind.variable);

            // Get type information for the binding
            var detail: ?[]const u8 = null;
            if (type_writer) |*tw| {
                const type_var = ModuleEnv.varFrom(binding.pattern_idx);
                // Type formatting is best-effort; missing type info is acceptable
                tw.write(type_var, .one_line) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    error.WriteFailed => {},
                };
                const type_str = tw.get();
                if (type_str.len > 0) {
                    detail = try self.strings.dupe(u8, type_str);
                }
                tw.reset();
            }

            const documentation = try doc_comments.extractDocForBinding(
                self.strings,
                module_env.common.source,
                &module_env.store,
                binding.owner,
            );

            _ = try self.addItem(.{
                .label = label,
                .kind = kind,
                .detail = detail,
                .documentation = documentation,
            });
        }

        // Add definitions from all_defs (top-level)
        const defs_slice = module_env.store.sliceDefs(module_env.all_defs);
        for (defs_slice) |def_idx| {
            const def = module_env.store.getDef(def_idx);
            const pattern = module_env.store.getSourcePattern(def.pattern);

            const ident_idx = patternIdent(pattern) orelse continue;

            const name = module_env.getIdentText(ident_idx);
            if (name.len == 0) continue;
            if (std.mem.findScalar(u8, name, '.') != null) continue;

            // Determine completion kind based on the expression type
            const expr = module_env.store.getSourceExpr(def.expr);
            const kind = completionKindForExpr(expr);

            // Get type information for the definition
            var detail: ?[]const u8 = null;
            if (type_writer) |*tw| {
                const type_var = ModuleEnv.varFrom(def.pattern);
                // Type formatting is best-effort; missing type info is acceptable
                tw.write(type_var, .one_line) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    error.WriteFailed => {},
                };
                const type_str = tw.get();
                if (type_str.len > 0) {
                    detail = try self.strings.dupe(u8, type_str);
                }
                tw.reset();
            }

            const documentation = try doc_comments.extractDocForDef(
                self.strings,
                module_env.common.source,
                &module_env.store,
                def,
            );

            _ = try self.addItem(.{
                .label = name,
                .kind = kind,
                .detail = detail,
                .documentation = documentation,
            });
        }

        // Also check statements (apps use statements for definitions)
        const local_statements_slice = module_env.store.sliceStatements(module_env.all_statements);
        for (local_statements_slice) |stmt_idx| {
            const stmt = module_env.store.getSourceStatement(stmt_idx);
            const stmt_parts = module_lookup.getStatementParts(stmt);

            if (module_lookup.boundPattern(stmt)) |pattern_idx| {
                const pattern = module_env.store.getSourcePattern(pattern_idx);

                const ident_idx = patternIdent(pattern) orelse continue;

                const name = module_env.getIdentText(ident_idx);
                if (name.len == 0) continue;
                if (std.mem.findScalar(u8, name, '.') != null) continue;

                // Determine completion kind
                var kind: u32 = @backingInt(CompletionItemKind.variable);
                if (stmt_parts.expr) |expr_idx| {
                    const expr = module_env.store.getSourceExpr(expr_idx);
                    kind = completionKindForExpr(expr);
                }

                // Get type information
                var detail: ?[]const u8 = null;
                if (type_writer) |*tw| {
                    const type_var = ModuleEnv.varFrom(pattern_idx);
                    // Type formatting is best-effort; missing type info is acceptable
                    tw.write(type_var, .one_line) catch |err| switch (err) {
                        error.OutOfMemory => return error.OutOfMemory,
                        error.WriteFailed => {},
                    };
                    const type_str = tw.get();
                    if (type_str.len > 0) {
                        detail = try self.strings.dupe(u8, type_str);
                    }
                    tw.reset();
                }

                const documentation = try doc_comments.extractDocForStatement(
                    self.strings,
                    module_env.common.source,
                    &module_env.store,
                    stmt,
                    stmt_idx,
                );

                _ = try self.addItem(.{
                    .label = name,
                    .kind = kind,
                    .detail = detail,
                    .documentation = documentation,
                });
            }
        }
    }

    // Record Field Completions

    /// Add record field completions for a record variable access (e.g., "myRecord.").
    pub fn addRecordFieldCompletions(
        self: *CompletionBuilder,
        module_env: *ModuleEnv,
        variable_name: []const u8,
        variable_start: u32,
    ) Allocator.Error!void {
        self.logDebug("addRecordFieldCompletions: looking for '{s}' at offset {d}", .{ variable_name, variable_start });

        // Look up the definition by name in top-level defs/statements.
        // We use def/stmt lookup rather than ScopeMap bindings because the
        // binding's pattern_idx may come from incomplete code and lack full
        // type info (especially when using snapshots).

        // Check top-level definitions
        const defs_slice = module_env.store.sliceDefs(module_env.all_defs);
        self.logDebug("addRecordFieldCompletions: checking {d} top-level defs", .{defs_slice.len});

        for (defs_slice) |def_idx| {
            const def = module_env.store.getDef(def_idx);
            const pattern = module_env.store.getSourcePattern(def.pattern);

            const ident_idx = patternIdent(pattern) orelse continue;

            const name = module_env.getIdentText(ident_idx);
            self.logDebug("addRecordFieldCompletions: def '{s}' pattern={} has_annotation={}", .{ name, def.pattern, def.annotation != null });
            if (std.mem.eql(u8, name, variable_name)) {
                self.logDebug("addRecordFieldCompletions: FOUND def '{s}' pattern={} annotation={?}", .{ name, def.pattern, def.annotation });

                // Found the definition - get its type and extract record fields
                const type_var = ModuleEnv.varFrom(def.pattern);
                self.logDebug("addRecordFieldCompletions: type_var for def={}", .{type_var});
                try self.addFieldsFromTypeVar(module_env, type_var);
                return;
            }
        }

        // Check statements (apps use statements for definitions)
        const statements_slice = module_env.store.sliceStatements(module_env.all_statements);
        self.logDebug("addRecordFieldCompletions: checking {d} statements", .{statements_slice.len});
        for (statements_slice) |stmt_idx| {
            const stmt = module_env.store.getSourceStatement(stmt_idx);
            const pattern_idx = module_lookup.getDeclarationPattern(stmt) orelse continue;

            const pattern = module_env.store.getSourcePattern(pattern_idx);
            const ident_idx = patternIdent(pattern) orelse continue;

            const name = module_env.getIdentText(ident_idx);
            self.logDebug("addRecordFieldCompletions: stmt '{s}'", .{name});
            if (std.mem.eql(u8, name, variable_name)) {
                self.logDebug("addRecordFieldCompletions: FOUND stmt '{s}'", .{name});
                // Found the definition - get its type and extract record fields
                const type_var = ModuleEnv.varFrom(pattern_idx);
                try self.addFieldsFromTypeVar(module_env, type_var);
                return;
            }
        }
    }

    /// Extract and add record fields from a type variable.
    pub fn addFieldsFromTypeVar(self: *CompletionBuilder, module_env: *ModuleEnv, type_var: types.Var) Allocator.Error!void {
        const type_store = &module_env.types;

        var resolved = type_store.resolveVar(type_var);
        var content = resolved.desc.content;

        self.logDebug("addFieldsFromTypeVar: type_var={}, content tag={s}", .{ type_var, @tagName(content) });

        var steps: usize = 0;
        while (true) : (steps += 1) {
            if (steps > 8) break;

            if (content.unwrapRecord()) |record| {
                self.logDebug("addFieldsFromTypeVar: found record after resolve", .{});
                try self.addFieldsFromRecord(module_env, record);
                return;
            }

            if (std.meta.activeTag(content) == .alias) {
                const backing_var = type_store.getAliasBackingVar(content.alias);
                resolved = type_store.resolveVar(backing_var);
                content = resolved.desc.content;
                continue;
            }
            if (std.meta.activeTag(content) != .structure or std.meta.activeTag(content.structure) != .nominal_type) break;
            if (!self.backingVisibleToRequester(module_env, content.structure.nominal_type)) break;

            // Row/tuple structure is declaration data: unwrap through the
            // declaration's backing template (formals appear as rigid vars).
            const decl_idx = type_store.lookupNominalDecl(content.structure.nominal_type) orelse break;
            const decl = type_store.getNominalDecl(decl_idx);
            if (!decl.isValid()) break;
            resolved = type_store.resolveVar(decl.backing);
            content = resolved.desc.content;
            continue;
        }

        // Try to get record fields, handling aliases that wrap records
        try self.addFieldsFromContent(module_env, content, 0);
    }

    /// Extract and add tuple element index completions from a type variable.
    /// For tuple types, adds completions like "0", "1", "2" for each element.
    pub fn addTupleIndexCompletions(self: *CompletionBuilder, module_env: *ModuleEnv, type_var: types.Var) Allocator.Error!void {
        const type_store = &module_env.types;

        var resolved = type_store.resolveVar(type_var);
        var content = resolved.desc.content;

        var steps: usize = 0;
        while (true) : (steps += 1) {
            if (steps > 8) break;

            if (std.meta.activeTag(content) == .structure) {
                const flat_type = content.structure;
                if (std.meta.activeTag(flat_type) == .tuple) {
                    const tuple = flat_type.tuple;
                    const elem_vars = type_store.sliceVars(tuple.elems);

                    var type_writer: ?types.TypeWriter = try module_env.initTypeWriter();
                    defer if (type_writer) |*tw| tw.deinit();

                    for (elem_vars, 0..) |elem_var, i| {
                        var detail: ?[]const u8 = null;
                        if (type_writer) |*tw| {
                            // Type formatting is best-effort; missing type info is acceptable
                            tw.write(elem_var, .one_line) catch |err| switch (err) {
                                error.OutOfMemory => return error.OutOfMemory,
                                error.WriteFailed => {},
                            };
                            const type_str = tw.get();
                            if (type_str.len > 0) {
                                detail = try self.strings.dupe(u8, type_str);
                            }
                            tw.reset();
                        }

                        // Use a stack buffer; addItem duplicates accepted labels.
                        var label_buf: [32]u8 = undefined;
                        const label = std.fmt.bufPrint(&label_buf, "{d}", .{i}) catch continue;
                        const added = try self.addItem(.{
                            .label = label,
                            .kind = @backingInt(CompletionItemKind.field),
                            .detail = detail,
                        });
                        if (added) {} else {}
                    }
                    return;
                }
                // The checker refuses tuple access on a nominal type, so
                // its backing is not followed.
                break;
            }
            if (std.meta.activeTag(content) == .alias) {
                const backing_var = type_store.getAliasBackingVar(content.alias);
                resolved = type_store.resolveVar(backing_var);
                content = resolved.desc.content;
                continue;
            }
            break;
        }
    }

    /// Resolve a record field's type variable from a receiver type.
    ///
    /// This unwraps aliases to find records and returns the field's type var
    /// for chained access resolution (e.g., myrec.subrec.).
    pub fn getFieldTypeVarFromTypeVar(
        self: *CompletionBuilder,
        module_env: *ModuleEnv,
        type_var: types.Var,
        field_name: []const u8,
    ) Allocator.Error!?types.Var {
        const type_store = &module_env.types;

        var resolved = type_store.resolveVar(type_var);
        var content = resolved.desc.content;

        var steps: usize = 0;
        while (steps < 8) : (steps += 1) {
            if (content.unwrapRecord()) |record| {
                return try self.findFieldVarInRecord(module_env, record, field_name);
            }

            if (std.meta.activeTag(content) == .alias) {
                const backing_var = type_store.getAliasBackingVar(content.alias);
                resolved = type_store.resolveVar(backing_var);
                content = resolved.desc.content;
                continue;
            }
            if (std.meta.activeTag(content) != .structure or std.meta.activeTag(content.structure) != .nominal_type) break;
            if (!self.backingVisibleToRequester(module_env, content.structure.nominal_type)) break;

            // Row/tuple structure is declaration data: unwrap through the
            // declaration's backing template (formals appear as rigid vars).
            const decl_idx = type_store.lookupNominalDecl(content.structure.nominal_type) orelse break;
            const decl = type_store.getNominalDecl(decl_idx);
            if (!decl.isValid()) break;
            resolved = type_store.resolveVar(decl.backing);
            content = resolved.desc.content;
            continue;
        }

        return null;
    }

    /// Recursively extract fields from type content, unwrapping aliases.
    fn addFieldsFromContent(
        self: *CompletionBuilder,
        module_env: *ModuleEnv,
        content: types.Content,
        depth: usize,
    ) Allocator.Error!void {
        const type_store = &module_env.types;

        self.logDebug("addFieldsFromContent: content tag={s}", .{@tagName(content)});

        if (depth > 16) return;

        // Check if this is directly a record
        if (content.unwrapRecord()) |record| {
            self.logDebug("addFieldsFromContent: found record!", .{});
            try self.addFieldsFromRecord(module_env, record);
            return;
        }

        // Check if this is an alias (e.g., a type alias wrapping a record)
        switch (content) {
            .alias => |alias| {
                self.logDebug("addFieldsFromContent: unwrapping alias", .{});
                // Get the backing type of the alias
                const backing_var = type_store.getAliasBackingVar(alias);
                const backing_resolved = type_store.resolveVar(backing_var);
                try self.addFieldsFromContent(module_env, backing_resolved.desc.content, depth + 1);
            },
            .structure => |flat_type| {
                self.logDebug("addFieldsFromContent: structure, flat_type tag={s}", .{@tagName(flat_type)});
            },
            .flex, .rigid, .field_presence, .err => {
                self.logDebug("addFieldsFromContent: not a record or alias, tag={s}", .{@tagName(content)});
            },
        }
    }

    /// Add completion items for fields in a record type.
    fn addFieldsFromRecord(self: *CompletionBuilder, module_env: *ModuleEnv, record: types.Record) Allocator.Error!void {
        const type_store = &module_env.types;

        const row = try record_row.gather(self.allocator, &module_env.types, &module_env.common.idents, record);
        defer self.allocator.free(row);

        self.logDebug("addFieldsFromRecord: record.fields={}, row.len={d}", .{ record.fields, row.len });

        // Initialize type writer for formatting field types
        var type_writer: ?types.TypeWriter = try module_env.initTypeWriter();
        defer if (type_writer) |*tw| tw.deinit();

        // Iterate over record fields
        for (row) |field| {
            const field_name = module_env.getIdentText(field.name);
            const field_presence = field.presence;
            self.logDebug("addFieldsFromRecord: field '{s}'", .{field_name});
            if (field_name.len == 0) continue;

            const field_var = field_presence.typeVar();

            // Get field type for detail
            var detail: ?[]const u8 = null;
            if (type_writer) |*tw| {
                // Type formatting is best-effort; missing type info is acceptable
                tw.write(field_var, .one_line) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    error.WriteFailed => {},
                };
                const type_str = tw.get();
                if (type_str.len > 0) {
                    detail = try self.strings.dupe(u8, type_str);
                }
                tw.reset();
            }

            const insert_text = if (fieldPresenceIsOptional(type_store, field_presence))
                try std.fmt.allocPrint(self.strings, "?{s}", .{field_name})
            else
                null;

            _ = try self.addItem(.{
                .label = field_name,
                .kind = @backingInt(CompletionItemKind.field),
                .detail = detail,
                .insertText = insert_text,
            });
        }
    }

    fn fieldPresenceIsOptional(type_store: *const types.Store, presence: types.RecordField.Presence) bool {
        const presence_var = presence.presenceVar() orelse return false;
        return switch (type_store.resolveVar(presence_var).desc.content) {
            .field_presence => |kind| switch (kind) {
                .optional => true,
                .required, .defaulted => false,
            },
            .flex, .rigid, .alias, .structure, .err => false,
        };
    }

    /// Find the type var for a specific field within a record.
    fn findFieldVarInRecord(self: *CompletionBuilder, module_env: *ModuleEnv, record: types.Record, field_name: []const u8) Allocator.Error!?types.Var {
        const row = try record_row.gather(self.allocator, &module_env.types, &module_env.common.idents, record);
        defer self.allocator.free(row);

        for (row) |field| {
            if (std.mem.eql(u8, module_env.getIdentText(field.name), field_name)) {
                return field.presence.typeVar();
            }
        }

        return null;
    }

    // Method Completions

    /// Add method completions for static dispatch (e.g., "value.method()").
    pub fn addMethodCompletions(
        self: *CompletionBuilder,
        module_env: *ModuleEnv,
        variable_name: []const u8,
        variable_start: u32,
    ) Allocator.Error!void {
        self.logDebug("addMethodCompletions: looking for '{s}' at offset {d}", .{ variable_name, variable_start });

        const bindings = try self.scopeBindings(module_env);
        self.logDebug("addMethodCompletions: scope has {d} bindings", .{bindings.len});

        // Find the binding with matching name that's visible at the variable position
        var found_binding: ?scope_map.Binding = null;
        for (bindings) |binding| {
            const name = module_env.getIdentText(binding.ident);
            const is_visible = scope_map.ScopeMap.isVisibleAt(binding, variable_start);
            if (!is_visible) continue;
            if (std.mem.eql(u8, name, variable_name)) {
                self.logDebug("addMethodCompletions: FOUND binding '{s}'", .{name});
                found_binding = binding;
                break;
            }
        }

        // Also check top-level definitions
        if (found_binding == null) {
            const defs_slice = module_env.store.sliceDefs(module_env.all_defs);
            self.logDebug("addMethodCompletions: checking {d} top-level defs", .{defs_slice.len});
            for (defs_slice) |def_idx| {
                const def = module_env.store.getDef(def_idx);
                const pattern = module_env.store.getSourcePattern(def.pattern);

                const ident_idx = patternIdent(pattern) orelse continue;

                const name = module_env.getIdentText(ident_idx);
                if (std.mem.eql(u8, name, variable_name)) {
                    self.logDebug("addMethodCompletions: FOUND def '{s}'", .{name});
                    // Found the definition - get its type and find methods
                    const type_var = ModuleEnv.varFrom(def.pattern);
                    try self.addMethodsFromTypeVar(module_env, type_var);
                    return;
                }
            }
        }

        // Also check statements (apps use statements for definitions)
        if (found_binding == null) {
            const statements_slice = module_env.store.sliceStatements(module_env.all_statements);
            self.logDebug("addMethodCompletions: checking {d} statements", .{statements_slice.len});
            for (statements_slice) |stmt_idx| {
                const stmt = module_env.store.getSourceStatement(stmt_idx);
                const pattern_idx = module_lookup.getDeclarationPattern(stmt) orelse continue;

                const pattern = module_env.store.getSourcePattern(pattern_idx);
                const ident_idx = patternIdent(pattern) orelse continue;

                const name = module_env.getIdentText(ident_idx);
                if (std.mem.eql(u8, name, variable_name)) {
                    self.logDebug("addMethodCompletions: FOUND stmt '{s}'", .{name});
                    // Found the definition - get its type and find methods
                    const type_var = ModuleEnv.varFrom(pattern_idx);
                    try self.addMethodsFromTypeVar(module_env, type_var);
                    return;
                }
            }
        }

        if (found_binding) |binding| {
            self.logDebug("addMethodCompletions: using binding pattern_idx={}", .{binding.pattern_idx});
            if (self.findExprTypeForPattern(module_env, binding.pattern_idx)) |type_var| {
                try self.addMethodsFromTypeVar(module_env, type_var);
                return;
            }
            // Get the type of this binding and find methods
            const type_var = ModuleEnv.varFrom(binding.pattern_idx);
            try self.addMethodsFromTypeVar(module_env, type_var);
        }
    }

    /// Extract methods available for a type variable and add them as completions.
    pub fn addMethodsFromTypeVar(self: *CompletionBuilder, module_env: *ModuleEnv, type_var: types.Var) Allocator.Error!void {
        const type_store = &module_env.types;

        self.logDebug("addMethodsFromTypeVar: type_var={}", .{type_var});
        var resolved = type_store.resolveVar(type_var);
        var content = resolved.desc.content;

        var steps: usize = 0;
        while (true) : (steps += 1) {
            if (steps > 8) {
                self.logDebug("addMethodsFromTypeVar: hit step limit", .{});
                break;
            }

            const method_owner_opt: ?MethodOwnerLookup = if (std.meta.activeTag(content) == .alias)
                if (content.alias.source_decl.toOptional()) |source_decl| .{
                    .owner = @fromBackingInt(@intCast(source_decl)),
                    .type_name = module_env.getIdentText(content.alias.ident.ident_idx),
                    .builtin_origin = content.alias.source_decl.originIsBuiltin(),
                    .origin_module = content.alias.origin_module,
                } else null
            else if (std.meta.activeTag(content) == .structure and std.meta.activeTag(content.structure) == .nominal_type)
                if (content.structure.nominal_type.sourceDeclOptional()) |source_decl| .{
                    .owner = @fromBackingInt(@intCast(source_decl)),
                    .type_name = module_env.getIdentText(content.structure.nominal_type.ident.ident_idx),
                    .builtin_origin = content.structure.nominal_type.originIsBuiltin(),
                    .origin_module = content.structure.nominal_type.origin_module,
                } else null
            else
                null;

            if (method_owner_opt) |method_owner| {
                self.logDebug("addMethodsFromTypeVar: owner={} name={s}", .{ method_owner.owner, method_owner.type_name });

                // A type's methods are declared in its own module.
                const owner_env = module_envs.forTypeOrigin(self.module_handle.envPtr(), module_env, method_owner.origin_module, method_owner.builtin_origin) orelse
                    base.invariant("completion: no module env of the build declares a type of module {s}", .{module_env.moduleIdentityDisplayText(method_owner.origin_module)});
                try self.addMethodsForOwnerInEnv(owner_env, method_owner);
            }

            switch (content) {
                inline .flex, .rigid => |flex| {
                    self.logDebug("addMethodsFromTypeVar: flex constraints", .{});
                    // Extract method names from flex constraints
                    try self.addMethodsFromConstraints(module_env, flex.constraints);
                    break;
                },
                .alias => |alias| {
                    self.logDebug("addMethodsFromTypeVar: alias unwrap", .{});
                    const backing_var = type_store.getAliasBackingVar(alias);
                    resolved = type_store.resolveVar(backing_var);
                    content = resolved.desc.content;
                    continue;
                },
                .structure, .field_presence, .err => break,
            }
        }
    }

    /// Extract method names from static dispatch constraints and add them as completions.
    fn addMethodsFromConstraints(
        self: *CompletionBuilder,
        module_env: *ModuleEnv,
        constraints: types.StaticDispatchConstraint.SafeList.Range,
    ) Allocator.Error!void {
        if (constraints.isEmpty()) {
            self.logDebug("addMethodsFromConstraints: empty", .{});
            return;
        }

        const constraints_slice = module_env.types.sliceStaticDispatchConstraints(constraints);
        self.logDebug("addMethodsFromConstraints: count={d}", .{constraints_slice.len});
        for (constraints_slice) |constraint| {
            const method_name = module_env.getIdentText(constraint.fn_name);

            if (method_name.len == 0) continue;

            // Try to get detail from the constraint's function type
            var detail: ?[]const u8 = null;
            var type_writer: ?types.TypeWriter = try module_env.initTypeWriter();
            defer if (type_writer) |*tw| tw.deinit();

            if (type_writer) |*tw| {
                // Type formatting is best-effort; missing type info is acceptable
                tw.write(constraint.fn_var, .one_line) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    error.WriteFailed => {},
                };
                const type_str = tw.get();
                if (type_str.len > 0) {
                    detail = try self.strings.dupe(u8, type_str);
                }
                tw.reset();
            }

            const added = try self.addItem(.{
                .label = method_name,
                .kind = @backingInt(CompletionItemKind.method),
                .detail = detail,
            });
            if (added) {} else {}
        }
    }

    /// Find the type of an expression for a pattern.
    fn findExprTypeForPattern(self: *CompletionBuilder, module_env: *ModuleEnv, pattern_idx: CIR.Pattern.Idx) ?types.Var {
        const defs_slice = module_env.store.sliceDefs(module_env.all_defs);
        for (defs_slice) |def_idx| {
            const def = module_env.store.getDef(def_idx);
            if (def.pattern == pattern_idx) {
                self.logDebug("findExprTypeForPattern: def expr for pattern_idx={} expr_idx={}", .{ pattern_idx, def.expr });
                return ModuleEnv.varFrom(def.expr);
            }
        }

        const statements_slice = module_env.store.sliceStatements(module_env.all_statements);
        for (statements_slice) |stmt_idx| {
            const stmt = module_env.store.getSourceStatement(stmt_idx);
            const stmt_parts = module_lookup.getStatementParts(stmt);
            if (module_lookup.boundPattern(stmt)) |stmt_pattern_idx| {
                if (stmt_pattern_idx == pattern_idx) {
                    if (stmt_parts.expr) |expr_idx| {
                        self.logDebug("findExprTypeForPattern: stmt expr for pattern_idx={} expr_idx={}", .{ pattern_idx, expr_idx });
                        return ModuleEnv.varFrom(expr_idx);
                    }
                }
            }
        }

        self.logDebug("findExprTypeForPattern: no expr for pattern_idx={}", .{pattern_idx});
        return null;
    }

    /// Add methods for a specific source declaration owner by searching method_idents.
    fn addMethodsForOwnerInEnv(self: *CompletionBuilder, module_env: *ModuleEnv, method_owner: MethodOwnerLookup) Allocator.Error!void {
        // Initialize type writer for formatting method signatures
        var type_writer: ?types.TypeWriter = try module_env.initTypeWriter();
        defer if (type_writer) |*tw| tw.deinit();

        // Get the type name for display purposes
        const type_name = method_owner.type_name;

        // Iterate through method_idents to find all methods for this owner.
        const entries = module_env.method_idents.entries.items;
        for (entries) |entry| {
            // Check if this method is for our type owner.
            if (entry.key.owner == method_owner.owner) {
                const method_ident = entry.key.methodIdent();
                const method_name = module_env.getIdentText(method_ident);

                if (method_name.len == 0) continue;

                // Try to get the method's type signature
                var detail: ?[]const u8 = null;
                const qualified_ident = entry.value;
                const qualified_name = module_env.getIdentText(qualified_ident);

                // The method table entry names the method's def.
                const binding = module_env.lookupMethodBindingForOwnerConst(method_owner.owner, method_ident) orelse
                    base.invariant("completion: a method ident has no method table entry", .{});
                const method_def = module_env.store.getDef(binding.def_idx);
                const method_type_var = ModuleEnv.varFrom(method_def.pattern);
                if (Check.valuelessMethod(module_env, binding.def_idx) != null) continue;
                if (!firstParameterTakesOwner(module_env, method_type_var, method_owner)) continue;

                if (type_writer) |*tw| {
                    // Type formatting is best-effort; missing type info is acceptable
                    tw.write(method_type_var, .one_line) catch |err| switch (err) {
                        error.OutOfMemory => return error.OutOfMemory,
                        error.WriteFailed => {},
                    };
                    const type_str = tw.get();
                    if (type_str.len > 0) {
                        detail = try self.strings.dupe(u8, type_str);
                    }
                    tw.reset();
                }

                // If we couldn't get the type signature, at least show which type it's from
                if (detail == null and type_name.len > 0 and qualified_name.len > 0) {
                    detail = try std.fmt.allocPrint(self.strings, "method on {s}", .{type_name});
                }

                // Extract documentation for the method definition.
                const documentation = try doc_comments.extractDocForDef(self.strings, module_env.common.source, &module_env.store, method_def);

                const added = try self.addItem(.{
                    .label = method_name,
                    .kind = @backingInt(CompletionItemKind.method),
                    .detail = detail,
                    .documentation = documentation,
                });
                if (added) {} else {}
            }
        }
    }

    /// A completion filter: whether to suggest the associated item of type
    /// `method_type` after a value of the owner's type. Completion is a
    /// suggestion, so this filter only leaves out items that cannot take the
    /// receiver: it keeps a function whose first parameter is the owner type
    /// or a type variable. The exact rule is unification in the checker,
    /// which relates the item's type to `receiver, args -> ret`, including
    /// the type arguments and a variable's `where` constraints.
    fn firstParameterTakesOwner(owner_env: *ModuleEnv, method_type: types.Var, method_owner: MethodOwnerLookup) bool {
        const type_store = &owner_env.types;
        const func = type_store.resolveThroughAliases(method_type).desc.content.unwrapFunc() orelse return false;
        const params = type_store.sliceVars(func.args);
        if (params.len == 0) return false;
        var content = type_store.resolveVar(params[0]).desc.content;
        while (true) switch (content) {
            .flex, .rigid => return true,
            .alias => |alias| {
                if (alias.source_decl.toOptional()) |decl| {
                    if (decl == @backingInt(method_owner.owner) and alias.origin_module == owner_env.self_module_identity) return true;
                }
                content = type_store.resolveVar(type_store.getAliasBackingVar(alias)).desc.content;
            },
            .structure => |flat_type| switch (flat_type) {
                .nominal_type => |nominal| {
                    const decl = nominal.sourceDeclOptional() orelse return false;
                    return decl == @backingInt(method_owner.owner) and nominal.origin_module == owner_env.self_module_identity;
                },
                .record, .tuple, .fn_pure, .fn_effectful, .fn_unbound, .empty_record, .tag_union, .empty_tag_union => return false,
            },
            .field_presence, .err => return false,
        };
    }

    // Tag Union Completions

    /// Add tag completions for a nominal type (e.g., `Color.` → `Red`, `Green`, `Blue`).
    /// Entry point for `TypeName.` completion on nominal types.
    ///
    /// Returns true if tags were found and added, false otherwise.
    pub fn addTagCompletionsForNominalType(
        self: *CompletionBuilder,
        module_env: *ModuleEnv,
        type_name: []const u8,
        requesting_module_name: ?[]const u8, // null = same module (always allowed)
    ) Allocator.Error!bool {
        // Search all_statements for s_nominal_decl matching type_name
        const statements_slice = module_env.store.sliceStatements(module_env.all_statements);
        for (statements_slice) |stmt_idx| {
            const stmt = module_env.store.getSourceStatement(stmt_idx);
            if (std.meta.activeTag(stmt) != .s_nominal_decl) continue;
            const nom_decl = stmt.s_nominal_decl;
            const header = module_env.store.getTypeHeader(nom_decl.header);
            const rel_name = module_env.getIdentText(header.relative_name);

            if (!std.mem.eql(u8, rel_name, type_name)) continue;

            // Opaque check: if is_opaque and from another module, skip
            if (nom_decl.is_opaque and requesting_module_name != null) {
                if (!std.mem.eql(u8, requesting_module_name.?, module_env.module_name)) {
                    return false;
                }
            }

            // Get the backing type annotation
            const anno = module_env.store.getTypeAnno(nom_decl.anno);
            return try self.addTagsFromTypeAnno(module_env, anno);
        }
        return false;
    }

    /// Extracts tags from a type annotation (handles tag_union directly).
    fn addTagsFromTypeAnno(
        self: *CompletionBuilder,
        module_env: *ModuleEnv,
        anno: CIR.TypeAnno,
    ) Allocator.Error!bool {
        if (std.meta.activeTag(anno) != .tag_union) return false;
        const tags_slice = module_env.store.sliceTypeAnnos(anno.tag_union.tags);
        for (tags_slice) |tag_anno_idx| {
            const tag_anno = module_env.store.getTypeAnno(tag_anno_idx);
            if (std.meta.activeTag(tag_anno) != .tag) continue;
            const tag = tag_anno.tag;
            const tag_name = module_env.getIdentText(tag.name);
            if (tag_name.len == 0) continue;

            // Show the tag signature (e.g. "SubVal(Str)") as detail
            const detail = try self.formatTagSignature(module_env, tag_name, tag.args);

            _ = try self.addItem(.{
                .label = tag_name,
                .kind = @backingInt(CompletionItemKind.enum_member),
                .detail = detail,
            });
        }
        return true;
    }

    /// Format a tag signature like "SubVal(Str)" or "Cons(a, List(a))".
    /// Returns null for tags with no arguments.
    fn formatTagSignature(self: *CompletionBuilder, module_env: *ModuleEnv, tag_name: []const u8, args: CIR.TypeAnno.Span) Allocator.Error!?[]const u8 {
        const args_slice = module_env.store.sliceTypeAnnos(args);
        if (args_slice.len == 0) return null;

        return try self.formatTagSignatureInner(module_env, tag_name, args_slice);
    }

    fn formatTagSignatureInner(self: *CompletionBuilder, module_env: *ModuleEnv, tag_name: []const u8, args_slice: []const CIR.TypeAnno.Idx) Allocator.Error![]const u8 {
        var buf: std.ArrayList(u8) = .empty;
        errdefer buf.deinit(self.strings);
        try buf.appendSlice(self.strings, tag_name);
        try buf.append(self.strings, '(');
        for (args_slice, 0..) |arg_idx, i| {
            if (i > 0) try buf.appendSlice(self.strings, ", ");
            const arg_anno = module_env.store.getTypeAnno(arg_idx);
            try self.writeTypeAnno(&buf, module_env, arg_anno);
        }
        try buf.append(self.strings, ')');
        return try buf.toOwnedSlice(self.strings);
    }

    /// Write a human-readable representation of a TypeAnno to a buffer.
    fn writeTypeAnno(self: *CompletionBuilder, buf: *std.ArrayList(u8), module_env: *ModuleEnv, anno: CIR.TypeAnno) Allocator.Error!void {
        const alloc = self.strings;
        switch (anno) {
            .lookup => |t| {
                const name = module_env.getIdentText(t.name);
                try buf.appendSlice(alloc, stripBuiltinPrefix(name));
            },
            .rigid_var => |t| {
                try buf.appendSlice(alloc, module_env.getIdentText(t.name));
            },
            .rigid_var_lookup => |t| {
                const ref_anno = module_env.store.getTypeAnno(t.ref);
                try self.writeTypeAnno(buf, module_env, ref_anno);
            },
            .apply => |a| {
                const name = module_env.getIdentText(a.name);
                try buf.appendSlice(alloc, stripBuiltinPrefix(name));
                const apply_args = module_env.store.sliceTypeAnnos(a.args);
                if (apply_args.len > 0) {
                    try buf.append(alloc, '(');
                    for (apply_args, 0..) |arg_idx, i| {
                        if (i > 0) try buf.appendSlice(alloc, ", ");
                        const arg_anno = module_env.store.getTypeAnno(arg_idx);
                        try self.writeTypeAnno(buf, module_env, arg_anno);
                    }
                    try buf.append(alloc, ')');
                }
            },
            .tag_union => |tu| {
                try buf.append(alloc, '[');
                const tags = module_env.store.sliceTypeAnnos(tu.tags);
                for (tags, 0..) |tag_idx, i| {
                    if (i > 0) try buf.appendSlice(alloc, ", ");
                    const tag_anno = module_env.store.getTypeAnno(tag_idx);
                    try self.writeTypeAnno(buf, module_env, tag_anno);
                }
                try buf.append(alloc, ']');
            },
            .tag => |t| {
                try buf.appendSlice(alloc, module_env.getIdentText(t.name));
                const tag_args = module_env.store.sliceTypeAnnos(t.args);
                if (tag_args.len > 0) {
                    try buf.append(alloc, '(');
                    for (tag_args, 0..) |arg_idx, i| {
                        if (i > 0) try buf.appendSlice(alloc, ", ");
                        const arg_anno = module_env.store.getTypeAnno(arg_idx);
                        try self.writeTypeAnno(buf, module_env, arg_anno);
                    }
                    try buf.append(alloc, ')');
                }
            },
            .tuple => |t| {
                try buf.append(alloc, '(');
                const elems = module_env.store.sliceTypeAnnos(t.elems);
                for (elems, 0..) |elem_idx, i| {
                    if (i > 0) try buf.appendSlice(alloc, ", ");
                    const elem_anno = module_env.store.getTypeAnno(elem_idx);
                    try self.writeTypeAnno(buf, module_env, elem_anno);
                }
                try buf.append(alloc, ')');
            },
            .record => |r| {
                try buf.append(alloc, '{');
                const fields = module_env.store.sliceAnnoRecordFields(r.fields);
                for (fields, 0..) |field_idx, i| {
                    if (i > 0) try buf.appendSlice(alloc, ", ");
                    const field = module_env.store.getAnnoRecordField(field_idx);
                    try buf.appendSlice(alloc, module_env.getIdentText(field.name));
                    try buf.appendSlice(alloc, ": ");
                    const field_anno = module_env.store.getTypeAnno(field.ty);
                    try self.writeTypeAnno(buf, module_env, field_anno);
                }
                try buf.append(alloc, '}');
            },
            .@"fn" => |f| {
                const fn_args = module_env.store.sliceTypeAnnos(f.args);
                for (fn_args, 0..) |arg_idx, i| {
                    if (i > 0) try buf.appendSlice(alloc, ", ");
                    const arg_anno = module_env.store.getTypeAnno(arg_idx);
                    try self.writeTypeAnno(buf, module_env, arg_anno);
                }
                try buf.appendSlice(alloc, if (f.effectful) " => " else " -> ");
                const ret_anno = module_env.store.getTypeAnno(f.ret);
                try self.writeTypeAnno(buf, module_env, ret_anno);
            },
            .parens => |p| {
                try buf.append(alloc, '(');
                const inner = module_env.store.getTypeAnno(p.anno);
                try self.writeTypeAnno(buf, module_env, inner);
                try buf.append(alloc, ')');
            },
            .underscore => try buf.append(alloc, '_'),
            .malformed => try buf.appendSlice(alloc, "?"),
        }
    }

    /// Add ambient/structural tag completions from the module's type store.
    /// These are tags that appear in expression context without qualification.
    pub fn addAmbientTagCompletions(
        self: *CompletionBuilder,
        module_env: *ModuleEnv,
    ) Allocator.Error!void {
        // Iterate all tags in the type store
        const tag_names = module_env.types.tags.items(.name);
        for (tag_names) |name_idx| {
            const tag_name = module_env.getIdentText(name_idx);
            if (tag_name.len == 0) continue;

            _ = try self.addItem(.{
                .label = tag_name,
                .kind = @backingInt(CompletionItemKind.enum_member),
                .detail = null,
            });
        }
    }
};

// Helper Functions

/// Strip "Builtin." and "Num." prefixes for display (e.g. "Builtin.Str" → "Str", "Num.U64" → "U64").
fn stripBuiltinPrefix(name: []const u8) []const u8 {
    if (std.mem.startsWith(u8, name, "Builtin.")) {
        const without_builtin = name[8..];
        if (std.mem.startsWith(u8, without_builtin, "Num.")) {
            return without_builtin[4..];
        }
        return without_builtin;
    }
    if (std.mem.startsWith(u8, name, "Num.")) {
        return name[4..];
    }
    return name;
}

/// Strip module prefix from a name.
fn stripModulePrefix(name: []const u8, module_name: []const u8) []const u8 {
    var i: usize = 0;
    while (i < name.len) {
        const seg_start = i;
        const dot_idx = std.mem.findScalarPos(u8, name, seg_start, '.') orelse name.len;
        const seg = name[seg_start..dot_idx];

        if (std.mem.eql(u8, seg, module_name)) {
            if (dot_idx < name.len) return name[dot_idx + 1 ..];
            return "";
        }

        if (dot_idx == name.len) break;
        i = dot_idx + 1;
    }

    return name;
}

/// Get the first segment of a dotted name.
fn firstSegment(name: []const u8) []const u8 {
    const dot_idx = std.mem.findScalar(u8, name, '.') orelse name.len;
    return name[0..dot_idx];
}

/// Extract the immediate child label under `namespace_chain` from a full name.
///
/// Examples:
/// - full: `MyType.Sub.ta`, chain: `MyType.Sub` => `ta`
/// - full: `pkg.MyType.Sub.ta`, chain: `MyType.Sub` => `ta`
fn namespaceMemberLabel(full_name: []const u8, namespace_chain: []const u8) ?[]const u8 {
    if (namespace_chain.len == 0) return null;

    // Direct match: `MyType.Sub.<member>`
    if (std.mem.startsWith(u8, full_name, namespace_chain) and
        full_name.len > namespace_chain.len and
        full_name[namespace_chain.len] == '.')
    {
        const remainder = full_name[namespace_chain.len + 1 ..];
        if (remainder.len == 0) return null;
        return firstSegment(remainder);
    }

    // Qualified match: `<module>.MyType.Sub.<member>`
    var i: usize = 0;
    while (i < full_name.len) : (i += 1) {
        if (full_name[i] != '.') continue;
        const start = i + 1;
        if (start >= full_name.len) break;
        if (start + namespace_chain.len >= full_name.len) break;
        if (!std.mem.eql(u8, full_name[start .. start + namespace_chain.len], namespace_chain)) continue;
        if (full_name[start + namespace_chain.len] != '.') continue;

        const remainder_start = start + namespace_chain.len + 1;
        if (remainder_start >= full_name.len) return null;
        return firstSegment(full_name[remainder_start..]);
    }

    return null;
}

// Tests

test "stripModulePrefix" {
    const testing = std.testing;

    try testing.expectEqualStrings("to_str", stripModulePrefix("Basic.to_str", "Basic"));
    try testing.expectEqualStrings("to_str", stripModulePrefix("MyModule.Basic.to_str", "Basic"));
    try testing.expectEqualStrings("Basic.to_str", stripModulePrefix("Basic.to_str", "Other"));
    try testing.expectEqualStrings("", stripModulePrefix("Basic", "Basic"));
    try testing.expectEqualStrings("foo", stripModulePrefix("foo", "Basic"));
}

test "firstSegment" {
    const testing = std.testing;

    try testing.expectEqualStrings("Basic", firstSegment("Basic.to_str"));
    try testing.expectEqualStrings("foo", firstSegment("foo"));
    try testing.expectEqualStrings("A", firstSegment("A.B.C"));
    try testing.expectEqualStrings("", firstSegment(""));
}
