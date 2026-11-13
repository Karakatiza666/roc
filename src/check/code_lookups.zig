//! The lookups through which the Code walk reads the modules one module can
//! see (design.md "Code Reification"): one per module in reach, each that
//! module's own view of its reach, so a module's code slots read the slots
//! of its own imports. The description step and every reader that computes
//! a module's Code inventories on demand build them.

const std = @import("std");
const base = @import("base");
const can = @import("can");

const checked = @import("checked_artifact.zig");
const canonical = @import("canonical_names.zig");
const code_analyses = @import("code_analyses.zig");
const code_reifier = @import("code_reifier.zig");
const static_dispatch = @import("static_dispatch_registry.zig");

const Allocator = std.mem.Allocator;
const CIR = can.CIR;
const ModuleEnv = can.ModuleEnv;
const CheckedModuleArtifactKey = checked.CheckedModuleArtifactKey;
const ImportedModuleView = checked.ImportedModuleView;

fn invariant(comptime message: []const u8) noreturn {
    base.invariant("code lookup invariant violated: " ++ message, .{});
}

/// The Code inventories of `view`, computed on first demand, with `reach`
/// the modules the reader sees (it may hold `view` itself). A reader calls
/// this only for a module whose template it lowers or describes, so a
/// module no such reader reaches keeps its bodies unindexed.
pub fn codeInventories(gpa: Allocator, view: ImportedModuleView, reach: []const ImportedModuleView) Allocator.Error!*const code_analyses.CodeInventories {
    if (view.checked_bodies.analyses.code.inventories_slot.peek()) |computed| return computed;
    var lookups = try Lookups.init(gpa, view, reach);
    defer lookups.deinit(gpa);
    return view.checked_bodies.codeInventories(checked.foreignModule(view, lookups.own.lookup()));
}

/// The lookups of every module a description step reads: one per module,
/// each that module's own view of its reach (`code_reifier.ModuleInputs`),
/// so a module's code slots read the slots of its own imports.
pub const Lookups = struct {
    /// Every module the evaluation sees but the described one, sorted by key.
    views: []const ImportedModuleView,
    /// One lookup per view, in the order of `views`.
    modules: []ForeignStagedLookup,
    /// The described module's own lookup.
    own: ForeignStagedLookup,

    pub fn init(gpa: Allocator, module: ImportedModuleView, reach: []const ImportedModuleView) Allocator.Error!*Lookups {
        var views = std.ArrayList(ImportedModuleView).empty;
        errdefer views.deinit(gpa);
        for (reach) |view| {
            if (CheckedModuleArtifactKey.eql(view.key, module.key)) continue;
            if (checked.viewInReach(views.items, view.key) != null) continue;
            try views.append(gpa, view);
        }
        std.mem.sort(ImportedModuleView, views.items, {}, struct {
            fn lessThan(_: void, a: ImportedModuleView, b: ImportedModuleView) bool {
                return std.mem.order(u8, &a.key.bytes, &b.key.bytes) == .lt;
            }
        }.lessThan);
        const self = try gpa.create(Lookups);
        errdefer gpa.destroy(self);
        const owned_views = try views.toOwnedSlice(gpa);
        errdefer gpa.free(owned_views);
        const modules = try gpa.alloc(ForeignStagedLookup, owned_views.len);
        self.* = .{
            .views = owned_views,
            .modules = modules,
            .own = .{
                .lookups = self,
                .env = module.module_env,
                .import_identities = module.import_identities,
                .names = module.canonical_names,
                .method_registry = module.method_registry,
            },
        };
        for (owned_views, modules) |*view, *lookup| lookup.* = .{
            .lookups = self,
            .env = view.module_env,
            .import_identities = view.import_identities,
            .names = view.canonical_names,
            .method_registry = view.method_registry,
        };
        return self;
    }

    pub fn deinit(self: *Lookups, gpa: Allocator) void {
        gpa.free(self.modules);
        gpa.free(self.views);
        gpa.destroy(self);
    }

    fn indexOfKey(self: *const Lookups, key: [32]u8) ?usize {
        const found = std.sort.binarySearch(ImportedModuleView, self.views, key, struct {
            fn order(target: [32]u8, view: ImportedModuleView) std.math.Order {
                return std.mem.order(u8, &target, &view.key.bytes);
            }
        }.order);
        return found;
    }

    /// The module at `index` with its own lookup.
    fn moduleAt(self: *const Lookups, index: usize) code_reifier.ForeignModule {
        return checked.foreignModule(self.views[index], self.modules[index].lookup());
    }

    fn lookupOf(self: *const Lookups, index: usize) code_reifier.ForeignLookup {
        return self.modules[index].lookup();
    }
};

/// How the walk reaches the modules one module can see, from that module:
/// its imports by import index (the checked module each import resolved
/// to), and every module of the evaluation by key or content identity.
pub const ForeignStagedLookup = struct {
    lookups: *const Lookups,
    env: *const ModuleEnv,
    import_identities: []const checked.ImportIdentity,
    names: *const canonical.CanonicalNameStore,
    method_registry: *const static_dispatch.MethodRegistry,

    pub fn lookup(self: *const ForeignStagedLookup) code_reifier.ForeignLookup {
        return .{
            .context = self,
            .resolve = resolve,
            .resolve_alias = resolveAlias,
            .resolve_exported = resolveExported,
            .resolve_exported_alias = resolveExportedAlias,
            .resolve_exported_computed = resolveExportedComputed,
            .resolve_constant = resolveConstant,
            .resolve_method = resolveMethod,
            .resolve_inspect_override = resolveInspectOverride,
            .resolve_builtin_module = resolveBuiltinModule,
            .resolve_lookup_target = resolveLookupTarget,
            .resolve_module = resolveModule,
            .resolve_identity_module = resolveIdentityModule,
            .resolve_import_module = resolveImportModule,
        };
    }

    fn of(context: *const anyopaque) *const ForeignStagedLookup {
        return @ptrCast(@alignCast(context));
    }

    /// The module the import `import_idx` resolved to, or null for an
    /// import checking left unresolved.
    fn importIndex(self: *const ForeignStagedLookup, import_idx: CIR.Import.Idx) ?usize {
        const key = self.import_identities[@backingInt(import_idx)].artifact_key orelse return null;
        return self.lookups.indexOfKey(key.bytes) orelse
            invariant("a resolved import names a module the evaluation does not see");
    }

    /// A module in reach by its content identity, for a field default's
    /// declaring module (D5).
    fn resolveIdentityModule(context: *const anyopaque, identity: *const [32]u8) ?code_reifier.ForeignModule {
        const lookups = of(context).lookups;
        for (lookups.views, 0..) |*view, index| {
            if (checked.importedViewIdentityMatches(view, identity)) return lookups.moduleAt(index);
        }
        return null;
    }

    /// A module in reach by its key, for a recipe's root (D1).
    /// The module an import of this module resolved to, with its own lookup.
    fn resolveImportModule(context: *const anyopaque, import_idx: CIR.Import.Idx) ?code_reifier.ForeignModule {
        const self = of(context);
        const index = self.importIndex(import_idx) orelse return null;
        return self.lookups.moduleAt(index);
    }

    fn resolveModule(context: *const anyopaque, key: *const [32]u8) ?code_reifier.ForeignModule {
        const lookups = of(context).lookups;
        const index = lookups.indexOfKey(key.*) orelse return null;
        return lookups.moduleAt(index);
    }

    /// The definition a lookup of this module names.
    fn resolveLookupTarget(context: *const anyopaque, expr_idx: CIR.Expr.Idx) ?checked.LookupTarget {
        const self = of(context);
        return checked.lookupTargetInReach(self.env, self.import_identities, self.lookups.views, expr_idx);
    }

    /// Whether the module of content identity `module` is the builtin module:
    /// the described module or a module in reach, by its role.
    fn resolveBuiltinModule(context: *const anyopaque, module: *const [32]u8) bool {
        const self = of(context);
        const own = self.lookups.own.env;
        if (own.module_role == .builtin and checked.moduleEnvIdentityMatches(own, module)) return true;
        for (self.lookups.views) |*view| {
            if (view.module_env.module_role == .builtin and checked.importedViewIdentityMatches(view, module)) return true;
        }
        return false;
    }

    /// The registries in the order a method is looked up from this module:
    /// its own, then its imports in import order, then every other module
    /// in reach (`lookupCheckedMethodTarget`'s order). A method this module
    /// declares on an imported nominal is the one Roc dispatches to.
    const RegistryOrder = struct {
        self: *const ForeignStagedLookup,
        step: union(enum) { own, import: usize, view: usize, done } = .own,

        const Registry = struct {
            names: *const canonical.CanonicalNameStore,
            registry: *const static_dispatch.MethodRegistry,
        };

        fn next(it: *RegistryOrder) ?Registry {
            const lookups = it.self.lookups;
            while (true) switch (it.step) {
                .own => {
                    it.step = .{ .import = 0 };
                    return .{ .names = it.self.names, .registry = it.self.method_registry };
                },
                .import => |position| {
                    if (position == it.self.import_identities.len) {
                        it.step = .{ .view = 0 };
                        continue;
                    }
                    it.step = .{ .import = position + 1 };
                    const index = it.self.importIndex(@fromBackingInt(@intCast(position))) orelse continue;
                    const view = lookups.views[index];
                    return .{ .names = view.canonical_names, .registry = view.method_registry };
                },
                .view => |index| {
                    if (index == lookups.views.len) {
                        it.step = .done;
                        continue;
                    }
                    it.step = .{ .view = index + 1 };
                    const view = lookups.views[index];
                    return .{ .names = view.canonical_names, .registry = view.method_registry };
                },
                .done => return null,
            };
        }
    };

    /// The target a nominal's declaration names for one method.
    ///
    /// A method is declared against a nominal rather than exported under a
    /// name, so the registries answer this where the export tables answer a
    /// call.
    fn resolveMethod(
        context: *const anyopaque,
        owner: code_reifier.ForeignNominal,
        method: []const u8,
    ) ?static_dispatch.MethodTarget {
        var order = RegistryOrder{ .self = of(context) };
        while (order.next()) |registry| {
            if (checked.registeredMethod(registry.names, registry.registry, owner, method)) |target| return target;
        }
        return null;
    }

    /// The inspect override a nominal's declaration names, asked of the
    /// registry that declares its `to_inspect`, in `resolveMethod`'s order.
    ///
    /// The first registry holding the method answers, override or not: a
    /// declaration that is not an override is still the one Roc resolves, so
    /// a later registry must not supply one in its place.
    fn resolveInspectOverride(
        context: *const anyopaque,
        owner: code_reifier.ForeignNominal,
    ) ?static_dispatch.MethodTarget {
        var order = RegistryOrder{ .self = of(context) };
        while (order.next()) |registry| {
            if (checked.registeredMethod(registry.names, registry.registry, owner, "to_inspect") != null) {
                return checked.registeredInspectOverride(registry.names, registry.registry, owner);
            }
        }
        return null;
    }

    /// A constant of a named artifact. The ref the checker resolved names the
    /// artifact, which may be one this module never imported itself.
    fn resolveConstant(context: *const anyopaque, const_ref: checked.ConstRef) ?code_reifier.ForeignConstant {
        const lookups = of(context).lookups;
        const index = lookups.indexOfKey(const_ref.artifact.bytes) orelse return null;
        return checked.exportedConstant(lookups.views[index], lookups.lookupOf(index), const_ref);
    }

    fn resolve(context: *const anyopaque, import_idx: CIR.Import.Idx, target_node_idx: u32) ?code_reifier.ForeignDefinition {
        const self = of(context);
        const index = self.importIndex(import_idx) orelse return null;
        return checked.exportedDefinition(self.lookups.views[index], self.lookups.lookupOf(index), @fromBackingInt(@intCast(target_node_idx)));
    }

    /// An exact function alias a staged site names through an import.
    fn resolveAlias(context: *const anyopaque, import_idx: CIR.Import.Idx, target_node_idx: u32) ?code_reifier.ForeignAlias {
        const self = of(context);
        const index = self.importIndex(import_idx) orelse return null;
        return checked.exportedAlias(self.lookups.views[index], self.lookups.lookupOf(index), @fromBackingInt(@intCast(target_node_idx)));
    }

    /// A definition of a named artifact, which a call inside a description
    /// reaches through a binding the producer resolved.
    fn resolveExported(context: *const anyopaque, artifact: canonical.ArtifactRef, def: CIR.Def.Idx) ?code_reifier.ForeignDefinition {
        const lookups = of(context).lookups;
        const index = lookups.indexOfKey(artifact.bytes) orelse return null;
        return checked.exportedDefinition(lookups.views[index], lookups.lookupOf(index), def);
    }

    /// An exact function alias of a named artifact, which a call reaches the
    /// way it reaches a definition.
    fn resolveExportedAlias(context: *const anyopaque, artifact: canonical.ArtifactRef, def: CIR.Def.Idx) ?code_reifier.ForeignAlias {
        const lookups = of(context).lookups;
        const index = lookups.indexOfKey(artifact.bytes) orelse return null;
        return checked.exportedAlias(lookups.views[index], lookups.lookupOf(index), def);
    }

    /// A top-level value of a named artifact that computes a function, which
    /// a use inside a description reads as the expression it was written as.
    fn resolveExportedComputed(context: *const anyopaque, artifact: canonical.ArtifactRef, def: CIR.Def.Idx) ?code_reifier.ForeignComputed {
        const lookups = of(context).lookups;
        const index = lookups.indexOfKey(artifact.bytes) orelse return null;
        return checked.exportedComputed(lookups.views[index], lookups.lookupOf(index), def);
    }
};
