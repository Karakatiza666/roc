//! The on-demand code facts of one checked module: its translators' cuts and
//! the instance inventories of its templates (design.md "On-Demand Analyses
//! And Write-Once Slots", "Code Reification").
//!
//! Both are pure functions of the module's sealed data and of the same facts
//! of its imports. Each is computed on first demand into a write-once slot
//! owned by the module, is never serialized, and reports nothing: a problem
//! is data, which the module's description step reports.
//!
//! | Slot | Computed by | Read by |
//! |---|---|---|
//! | `cuts` | `code_reifier.moduleCuts` | the description steps of the module and of its importers |
//! | `inventories` | `code_reifier.planModule` | the description steps, Monotype and Boxy lowering |
//!
//! A consumer supplies the reifier's inputs (`code_reifier.CutInputs`,
//! `code_reifier.PlanInputs`) with each demand, as a consumer of a body
//! analysis supplies the module's `CheckedBodies`. The result does not depend
//! on which consumer computes it.

const std = @import("std");
const base = @import("base");
const can = @import("can");
const collections = @import("collections");

const canonical = @import("canonical_names.zig");
const checked_artifact = @import("checked_artifact.zig");
const code_output = @import("code_output.zig");
const code_reifier = @import("code_reifier.zig");
const static_dispatch = @import("static_dispatch_registry.zig");

const Allocator = std.mem.Allocator;
const CIR = can.CIR;
const CheckedTypeId = checked_artifact.CheckedTypeId;
const CheckedModuleArtifactKey = checked_artifact.CheckedModuleArtifactKey;
const CheckedProcedureTemplateId = canonical.CheckedProcedureTemplateId;

/// A range of one of a table's pools.
pub const Span = extern struct { start: u32 = 0, len: u32 = 0 };

/// The translators' cuts this module declares (plan I14, normal-form 3.8):
/// per nominal type whose `code_primitives` item is accepted, the checked
/// lookups that item lists. The walk of a site whose translator the type
/// owns resolves each lookup to the function it names, which is then a
/// `Prim` by its qualified name rather than a body to walk.
///
/// | Slice | One entry per | Holds |
/// |---|---|---|
/// | `cuts` | nominal type with a cut | its declaration statement, and its span of `members` |
/// | `members` | function in a cut, in the order the tuple lists it | the checked lookup that names it |
pub const CodeCutTable = struct {
    pub const Cut = struct { owner_decl: CIR.Statement.Idx, members: Span };

    cuts: []const Cut = &.{},
    members: []const CIR.Expr.Idx = &.{},

    /// The checked lookups of the cut that the nominal declared at
    /// `owner_decl` lists, or null for a type that declares none, whose cut
    /// is empty.
    pub fn membersOf(self: *const CodeCutTable, owner_decl: CIR.Statement.Idx) ?[]const CIR.Expr.Idx {
        for (self.cuts) |cut| {
            if (cut.owner_decl == owner_decl) return self.members[cut.members.start..][0..cut.members.len];
        }
        return null;
    }

    pub fn deinit(self: *CodeCutTable, allocator: Allocator) void {
        allocator.free(self.cuts);
        allocator.free(self.members);
        self.* = .{};
    }
};

/// An entry of a `code_primitives` item that is no `Code.prim` of a function
/// defined as a lambda or of a top-level constant, one that names a
/// definition an earlier entry names, or one that names a primitive (D3), or
/// an item that is no list of entries. The description step of the module
/// reports it at the entry or the item.
pub const CutProblem = struct {
    region: base.Region,
    kind: Kind,

    pub const Kind = enum { not_a_function, not_a_list, listed_twice, already_primitive };
};

/// The result of the `cuts` slot.
pub const CodeCuts = struct {
    table: CodeCutTable = .{},
    /// In the order of the module's `code_primitives` items.
    problems: []const CutProblem = &.{},

    fn destroy(self: *CodeCuts, allocator: Allocator) void {
        self.table.deinit(allocator);
        allocator.free(self.problems);
        allocator.destroy(self);
    }
};

/// A method the compiler calls by the type of a value, with no written use
/// (Q17): equality and hashing of a structure call each component's own
/// `is_eq` and `to_hash`, and inspection calls an eligible `to_inspect`. Its
/// instance is a function of the owner type only, so a type occurrence of
/// the owner describes it (design.md "Code Instance Tables").
pub const DescriptorMethod = enum(u32) {
    is_eq,
    to_hash,
    to_inspect,

    /// The method's name, as the method registries spell it.
    pub fn text(self: DescriptorMethod) []const u8 {
        return switch (self) {
            .is_eq => base.Ident.IS_EQ_METHOD_NAME,
            .to_hash => base.Ident.TO_HASH_METHOD_NAME,
            .to_inspect => "to_inspect",
        };
    }

    /// The descriptor method that `method` of `names` names, or null for
    /// any other method. It compares method name ids of `names`.
    pub fn fromMethodName(names: *const canonical.CanonicalNameStore, method: canonical.MethodNameId) ?DescriptorMethod {
        for (std.enums.values(DescriptorMethod)) |descriptor| {
            if (names.lookupMethodName(descriptor.text()) == method) return descriptor;
        }
        return null;
    }
};

/// Types of one checked store, each a type id read with what its variables
/// stand for. A term with no bindings is the type as the store writes it;
/// a term with bindings is a type a nominal's backing holds, whose
/// variables are the declaration's formal arguments, each bound to the
/// term of the argument the nominal was given.
///
/// | Slice | One entry per | Holds |
/// |---|---|---|
/// | `terms` | term | its type and its span of `bindings` |
/// | `bindings` | binding of a term | the variable and its term |
pub const TypeTerms = struct {
    pub const Term = struct { ty: CheckedTypeId, bindings: Span = .{} };
    pub const Binding = struct { variable: CheckedTypeId, term: u32 };

    terms: []const Term = &.{},
    bindings: []const Binding = &.{},

    pub fn termBindings(self: *const TypeTerms, term: Term) []const Binding {
        return self.bindings[term.bindings.start..][0..term.bindings.len];
    }

    pub fn deinit(self: *TypeTerms, allocator: Allocator) void {
        allocator.free(self.terms);
        allocator.free(self.bindings);
        self.* = .{};
    }
};

/// The instance inventories of this module's templates (D1 of
/// roc-reify-structural-proposal.md).
///
/// A `Code` site whose function type mentions a quantified variable of the
/// template that holds it is an instance site. Its own module describes it
/// nowhere: each closing use of the template (a use whose types fix those
/// variables) describes it, in the module of the use. A use inside a
/// template with an inventory, of a template with one, at the holder's own
/// variables, is a forward use: its table is an entry of the holder's table.
/// A generic bound call (R7) binds its sites' inputs at each closing use, so
/// each of its sites is an instance site too.
///
/// | Slice | One entry per | Holds |
/// |---|---|---|
/// | `inventories` | template of this module with instance sites or forward uses, ascending by template | its spans of `entries` and `bound_calls` |
/// | `entries` | inventory entry, in inventory order | a site or identity call (with its `recipes` index), or a forward use |
/// | `sites` | instance site or instance identity call of this module, ascending by node | its index in its template's inventory |
/// | `forwards` | forward edge of this module, ascending by edge | its index in its holder's inventory |
/// | `forward_edges` | `forward` entry, in entry order | the edge the entry's table is selected at |
/// | `recipes` | instance site | what a walk in any module reads to describe it |
/// | `scheme_vars` | quantified variable of a recipe's root | a type id of the root's module |
/// | `args` | template-call argument of a recipe | an expression of the site's module |
/// | `modules` | module a recipe's root lives in | its key |
/// | `bound_calls` | generic bound call of this module, by inventory | the call and its spans of `bound_sites` and `bound_leaves` |
/// | `bound_sites` | site of a bound call, in site order | its index in the template's inventory |
/// | `bound_leaves` | leaf of a bound call, in leaf order | the binder pattern of this module |
/// | `refusals` | site or identity call no closing use can describe | the refusal, which the description step reports |
/// | `refused_methods` | method of this module the compiler calls with no written use, bound to a template of another module that has an inventory | the method's key and the refusal, which the description step reports |
/// | `implicits` | `implicit` entry, in entry order | the descriptor method and its owner type's `terms` index |
/// | `terms` | owner type of an `implicit` entry | the type with what its variables stand for |
/// | `closing_edges` | edge of a use, or of a use's evidence, that the module scan records, ascending | its key: the description step can close only these edges |
pub const CodeInventories = struct {
    pub const none: u32 = std.math.maxInt(u32);

    pub const Inventory = struct {
        template: CheckedProcedureTemplateId,
        /// A span of `entries`.
        entries: Span,
        /// The template's generic bound calls, a span of `bound_calls`.
        bound_calls: Span = .{},
    };

    /// A call in a template whose result is a `Code.Bound`, whose type
    /// mentions a variable of the template, and which reads nothing at run
    /// time but through its sites (`CodeReificationSite.BoundReads`). Each
    /// closing use binds its inputs at the use's instance (R7, design.md
    /// "Bound Instance Roots").
    pub const BoundCall = struct {
        call: CIR.Expr.Idx,
        /// The inventory index of each of its sites, in site order: a span
        /// of `bound_sites`.
        sites: Span,
        /// The call's leaves, a span of `bound_leaves`: the order of the
        /// leaf parts of its requirement type, and of the tuple its bound
        /// requirement takes.
        leaves: Span = .{},
    };

    /// A `site` entry is an instance site or an instance identity call:
    /// its recipe's kind says which. An `implicit` entry is a type
    /// occurrence at the template's variables of a nominal whose descriptor
    /// method has an inventory (Q17): the method's table at that type.
    pub const EntryKind = enum { site, forward, implicit };

    pub const Entry = struct {
        kind: EntryKind,
        /// The site, the identity call, the expression a forward edge
        /// stands at, or for an `implicit` entry the expression whose type
        /// holds the occurrence.
        node: CIR.Expr.Idx,
        /// A site's index in `recipes`, an `implicit` entry's index in
        /// `implicits`, a `forward` entry's index in `forward_edges`.
        recipe: u32,
    };

    /// An `implicit` entry: the descriptor method, and the owner type over
    /// the holder's variables, a `terms` index.
    pub const Implicit = struct {
        method: DescriptorMethod,
        owner: u32,
    };

    pub const Indexed = struct { node: CIR.Expr.Idx, index: u32 };

    /// A forward edge and its index in its holder's inventory.
    pub const IndexedEdge = struct {
        edge: code_output.CodeEdge,
        index: u32,

        /// By edge, then by index, so the first entry of an edge comes first.
        pub fn lessThan(_: void, a: IndexedEdge, b: IndexedEdge) bool {
            return switch (code_output.EdgeKey.order(code_output.EdgeKey.of(a.edge), code_output.EdgeKey.of(b.edge))) {
                .lt => true,
                .gt => false,
                .eq => a.index < b.index,
            };
        }
    };

    /// How a closing use describes one entry: a site of each kind (a value
    /// site's `fn_ty` is the value's type), or a `Code.type_id` or
    /// `Code.ty_of` call, whose `root_body` is the call's proxy (Q8, D6).
    pub const RecipeKind = enum { inline_lambda, named_function, template_call, type_id, ty_of, value };

    /// What the walk of one instance site reads, in the module that holds
    /// the site and the module that defines its root. The site's lambda and
    /// its bound capture reads stay in CIR and `ModuleEnv`, where the walk
    /// reads them.
    pub const Recipe = struct {
        kind: RecipeKind,
        view: can.NodeStore.CodeReificationSite.View,
        /// The `f` of the site's `Code(f)`, in the site's module.
        fn_ty: CheckedTypeId,
        region: base.Region,
        /// The module of the root (`modules` index), or `none` for the
        /// site's own module.
        root_module: u32,
        /// The lambda a named site or the site itself describes, the
        /// template's body, or an identity call's proxy.
        root_body: CIR.Expr.Idx,
        /// What the root quantifies over, in the root's module: a span of
        /// `scheme_vars` and the type that holds them, or null for a root
        /// with no scheme.
        scheme_vars: Span,
        scheme_root: ?CheckedTypeId,
        /// Whether the root reads the block around it.
        in_block: bool,
        /// The site's lookup or the template call's callee, in the site's
        /// module.
        use: ?CIR.Expr.Idx,
        /// The call the site is an argument of, whose translator declares
        /// the site's cut.
        translator: ?CIR.Expr.Idx,
        /// A template call's arguments, a span of `args`.
        args: Span,
        /// The bound call (`bound_calls` index) whose inputs a closing use
        /// binds at this site, or `none`.
        bound: u32 = none,
    };

    /// A site or identity call of a template that no closing use can
    /// describe. The description step reports it.
    pub const Refusal = struct {
        node: CIR.Expr.Idx,
        rejection: code_reifier.Rejection,
    };

    /// A method the compiler calls with no written use (Q17), bound to a
    /// template of another module that has an inventory. No closing use
    /// describes that template at the method's instance, so every call the
    /// compiler makes by type treats the method as a rejected declaration.
    /// The key is in this module's names, as its method registry has it.
    pub const RefusedMethod = struct {
        key: static_dispatch.MethodKey,
        rejection: code_reifier.Rejection,
    };

    inventories: []const Inventory = &.{},
    entries: []const Entry = &.{},
    sites: []const Indexed = &.{},
    forwards: []const IndexedEdge = &.{},
    forward_edges: []const code_output.CodeEdge = &.{},
    recipes: []const Recipe = &.{},
    scheme_vars: []const CheckedTypeId = &.{},
    args: []const CIR.Expr.Idx = &.{},
    modules: []const CheckedModuleArtifactKey = &.{},
    bound_calls: []const BoundCall = &.{},
    bound_sites: []const u32 = &.{},
    bound_leaves: []const CIR.Pattern.Idx = &.{},
    /// Ascending by node.
    refusals: []const Refusal = &.{},
    /// In method registry order.
    refused_methods: []const RefusedMethod = &.{},
    /// One per `implicit` entry, in entry order.
    implicits: []const Implicit = &.{},
    /// The owner types of `implicits`, in this module's store.
    terms: TypeTerms = .{},
    /// Ascending, each once.
    closing_edges: []const code_output.EdgeKey = &.{},

    /// Whether the description step can give `edge` a closing table: the
    /// module scan recorded it as the edge of a use or of a use's evidence.
    /// Lowering reads the code output at such an edge only.
    pub fn mayClose(self: *const CodeInventories, edge: code_output.CodeEdge) bool {
        return std.sort.binarySearch(code_output.EdgeKey, self.closing_edges, code_output.EdgeKey.of(edge), code_output.EdgeKey.order) != null;
    }

    /// Whether the method `key` of this module is refused (Q17): every call
    /// the compiler makes by type treats it as a rejected declaration.
    pub fn refusesMethod(self: *const CodeInventories, key: static_dispatch.MethodKey) bool {
        for (self.refused_methods) |refused| {
            if (std.meta.eql(refused.key, key)) return true;
        }
        return false;
    }

    /// The inventory of `template`, or null for a template with none.
    pub fn inventoryOf(self: *const CodeInventories, template: CheckedProcedureTemplateId) ?Inventory {
        const index = std.sort.binarySearch(Inventory, self.inventories, template, struct {
            fn order(key: CheckedProcedureTemplateId, item: Inventory) std.math.Order {
                return std.math.order(@backingInt(key), @backingInt(item.template));
            }
        }.order) orelse return null;
        return self.inventories[index];
    }

    /// The entries of one inventory, in inventory order.
    pub fn inventoryEntries(self: *const CodeInventories, inventory: Inventory) []const Entry {
        return self.entries[inventory.entries.start..][0..inventory.entries.len];
    }

    /// The generic bound calls of one inventory.
    pub fn inventoryBoundCalls(self: *const CodeInventories, inventory: Inventory) []const BoundCall {
        return self.bound_calls[inventory.bound_calls.start..][0..inventory.bound_calls.len];
    }

    fn indexOf(items: []const Indexed, node: CIR.Expr.Idx) ?u32 {
        const index = std.sort.binarySearch(Indexed, items, node, struct {
            fn order(key: CIR.Expr.Idx, item: Indexed) std.math.Order {
                return std.math.order(@backingInt(key), @backingInt(item.node));
            }
        }.order) orelse return null;
        return items[index].index;
    }

    /// The inventory index of the instance site or identity call at `node`,
    /// or null where `node` is none.
    pub fn siteIndex(self: *const CodeInventories, node: CIR.Expr.Idx) ?u32 {
        return indexOf(self.sites, node);
    }

    /// Whether the site or identity call at `node` is described at each
    /// closing use of its template.
    pub fn isInstanceSite(self: *const CodeInventories, node: CIR.Expr.Idx) bool {
        return self.siteIndex(node) != null;
    }

    /// The inventory index of the forward edge `edge`, or null.
    pub fn forwardIndex(self: *const CodeInventories, edge: code_output.CodeEdge) ?u32 {
        const key = code_output.EdgeKey.of(edge);
        const index = std.sort.binarySearch(IndexedEdge, self.forwards, key, struct {
            fn order(target: code_output.EdgeKey, item: IndexedEdge) std.math.Order {
                return code_output.EdgeKey.order(target, code_output.EdgeKey.of(item.edge));
            }
        }.order) orelse return null;
        return self.forwards[index].index;
    }

    /// The index in `bound_calls` of the generic bound call at `call`, or
    /// null where `call` is none.
    pub fn boundCallIndex(self: *const CodeInventories, call: CIR.Expr.Idx) ?u32 {
        for (self.bound_calls, 0..) |bound, index| {
            if (bound.call == call) return @intCast(index);
        }
        return null;
    }

    /// The inventory indices of the sites of `call`, in site order.
    pub fn boundCallSites(self: *const CodeInventories, call: BoundCall) []const u32 {
        return self.bound_sites[call.sites.start..][0..call.sites.len];
    }

    /// The leaves of generic bound call `call_index`.
    pub fn boundCallLeaves(self: *const CodeInventories, call_index: u32) []const CIR.Pattern.Idx {
        const leaves = self.bound_calls[call_index].leaves;
        return self.bound_leaves[leaves.start..][0..leaves.len];
    }

    /// The quantified variables of a recipe's root.
    pub fn recipeSchemeVars(self: *const CodeInventories, recipe: Recipe) []const CheckedTypeId {
        return self.scheme_vars[recipe.scheme_vars.start..][0..recipe.scheme_vars.len];
    }

    /// The arguments of a template-call recipe.
    pub fn recipeArgs(self: *const CodeInventories, recipe: Recipe) []const CIR.Expr.Idx {
        return self.args[recipe.args.start..][0..recipe.args.len];
    }

    fn destroy(self: *CodeInventories, allocator: Allocator) void {
        allocator.free(self.inventories);
        allocator.free(self.entries);
        allocator.free(self.sites);
        allocator.free(self.forwards);
        allocator.free(self.forward_edges);
        allocator.free(self.recipes);
        allocator.free(self.scheme_vars);
        allocator.free(self.args);
        allocator.free(self.modules);
        allocator.free(self.bound_calls);
        allocator.free(self.bound_sites);
        allocator.free(self.bound_leaves);
        allocator.free(self.refusals);
        allocator.free(self.refused_methods);
        allocator.free(self.implicits);
        self.terms.deinit(allocator);
        allocator.free(self.closing_edges);
        allocator.destroy(self);
    }
};

/// The code facts of one checked module, owned by the module's body analyses
/// (`body_analyses.BodyAnalyses.code`). `allocator` must be safe to use from
/// every thread that reads the module.
pub const CodeAnalyses = struct {
    allocator: Allocator,
    io: std.Io,
    cuts_slot: collections.OnceSlot(*CodeCuts, .code_cuts) = .empty,
    inventories_slot: collections.OnceSlot(*CodeInventories, .code_inventories) = .empty,

    pub fn init(allocator: Allocator, io: std.Io) CodeAnalyses {
        return .{ .allocator = allocator, .io = io };
    }

    pub fn deinit(self: *CodeAnalyses) void {
        if (self.cuts_slot.peek()) |table| table.destroy(self.allocator);
        if (self.inventories_slot.peek()) |plan| plan.destroy(self.allocator);
        self.* = undefined;
    }

    /// The module's cuts. `code_reifier.moduleCuts(allocator, inputs)`
    /// computes them on first demand; it writes no `ConstStore`.
    pub fn cuts(self: *CodeAnalyses, inputs: code_reifier.CutInputs) Allocator.Error!*const CodeCuts {
        return self.cuts_slot.getOrCompute(self.io, Allocator.Error, CutsRequest{ .analyses = self, .inputs = inputs }, CutsRequest.compute);
    }

    const CutsRequest = struct {
        analyses: *CodeAnalyses,
        inputs: code_reifier.CutInputs,

        fn compute(request: CutsRequest) Allocator.Error!*CodeCuts {
            return code_reifier.moduleCuts(request.analyses.allocator, request.inputs);
        }
    };

    /// The inventories of the module's templates.
    /// `code_reifier.planModule(allocator, inputs)` computes them on first
    /// demand. It may demand the inventories and cuts of imported modules,
    /// which are acyclic.
    pub fn inventories(self: *CodeAnalyses, inputs: code_reifier.PlanInputs) Allocator.Error!*const CodeInventories {
        return self.inventories_slot.getOrCompute(self.io, Allocator.Error, InventoriesRequest{ .analyses = self, .inputs = inputs }, InventoriesRequest.compute);
    }

    const InventoriesRequest = struct {
        analyses: *CodeAnalyses,
        inputs: code_reifier.PlanInputs,

        fn compute(request: InventoriesRequest) Allocator.Error!*CodeInventories {
            return code_reifier.planModule(request.analyses.allocator, request.inputs);
        }
    };
};
