//! The description step of compile-time evaluation (design.md "Code
//! Reification").
//!
//! The step runs first in the evaluation of each module whose code output
//! is `pending`. It reads only sealed data and the code slots of the module
//! and its imports, never an evaluation output, so the steps of all
//! prepared modules are independent. It writes only the module's
//! evaluation output: `Code` values into its `ConstStore`, and the
//! `CodeOutput` column. It reports each refusal into the module's problem
//! store.
//!
//! | Order | What | Output | Report |
//! |---|---|---|---|
//! | 1 | cut problems (`codeCuts` slot) | none | each problem |
//! | 1 | refused methods (`codeInventories` slot, Q17) | none | each refusal |
//! | 2 | identity calls, node order | `identities` | each refusal |
//! | 3 | sites, node order | `sites` | each refusal |
//! | 4 | closing edges: uses in node order, then requirements by requires index, then evidence node and contract call edges | `edge_tables`, `tables`, `root_bounds` | each refusal |
//! | 5 | bound inputs, site order | `bindings`, refused `sites` | each refused site |

const std = @import("std");
const builtin = @import("builtin");
const base = @import("base");
const can = @import("can");
const check = @import("check");
const collections = @import("collections");

const Allocator = std.mem.Allocator;
const CIR = can.CIR;
const ModuleEnv = can.ModuleEnv;
const checked = check.CheckedArtifact;
const code_reifier = check.CodeReifier;
const code_output = check.CodeOutput;
const problem = check.problem;

const CheckedModuleArtifact = checked.CheckedModuleArtifact;
const CheckedModuleArtifactKey = checked.CheckedModuleArtifactKey;
const ImportedModuleView = checked.ImportedModuleView;
const CodeOutput = code_output.CodeOutput;
const Lookups = check.CodeLookups.Lookups;
const Span = code_output.Span;
const ExprId = CIR.Expr.Idx;

fn invariant(comptime message: []const u8) noreturn {
    base.invariant("code description invariant violated: " ++ message, .{});
}

/// Run the description step of `module`, whose code output is `pending`.
///
/// `reach` holds every module the evaluation sees, the module itself
/// included or not. `problem_store` is null for an evaluation that reports
/// nothing: the output is the same.
pub fn describeModule(
    gpa: Allocator,
    module: *CheckedModuleArtifact,
    problem_store: ?*problem.Store,
    reach: []const ImportedModuleView,
) Allocator.Error!void {
    std.debug.assert(module.code_output.state == .pending);
    // The module's inventories, its imports' first (`CodeLookups.codeInventories`).
    _ = try check.CodeLookups.codeInventories(gpa, checked.importedView(module), reach);
    var lookups = try Lookups.init(gpa, checked.importedView(module), reach);
    defer lookups.deinit(gpa);
    const inputs: code_reifier.ModuleInputs = .{
        .sources = code_reifier.Reifier.artifactSources(module),
        .lookup = lookups.own.lookup(),
    };
    const bodies = inputs.sources.bodies;
    const key = module.key;

    // 1. The cuts this module declares.
    const cuts = try bodies.codeCuts(inputs);
    if (problem_store) |problems| {
        for (cuts.problems) |refused| {
            _ = try problems.appendProblem(.{ .staged_code = .{
                .reason = switch (refused.kind) {
                    .not_a_function => .primitive_not_a_function,
                    .listed_twice => .primitive_listed_twice,
                    .already_primitive => .primitive_already_primitive,
                    .not_a_list => .primitives_not_a_list,
                },
                .region = refused.region,
            } });
        }
    }

    // The methods the compiler calls that are bound to a template of
    // another module with an inventory, refused at the method (Q17).
    if (problem_store) |problems| {
        for ((try bodies.codeInventories(inputs)).refused_methods) |refused| {
            try appendStagedCodeRefusal(gpa, problems, key, refused.rejection.region, refused.rejection, .none, .{ .start = 0, .count = 0 });
        }
    }

    var builder = OutputBuilder{ .gpa = gpa };
    defer builder.deinit();

    // 2. Each `Code.prim`, `Code.type_id` and `Code.ty_of` call is the
    // constant it computes. A call of a template's inventory is described
    // at each closing use instead.
    const identities = try code_reifier.describeIdentities(gpa, &module.const_store, inputs);
    defer gpa.free(identities);
    for (identities) |identity| {
        switch (identity.outcome) {
            .node => |node| try builder.identities.append(gpa, .{ .node = identity.call, .outcome = .value, .value = node }),
            .rejected => |rejection| {
                try builder.identities.append(gpa, refusedIdentity(identity.call));
                if (problem_store) |problems| try appendStagedCodeRefusal(gpa, problems, key, identity.region, rejection, .none, .{ .start = 0, .count = 0 });
            },
            .not_a_definition, .not_nominal => {
                try builder.identities.append(gpa, refusedIdentity(identity.call));
                if (problem_store) |problems| {
                    _ = try problems.appendProblem(.{
                        .staged_code = .{
                            .reason = switch (identity.outcome) {
                                .not_a_definition => .prim_not_a_definition,
                                .not_nominal => .type_id_not_nominal,
                                .node, .rejected => unreachable, // the arms above take them
                            },
                            .region = identity.region,
                        },
                    });
                }
            },
        }
    }

    // 3 and 4. The sites and the closing uses share one walk.
    const requirement_uses = try checked.platformRequirementUses(gpa, module);
    defer gpa.free(requirement_uses);
    const description = try code_reifier.Description.init(gpa, &module.const_store, .{
        .module = inputs,
        .roots = module.compile_time_roots.roots,
        .requirement_uses = requirement_uses,
    });
    defer description.deinit();

    const outcomes = try description.describeSites();
    defer freeSiteOutcomes(gpa, outcomes);
    // Whether each outcome is refused: a rejected walk, or a site whose
    // bound call cannot supply its slots (step 5).
    const refused = try gpa.alloc(bool, outcomes.len);
    defer gpa.free(refused);
    for (outcomes, refused) |site, *is_refused| {
        is_refused.* = site.outcome == .rejected;
        switch (site.outcome) {
            .reified => {},
            .rejected => |rejection| if (problem_store) |problems| {
                try appendStagedCodeRefusal(gpa, problems, key, site.region, rejection, site.chain_stop, try chainEndType(gpa, problems, module.moduleEnvConst(), site, rejection));
            },
        }
    }

    var closed = try description.closeUses();
    defer closed.deinit(gpa);
    for (closed.refused) |use| {
        try builder.edge_tables.append(gpa, .{ .edge = .of(use.edge), .outcome = .refused, .table = code_output.refused_table });
        if (problem_store) |problems| try appendStagedCodeRefusal(gpa, problems, key, use.region, use.rejection, .none, .{ .start = 0, .count = 0 });
    }
    for (closed.refused_implicits) |occurrence| {
        if (problem_store) |problems| try appendStagedCodeRefusal(gpa, problems, key, occurrence.region, occurrence.rejection, .none, .{ .start = 0, .count = 0 });
    }
    for (closed.edges) |edge| try builder.edge_tables.append(gpa, .{ .edge = .of(edge.edge), .outcome = .value, .table = @fromBackingInt(edge.table) });
    try builder.takeTables(&closed.tables, closed.implicit_refused);

    // 5. The input slots of each bound call.
    try bindCodeInputs(gpa, module, bodies, outcomes, refused, &builder, problem_store);

    // The first slot of a site is the number of slots of the earlier sites
    // its call binds, as the walk counted it (site order).
    var call_slots = std.AutoHashMapUnmanaged(u32, u32).empty;
    defer call_slots.deinit(gpa);
    for (outcomes, refused) |site, is_refused| {
        const first_slot: u32 = if (site.bound_call) |call| slots: {
            const entry = try call_slots.getOrPut(gpa, call);
            if (!entry.found_existing) entry.value_ptr.* = 0;
            const first = entry.value_ptr.*;
            entry.value_ptr.* += @intCast(site.slots.len);
            break :slots first;
        } else 0;
        if (is_refused) {
            try builder.sites.append(gpa, .{ .node = site.expr, .outcome = .refused, .value = code_output.refused_value, .reads = .{}, .first_slot = 0 });
            continue;
        }
        try builder.sites.append(gpa, .{
            .node = site.expr,
            .outcome = .value,
            .value = site.outcome.reified,
            .reads = try builder.appendReads(site.reads),
            .first_slot = first_slot,
        });
    }
    // The name a template call calls is never read: the call stands for a
    // description built elsewhere, so nothing is walked for it. It reads as
    // refused and reports nothing.
    for (module.moduleEnvConst().store.codeReificationSites()) |site| {
        if (site.kind != .template_callee) continue;
        const node: ExprId = @fromBackingInt(@intCast(site.node_idx));
        if (!bodies.index().isCodeSite(node)) continue;
        try builder.sites.append(gpa, .{ .node = node, .outcome = .refused, .value = code_output.refused_value, .reads = .{}, .first_slot = 0 });
    }

    const provenance = try description.takeProvenance();
    defer {
        for (provenance) |*entry| entry.deinit(gpa);
        gpa.free(provenance);
    }
    module.code_output = try builder.finish(module.evaluationAllocator(), provenance);
}

fn refusedIdentity(call: ExprId) code_output.IdentityRecord {
    return .{ .node = call, .outcome = .refused, .value = code_output.refused_value };
}

fn freeSiteOutcomes(gpa: Allocator, outcomes: []code_reifier.SiteOutcome) void {
    for (outcomes) |outcome| {
        for (outcome.slots) |slot| {
            gpa.free(slot.steps);
            gpa.free(slot.shape);
        }
        gpa.free(outcome.slots);
        gpa.free(outcome.reads);
    }
    gpa.free(outcomes);
}

/// The columns of one module's `CodeOutput` while the step builds them, in
/// scratch storage. `finish` sorts the keyed columns and copies them into
/// the artifact's evaluation storage.
const OutputBuilder = struct {
    /// First: `deinit` frees every field after it.
    gpa: Allocator,
    sites: std.ArrayList(code_output.SiteRecord) = .empty,
    identities: std.ArrayList(code_output.IdentityRecord) = .empty,
    edge_tables: std.ArrayList(code_output.EdgeTableRecord) = .empty,
    tables: std.ArrayList(code_output.TableRecord) = .empty,
    table_entries: std.ArrayList(code_output.EntryRecord) = .empty,
    bound_entries: std.ArrayList(code_output.BoundEntryRecord) = .empty,
    first_slots: std.ArrayList(u32) = .empty,
    bindings: std.ArrayList(code_output.BindingRecord) = .empty,
    root_bounds: std.ArrayList(code_output.RootBoundRecord) = .empty,
    slots: std.ArrayList(checked.CheckedCodeSlot) = .empty,
    slot_steps: std.ArrayList(checked.CheckedCodeSlotStep) = .empty,
    slot_shapes: std.ArrayList(u32) = .empty,
    reads: std.ArrayList(checked.CheckedCodeRead) = .empty,
    implicit_instances: std.ArrayList(code_output.ImplicitInstanceRecord) = .empty,
    owner_terms: std.ArrayList(code_output.OwnerTermRecord) = .empty,
    owner_bindings: std.ArrayList(code_output.OwnerBindingRecord) = .empty,
    owner_members: std.ArrayList(code_output.OwnerMemberRecord) = .empty,
    owner_member_terms: std.ArrayList(u32) = .empty,
    owner_modules: std.ArrayList(checked.CheckedModuleArtifactKey) = .empty,

    fn deinit(self: *OutputBuilder) void {
        const gpa = self.gpa;
        inline for (@typeInfo(OutputBuilder).@"struct".field_names[1..]) |name| @field(self, name).deinit(gpa);
    }

    /// Take the tables the closing uses built: their pools are the first
    /// entries of this output's pools, so their spans hold as they are.
    fn takeTables(self: *OutputBuilder, tables: *const code_reifier.InstanceTables, implicit_refused: []const bool) Allocator.Error!void {
        const gpa = self.gpa;
        std.debug.assert(self.reads.items.len == 0 and self.slots.items.len == 0);
        for (tables.tables, tables.table_templates, tables.table_bounds) |entries, template, bounds| {
            try self.tables.append(gpa, .{
                .template = .{ .module = template.module, .template = template.template },
                .entries = .{ .start = entries.start, .len = entries.len },
                .bound_entries = .{ .start = bounds.start, .len = bounds.len },
            });
        }
        for (tables.table_entries) |entry| try self.table_entries.append(gpa, .{
            .kind = switch (entry.kind) {
                .node => .node,
                .table => .forward,
            },
            .value = entry.value,
            .reads = .{ .start = entry.reads.start, .len = entry.reads.len },
        });
        for (tables.bound_entries) |entry| try self.bound_entries.append(gpa, .{
            .call = entry.call,
            .slots = .{ .start = entry.slots.start, .len = entry.slots.len },
            .first_slots = .{ .start = entry.first_slots.start, .len = entry.first_slots.len },
        });
        for (tables.root_bounds) |bound| try self.root_bounds.append(gpa, .{ .root = bound.root, .entry = bound.entry });
        for (tables.implicit_instances, implicit_refused) |instance, is_refused| try self.implicit_instances.append(gpa, .{
            .method = instance.method,
            .outcome = if (is_refused) .refused else .value,
            .owner = instance.owner,
            .table = if (is_refused) code_output.refused_table else @fromBackingInt(instance.table),
        });
        for (tables.owner_terms) |term| try self.owner_terms.append(gpa, .{
            .module = term.module,
            .kind = term.kind,
            .ty = term.ty,
            .bindings = .{ .start = term.bindings.start, .len = term.bindings.len },
            .members = .{ .start = term.members.start, .len = term.members.len },
        });
        for (tables.owner_members) |member| try self.owner_members.append(gpa, .{
            .module = member.module,
            .label = member.label,
            .kind = member.kind,
            .terms = .{ .start = member.terms.start, .len = member.terms.len },
        });
        try self.owner_member_terms.appendSlice(gpa, tables.owner_member_terms);
        for (tables.owner_bindings) |binding| try self.owner_bindings.append(gpa, .{ .variable = binding.variable, .term = binding.term });
        try self.owner_modules.appendSlice(gpa, tables.owner_modules);
        try self.reads.appendSlice(gpa, tables.reads);
        try self.slots.appendSlice(gpa, tables.slots);
        try self.slot_steps.appendSlice(gpa, tables.slot_steps);
        try self.slot_shapes.appendSlice(gpa, tables.slot_shapes);
        try self.first_slots.appendSlice(gpa, tables.first_slots);
    }

    fn appendReads(self: *OutputBuilder, reads: []const checked.CheckedCodeRead) Allocator.Error!Span {
        if (reads.len == 0) return .{};
        const start: u32 = @intCast(self.reads.items.len);
        try self.reads.appendSlice(self.gpa, reads);
        return .{ .start = start, .len = @intCast(reads.len) };
    }

    /// Append one slot with its projections and shape.
    fn appendSlot(self: *OutputBuilder, slot: code_reifier.SlotSource) Allocator.Error!void {
        const gpa = self.gpa;
        const steps_start: u32 = @intCast(self.slot_steps.items.len);
        for (slot.steps) |step| try self.slot_steps.append(gpa, switch (step) {
            .field => |label| .{ .kind = .field, .value = @backingInt(label) },
            .index => |index| .{ .kind = .index, .value = index },
            .unwrap => .{ .kind = .unwrap, .value = 0 },
        });
        const shape_start: u32 = @intCast(self.slot_shapes.items.len);
        try self.slot_shapes.appendSlice(gpa, slot.shape);
        try self.slots.append(gpa, .{
            .source = slot.source,
            .steps_start = steps_start,
            .steps_len = @intCast(slot.steps.len),
            .shape_start = shape_start,
            .shape_len = @intCast(slot.shape.len),
            .encoder = if (slot.encoder) |encoder| .some(encoder) else .none,
        });
    }

    fn finish(self: *OutputBuilder, allocator: Allocator, provenance: []const code_reifier.SiteProvenance) Allocator.Error!CodeOutput {
        std.mem.sort(code_output.SiteRecord, self.sites.items, {}, nodeLessThan(code_output.SiteRecord));
        // By edge, a refusal first: an edge two uses share (a node that two
        // method calls target, or that a call targets and the evidence of
        // another use reaches) has one record. A use's refusal depends on
        // its node alone, so the refusal of one call refuses the node: each use
        // that reaches the node is refused too, and crashes in place.
        std.mem.sort(code_output.EdgeTableRecord, self.edge_tables.items, {}, struct {
            fn lessThan(_: void, a: code_output.EdgeTableRecord, b: code_output.EdgeTableRecord) bool {
                return switch (code_output.EdgeKey.order(a.edge, b.edge)) {
                    .lt => true,
                    .gt => false,
                    .eq => a.outcome == .refused and b.outcome == .value,
                };
            }
        }.lessThan);
        {
            var kept: usize = 0;
            for (self.edge_tables.items) |record| {
                if (kept != 0 and code_output.EdgeKey.order(self.edge_tables.items[kept - 1].edge, record.edge) == .eq) {
                    // `closeEdge` records each edge's table once.
                    std.debug.assert(record.outcome == .refused or self.edge_tables.items[kept - 1].outcome == .refused);
                    continue;
                }
                self.edge_tables.items[kept] = record;
                kept += 1;
            }
            self.edge_tables.shrinkRetainingCapacity(kept);
        }
        std.mem.sort(code_output.BindingRecord, self.bindings.items, {}, struct {
            fn lessThan(_: void, a: code_output.BindingRecord, b: code_output.BindingRecord) bool {
                return @backingInt(a.call) < @backingInt(b.call);
            }
        }.lessThan);
        // The identity outcomes and the root bounds come sorted.
        var output: CodeOutput = .{};
        errdefer output.deinit(allocator);
        output.sites = try allocator.dupe(code_output.SiteRecord, self.sites.items);
        output.identities = try allocator.dupe(code_output.IdentityRecord, self.identities.items);
        output.edge_tables = try allocator.dupe(code_output.EdgeTableRecord, self.edge_tables.items);
        output.tables = try allocator.dupe(code_output.TableRecord, self.tables.items);
        output.table_entries = try allocator.dupe(code_output.EntryRecord, self.table_entries.items);
        output.bound_entries = try allocator.dupe(code_output.BoundEntryRecord, self.bound_entries.items);
        output.first_slots = try allocator.dupe(u32, self.first_slots.items);
        output.bindings = try allocator.dupe(code_output.BindingRecord, self.bindings.items);
        output.root_bounds = try allocator.dupe(code_output.RootBoundRecord, self.root_bounds.items);
        output.slots = try allocator.dupe(checked.CheckedCodeSlot, self.slots.items);
        output.slot_steps = try allocator.dupe(checked.CheckedCodeSlotStep, self.slot_steps.items);
        output.slot_shapes = try allocator.dupe(u32, self.slot_shapes.items);
        output.reads = try allocator.dupe(checked.CheckedCodeRead, self.reads.items);
        output.implicit_instances = try allocator.dupe(code_output.ImplicitInstanceRecord, self.implicit_instances.items);
        output.owner_terms = try allocator.dupe(code_output.OwnerTermRecord, self.owner_terms.items);
        output.owner_bindings = try allocator.dupe(code_output.OwnerBindingRecord, self.owner_bindings.items);
        output.owner_members = try allocator.dupe(code_output.OwnerMemberRecord, self.owner_members.items);
        output.owner_member_terms = try allocator.dupe(u32, self.owner_member_terms.items);
        output.owner_modules = try allocator.dupe(checked.CheckedModuleArtifactKey, self.owner_modules.items);
        output.provenance = try code_output.CodeProvenanceTable.init(allocator, provenance);
        output.state = .complete;
        if (builtin.mode == .debug) output.validate() catch invariant("the description step wrote an inconsistent output");
        return output;
    }

    fn nodeLessThan(comptime Record: type) fn (void, Record, Record) bool {
        return struct {
            fn lessThan(_: void, a: Record, b: Record) bool {
                return @backingInt(a.node) < @backingInt(b.node);
            }
        }.lessThan;
    }
};

/// Record, on each call whose result is a `Code.Bound`, the input slots of
/// the sites it binds (roc-reify-proposal.md section 10.1), and refuse each
/// site whose slots the call cannot supply.
///
/// The program reads the call's compile-time value with the slot values
/// added, so the call has to be a compile-time root of its own whose type
/// the call fixes. The call's slots are the slots of its sites in site
/// order, so a refused site refuses the call.
fn bindCodeInputs(
    gpa: Allocator,
    module: *const CheckedModuleArtifact,
    bodies: check.CheckedBodies.CheckedBodies,
    outcomes: []const code_reifier.SiteOutcome,
    refused: []bool,
    builder: *OutputBuilder,
    problem_store: ?*problem.Store,
) Allocator.Error!void {
    for (outcomes, 0..) |first, first_index| {
        const call_node = first.bound_call orelse continue;
        // The first site of a call binds the whole group.
        const group_start = for (outcomes[0..first_index]) |earlier| {
            if (earlier.bound_call == call_node) break false;
        } else true;
        if (!group_start) continue;
        var slot_count: usize = 0;
        var any_refused = false;
        for (outcomes[first_index..], refused[first_index..]) |site, is_refused| {
            if (site.bound_call != call_node) continue;
            if (is_refused) any_refused = true;
            slot_count += site.slots.len;
        }
        if (slot_count == 0) continue;
        const call: ExprId = @fromBackingInt(call_node);
        const detail: []const u8 = refusal: {
            if (any_refused) break :refusal "the call also binds the inputs of a site that was refused";
            // Hoist selection recorded why the call has no root.
            const entry = module.hoisted_constants.lookupByExpr(call) orelse break :refusal switch (first.bound_root) {
                .runtime_value => "a translator that receives captured inputs runs while the compiler runs, and so does each call of its chain, so each argument of those calls outside a lambda must be fixed then. Read a value known only when the program runs in a lambda at a `Code` place instead, such as `|_| n`: the value is then an input slot. So type the parameter as `Code(a)`, or read the value in a lambda",
                .open_type => "a translator that receives captured inputs runs once while the compiler runs, at the one type the call has. The type of this call holds a type variable that neither its arguments nor its lambdas fix, so the call has no one type to run at. Fix the type so that the call's result has no type variable, such as with an annotation that names a concrete type",
                .other => "a translator that receives captured inputs runs while the compiler runs, and so does each call of its chain, so the compiler must be able to compute the call then, from its lambdas and fixed values",
            };
            std.debug.assert(entry.pattern.get() == null);
            if (builtin.mode == .debug) std.debug.assert(try boundRootTypeIsFixed(gpa, bodies.types, bodies.expr(call).ty));
            const slots_start: u32 = @intCast(builder.slots.items.len);
            for (outcomes[first_index..]) |site| {
                if (site.bound_call != call_node) continue;
                for (site.slots) |slot| try builder.appendSlot(slot);
            }
            try builder.bindings.append(gpa, .{
                .call = call,
                .outcome = .value,
                .slots = .{ .start = slots_start, .len = @intCast(slot_count) },
            });
            continue;
        };
        try builder.bindings.append(gpa, .{ .call = call, .outcome = .refused, .slots = .{} });
        // Each site of the call that reads a slot is refused.
        for (outcomes[first_index..], refused[first_index..]) |site, *is_refused| {
            if (site.bound_call != call_node or site.slots.len == 0) continue;
            if (is_refused.*) continue;
            is_refused.* = true;
            const problems = problem_store orelse continue;
            // A value site has one slot, which reads the value itself.
            const value_site = site.slots[0].source.kind == .value_site;
            _ = try problems.appendProblem(.{ .staged_code = .{
                .reason = if (value_site) .value_not_bound else .input_not_bound,
                .region = bodies.expr(site.expr).source_region,
                .detail = try problems.putExtraString(detail),
                .open = null,
            } });
        }
    }
}

/// Whether the type of a call that binds input slots holds no type variable.
/// Hoisting keeps only a root whose type is concrete, so this is a debug
/// check. The kind variable of an undetermined record field is no type
/// variable here: the walk refuses a site whose type mentions a kind
/// variable of its template (an instance site), and any other undetermined
/// kind is `required` where the root is evaluated and where the program
/// reads it, as Monotype's relation freeze commits it.
fn boundRootTypeIsFixed(gpa: Allocator, types: checked.CheckedTypeStoreView, root: checked.CheckedTypeId) Allocator.Error!bool {
    var visited: collections.DenseMapUnmanaged(checked.CheckedTypeId, void) = .empty;
    defer visited.deinit(gpa);
    var work = std.ArrayList(checked.CheckedTypeId).empty;
    defer work.deinit(gpa);
    try work.append(gpa, root);
    while (work.pop()) |id| {
        if (!try types.rootHasIdentityVariables(id)) continue;
        if ((try visited.getOrPut(gpa, id)).found_existing) continue;
        switch (types.payload(id)) {
            .pending, .flex, .rigid => return false,
            .field_kind, .err, .empty_record, .empty_tag_union => {},
            .alias => |alias| {
                try work.append(gpa, alias.backing);
                try work.appendSlice(gpa, alias.args);
            },
            .record => |record| {
                for (0..record.fields.len()) |field_index| try work.append(gpa, record.fields.get(field_index).ty);
                try work.append(gpa, record.ext);
            },
            .tuple => |items| try work.appendSlice(gpa, items),
            .nominal => |nominal| {
                try work.appendSlice(gpa, nominal.args);
                try work.appendSlice(gpa, nominal.padding_field_types);
            },
            .function => |function| {
                try work.appendSlice(gpa, function.args);
                try work.append(gpa, function.ret);
            },
            .tag_union => |tag_union| {
                for (0..tag_union.tags.len()) |tag_index| try work.appendSlice(gpa, tag_union.tags.get(tag_index).args);
                try work.append(gpa, tag_union.ext);
            },
        }
    }
    return true;
}

/// Report a refusal of the walk at `site_region`: a site, or a closing use
/// (D1). A refusal outside that region's own source (another module's, or a
/// callee or constant this module defines elsewhere) is shown where it is,
/// and the site or use is where the walk reached it from (F4, D9).
/// `chain_stop` is what stopped the calls that carry a site no call binds,
/// and `chain_end_type` the type the chain ended in.
fn appendStagedCodeRefusal(
    gpa: Allocator,
    problems: *problem.Store,
    artifact_key: CheckedModuleArtifactKey,
    site_region: base.Region,
    rejection: code_reifier.Rejection,
    chain_stop: can.NodeStore.CodeReificationSite.ChainStop,
    chain_end_type: problem.ExtraStringIdx,
) Allocator.Error!void {
    // The checker reported the error that stopped the walk.
    if (rejection.kind == .checking_error) return;
    const detail = if (rejection.open) |open|
        try openVariableDetail(gpa, problems, open)
    else
        try problems.putExtraString(rejection.detail);
    const foreign_place = !CheckedModuleArtifactKey.eql(rejection.module.artifact, artifact_key);
    const reached_place = foreign_place or !regionWithin(rejection.region, site_region);
    _ = try problems.appendProblem(.{ .staged_code = .{
        .reason = stagedCodeReason(rejection.kind),
        .chain_stop = if (rejection.kind == .capture) chain_stop else .none,
        .chain_end_type = chain_end_type,
        .region = if (reached_place) site_region else rejection.region,
        .reached = if (!reached_place)
            null
        else if (foreign_place)
            .{ .foreign = try foreignRefusalPlace(problems, rejection.module.env, rejection.region) }
        else
            .{ .local = rejection.region },
        .detail = detail,
        .open = if (rejection.open) |open| .{
            .cause = switch (open.cause) {
                .use_leaves_open => .use_leaves_open,
                .annotation_leaves_open => .annotation_leaves_open,
                .inferred => .inferred,
                .inferred_use_leaves_open => .inferred_use_leaves_open,
            },
            .place = switch (open.place) {
                .parameter => .parameter,
                .result => .result,
                .expression => .expression,
                .use => .use,
            },
        } else null,
    } });
}

/// The type of the expression a refused capture's chain ended in, written
/// for the report, when the chain ended with no call whose result is the
/// opt-in. Empty otherwise.
fn chainEndType(
    gpa: Allocator,
    problems: *problem.Store,
    env: *const ModuleEnv,
    site: code_reifier.SiteOutcome,
    rejection: code_reifier.Rejection,
) Allocator.Error!problem.ExtraStringIdx {
    const empty: problem.ExtraStringIdx = .{ .start = 0, .count = 0 };
    if (rejection.kind != .capture or site.chain_stop != .end) return empty;
    const end = site.chain_end orelse invariant("a chain stopped at its end records no expression it ended in");
    const text = try env.writeTypeOneLine(gpa, ModuleEnv.varFrom(end));
    defer gpa.free(text);
    return problems.putExtraString(text);
}

/// Whether `inner` lies inside `outer`, both regions of one module's source.
fn regionWithin(inner: base.Region, outer: base.Region) bool {
    return outer.start.offset <= inner.start.offset and inner.end.offset <= outer.end.offset;
}

/// A refusal's place outside the site's own source: its module's file, and
/// the lines and the 1-based span of `region` there (F4, D9).
fn foreignRefusalPlace(problems: *problem.Store, env: *const ModuleEnv, region: base.Region) Allocator.Error!problem.StagedCode.Foreign {
    const info = env.calcRegionInfo(region);
    return .{
        .path = try problems.putExtraString(env.diagnosticSourceName()),
        .line_text = try problems.putExtraString(info.calculateLineText(env.common.source, env.getLineStarts())),
        .start_line = info.start_line_idx + 1,
        .start_column = info.start_col_idx + 1,
        .end_line = info.end_line_idx + 1,
        .end_column = info.end_col_idx + 1,
    };
}

/// What a refusal at a type variable names: the variable, as its annotation
/// wrote it, and the place in the function it stands in.
fn openVariableDetail(
    gpa: Allocator,
    problems: *problem.Store,
    open: code_reifier.OpenVariable,
) Allocator.Error!problem.ExtraStringIdx {
    var text = std.ArrayList(u8).empty;
    defer text.deinit(gpa);
    if (open.name) |name| {
        try text.print(gpa, "the type variable {s}", .{name});
    } else {
        try text.appendSlice(gpa, "an unnamed type variable");
    }
    switch (open.place) {
        .parameter => |parameter| switch (parameter) {
            .name => |name| try text.print(gpa, ", in the type of the parameter {s}", .{name}),
            .position => |position| try text.print(gpa, ", in the type of parameter {d}", .{position}),
        },
        .result => try text.appendSlice(gpa, ", in the type the function returns"),
        .expression => try text.appendSlice(gpa, ", in the type of this expression"),
        .use => |use| try text.appendSlice(gpa, switch (use) {
            .call => ", which this call does not fix",
            .site => ", which this Code position does not fix",
        }),
    }
    return problems.putExtraString(text.items);
}

/// The reported reason for a walk that stopped.
fn stagedCodeReason(kind: code_reifier.Rejection.Kind) problem.StagedCode.Reason {
    return switch (kind) {
        .unsupported_expression => .unsupported_construct,
        .unsupported_type => .unsupported_type,
        .unresolved_type => .unresolved_type,
        .capture => .captures_a_binding,
        .effect => .performs_an_effect,
        .unresolved_reference => .definition_not_reachable,
        .argument_not_constant => .argument_not_constant,
        .bound_exceeded => .exceeds_a_bound,
        .input_not_bound => .input_not_bound,
        .value_not_bound => .value_not_bound,
        .value_not_computable => .value_not_computable,
        .function_parameter => .reads_a_function_parameter,
        .value_typed_late => .value_typed_late,
        .code_value => .reads_a_code_value,
        .bound_instance => .bound_instance,
        .instance_through_derived_evidence => .instance_through_derived_evidence,
        .instance_in_local_generic => .instance_in_local_generic,
        .bound_call_in_implicit_method => .bound_call_in_implicit_method,
        .requirement_constrained_variable => .requirement_constrained_variable,
        .type_id_not_nominal => .type_id_not_nominal,
        .ty_of_not_closed => .ty_of_not_closed,
        .checking_error => unreachable, // appendStagedCodeRefusal reports no checking error
    };
}

/// One module of a batch of description steps.
pub const BatchModule = struct {
    module: *CheckedModuleArtifact,
    problem_store: ?*problem.Store,
};

/// Run the description step of each module of `modules` whose code output
/// is `pending`, on `executor`'s lanes when there is more than one.
///
/// Each step reads only sealed data and code slots and writes only its own
/// module's `ConstStore`, `CodeOutput` and problem store, so the steps are
/// independent and each module's output does not depend on scheduling.
pub fn describeModules(
    gpa: Allocator,
    modules: []const BatchModule,
    reach: []const ImportedModuleView,
    executor: ?base.post_check_task_executor.Executor,
) Allocator.Error!void {
    var pending = std.ArrayList(BatchModule).empty;
    defer pending.deinit(gpa);
    for (modules) |entry| {
        if (entry.module.code_output.state == .pending) try pending.append(gpa, entry);
    }
    if (pending.items.len == 0) return;
    const lanes = executor orelse {
        for (pending.items) |entry| try describeModule(gpa, entry.module, entry.problem_store, reach);
        return;
    };
    if (pending.items.len == 1) {
        const entry = pending.items[0];
        return describeModule(gpa, entry.module, entry.problem_store, reach);
    }
    const Job = struct {
        gpa: Allocator,
        entry: BatchModule,
        reach: []const ImportedModuleView,
        failed: bool = false,

        fn run(context: *anyopaque, _: base.post_check_task_executor.Worker) ?*anyopaque {
            const job: *@This() = @ptrCast(@alignCast(context));
            describeModule(job.gpa, job.entry.module, job.entry.problem_store, job.reach) catch |err| switch (err) {
                error.OutOfMemory => job.failed = true,
            };
            return null;
        }
    };
    const jobs = try gpa.alloc(Job, pending.items.len);
    defer gpa.free(jobs);
    const tasks = try gpa.alloc(base.post_check_task_executor.Task, pending.items.len);
    defer gpa.free(tasks);
    const completions = try gpa.alloc(base.post_check_task_executor.Completion, pending.items.len);
    defer gpa.free(completions);
    for (pending.items, jobs, tasks, 0..) |entry, *job, *task, index| {
        job.* = .{ .gpa = gpa, .entry = entry, .reach = reach };
        task.* = .{ .id = index, .context = job, .run = Job.run };
    }
    try lanes.run(tasks, completions);
    for (jobs) |job| if (job.failed) return error.OutOfMemory;
}

/// Fill the `codeCuts` and `codeInventories` slots of every module of
/// `modules`, each with its own view of `reach`, which may hold the module
/// itself (design.md "Code Reification"). A module whose object this
/// evaluation builds publishes its inventories with its object interface
/// (`CheckedModuleArtifact.codeInventories`), so the evaluation fills them
/// here, also for a module whose code output came from the cache or a
/// reopened artifact. Lowering computes every other module's inventories
/// on demand, only for a module whose template it lowers.
pub fn fillCodeInventories(
    gpa: Allocator,
    modules: []const ImportedModuleView,
    reach: []const ImportedModuleView,
) Allocator.Error!void {
    for (modules) |view| {
        var lookups = try Lookups.init(gpa, view, reach);
        defer lookups.deinit(gpa);
        const inputs = checked.foreignModule(view, lookups.own.lookup());
        _ = try view.checked_bodies.codeCuts(inputs);
        _ = try check.CodeLookups.codeInventories(gpa, view, reach);
    }
}
