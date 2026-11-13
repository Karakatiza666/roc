//! The code descriptions of one module: the column of its evaluation output
//! that the description step of compile-time evaluation writes (design.md
//! "Code Reification").
//!
//! The description step of a module computes the compile-time value of each
//! `Code` site and identity call of the module, the instance table of each
//! closing use, the input slots of each bound call, and the bound entry of
//! each bound literal root. It writes them here and into the module's
//! `ConstStore`, and nothing else writes them. Checking and publication
//! write nothing here. Lowering reads this column where it reads the other
//! evaluation output.
//!
//! Every entry is named by an identity that is a function of the module's
//! sealed data: a CIR node, a Code edge, a compile-time root, or a site key.
//!
//! | Column | Key | Value |
//! |---|---|---|
//! | `sites` | site node, ascending | a description, or a refusal |
//! | `identities` | identity call node, ascending | a constant node, or a refusal |
//! | `edge_tables` | closing edge (`EdgeKey`), ascending | a table, or a refusal |
//! | `tables` | table id, by (template, instance) | its entries and bound entries |
//! | `bindings` | bound call node, ascending | input slots, or a refusal |
//! | `root_bounds` | compile-time root, ascending | a bound entry |
//! | `implicit_instances` | descriptor method and owner type (Q17) | a table, or a refusal |
//! | `provenance` | site key | where each node of a description came from |

const std = @import("std");
const can = @import("can");

const artifact_serialize = @import("artifact_serialize.zig");
const checked_artifact = @import("checked_artifact.zig");
const code_analyses = @import("code_analyses.zig");
const code_reifier = @import("code_reifier.zig");

const Allocator = std.mem.Allocator;
const SerializedSlice = artifact_serialize.SerializedSlice;
const CIR = can.CIR;
const ConstNodeId = checked_artifact.ConstNodeId;
const ComptimeRootId = checked_artifact.ComptimeRootId;
const CheckedModuleArtifactKey = checked_artifact.CheckedModuleArtifactKey;
const CheckedCodeRead = checked_artifact.CheckedCodeRead;
const CheckedCodeSlot = checked_artifact.CheckedCodeSlot;
const CheckedCodeSlotStep = checked_artifact.CheckedCodeSlotStep;
const CheckedTypeId = checked_artifact.CheckedTypeId;
const DescriptorMethod = code_analyses.DescriptorMethod;

fn invariant(comptime message: []const u8) noreturn {
    @import("base").invariant("code output invariant violated: " ++ message, .{});
}

/// A range of one of the output's pools.
pub const Span = extern struct { start: u32 = 0, len: u32 = 0 };

fn checkSpan(span: Span, len: usize) error{CorruptArtifact}!void {
    if (span.start > len or span.len > len - span.start) return error.CorruptArtifact;
}

/// A table of the output, by its position in `tables`.
pub const TableId = enum(u32) { _ };

/// Whether the description step of the module has run.
pub const State = enum(u8) {
    /// A fresh output: the description step has not run.
    pending,
    /// The description step has run, or the output came from the cache.
    complete,
};

/// Whether an entry holds a value or a refusal. The description step
/// reported each refusal, so lowering reads one as a crash that carries
/// `checked_error`.
pub const Outcome = enum(u32) { value, refused };

/// The description of a site that is not an instance site.
pub const Described = struct {
    /// The `Code` value in the module's `ConstStore`.
    value: ConstNodeId,
    /// The literal roots the walk met, in the order it met them.
    reads: []const CheckedCodeRead,
    /// The index of the site's first input slot among the slots of the call
    /// that binds it: the slots of the call's earlier sites, in site order.
    /// Zero for a site no call binds.
    first_slot: u32,
};

/// What lowering reads at a site.
pub const SiteOutcome = union(enum) {
    described: Described,
    refused,
};

/// What lowering reads at an identity call.
pub const Identity = union(enum) {
    value: ConstNodeId,
    refused,
};

/// What lowering reads at a closing edge.
pub const Use = union(enum) {
    table: TableId,
    refused,
};

/// One entry of a table, in the inventory order of the table's template.
pub const Entry = union(enum) {
    /// The description of an instance site or the constant of an identity
    /// call at the table's instance.
    node: struct { value: ConstNodeId, reads: []const CheckedCodeRead },
    /// An instance site that no description exists for at this instance.
    refused,
    /// A forward use: the table of the used template at this instance.
    forward: TableId,
};

/// The input slots of a bound call.
pub const Binding = union(enum) {
    slots: []const CheckedCodeSlot,
    refused,
};

/// A generic bound call of a table's template at the table's instance.
pub const BoundEntry = struct {
    /// The call's index in its template's generic bound calls (the
    /// template module's `codeInventories` slot).
    call: u32,
    /// The call's input slots, in slot order.
    slots: []const CheckedCodeSlot,
    /// The first slot of each of its sites, in site order.
    first_slots: []const u32,
};

/// One site of `CodeOutput.sites`.
pub const SiteRecord = extern struct {
    node: CIR.Expr.Idx,
    outcome: Outcome,
    /// The description, for a `value` outcome.
    value: ConstNodeId,
    /// A span of `reads`.
    reads: Span,
    first_slot: u32,
};

/// One identity call of `CodeOutput.identities`.
pub const IdentityRecord = extern struct {
    node: CIR.Expr.Idx,
    outcome: Outcome,
    value: ConstNodeId,
};

/// An edge where a template is selected (design.md "Code Instance
/// Tables"): `checked.LiteralEdge` with no `literal`. A table and a literal
/// root name an edge in the same way.
pub const CodeEdge = checked_artifact.LiteralEdge;

/// The kind of a `CodeEdge`, as `EdgeKey` stores it.
pub const EdgeKind = enum(u32) { node, use, requirement, derivation_call };

/// A `CodeEdge` as a cached record stores it: a use by its expression, an
/// evidence node by its id, a platform requirement by its requires index, a
/// contract call by its contract and then its node.
pub const EdgeKey = extern struct {
    kind: EdgeKind,
    first: u32,
    second: u32 = 0,

    pub fn of(edge: CodeEdge) EdgeKey {
        return switch (edge) {
            .node => |node| .{ .kind = .node, .first = @backingInt(node) },
            .use => |use_expr| .{ .kind = .use, .first = @backingInt(use_expr) },
            .requirement => |requires_idx| .{ .kind = .requirement, .first = requires_idx },
            .derivation_call => |call| .{ .kind = .derivation_call, .first = @backingInt(call.derivation), .second = @backingInt(call.node) },
            .literal => invariant("a literal is no edge a table is keyed by"),
        };
    }

    pub fn order(a: EdgeKey, b: EdgeKey) std.math.Order {
        const kinds = std.math.order(@backingInt(a.kind), @backingInt(b.kind));
        if (kinds != .eq) return kinds;
        const firsts = std.math.order(a.first, b.first);
        if (firsts != .eq) return firsts;
        return std.math.order(a.second, b.second);
    }

    pub fn lessThan(_: void, a: EdgeKey, b: EdgeKey) bool {
        return order(a, b) == .lt;
    }
};

/// One closing edge of `CodeOutput.edge_tables`.
pub const EdgeTableRecord = extern struct {
    edge: EdgeKey,
    outcome: Outcome,
    table: TableId,
};

/// The `value` of a refused site or identity record, which no reader
/// reads. A fixed value keeps the cached bytes and the object key
/// deterministic.
pub const refused_value: ConstNodeId = @fromBackingInt(std.math.maxInt(u32));

/// The `table` of a refused use record, which no reader reads.
pub const refused_table: TableId = @fromBackingInt(std.math.maxInt(u32));

/// The `TableTemplate.template` of a refused table, which serves no
/// template and which no use passes.
pub const no_template: u32 = std.math.maxInt(u32);

/// The template a table serves: the key of its module and its id there.
pub const TableTemplate = extern struct {
    module: CheckedModuleArtifactKey,
    template: u32,
};

/// One table of `CodeOutput.tables`.
pub const TableRecord = extern struct {
    template: TableTemplate,
    /// A span of `table_entries`.
    entries: Span,
    /// A span of `bound_entries`.
    bound_entries: Span,
};

/// What an entry of a table is: a description, a refusal, or a nested table.
pub const EntryKind = enum(u32) { node, refused, forward };

/// One entry of `CodeOutput.table_entries`.
pub const EntryRecord = extern struct {
    kind: EntryKind,
    /// A `ConstNodeId` for `node`, a `TableId` for `forward`.
    value: u32,
    /// A span of `reads`, for `node`.
    reads: Span,
};

/// One bound entry of `CodeOutput.bound_entries`.
pub const BoundEntryRecord = extern struct {
    call: u32,
    /// A span of `slots`.
    slots: Span,
    /// A span of `first_slots`.
    first_slots: Span,
};

/// One bound call of `CodeOutput.bindings`.
pub const BindingRecord = extern struct {
    call: CIR.Expr.Idx,
    outcome: Outcome,
    /// A span of `slots`.
    slots: Span,
};

/// A table of a descriptor method at an owner type (Q17, design.md "Code
/// Instance Tables"): what lowering passes where the compiler calls the
/// method for a value of that type.
pub const ImplicitInstanceRecord = extern struct {
    method: DescriptorMethod,
    outcome: Outcome,
    /// The owner type, an index of `owner_terms`.
    owner: u32,
    /// The table, for a `value` outcome.
    table: TableId,
};

/// `type`: a type with its bindings. `record_rest` and `tag_rest`: the
/// rest of a row that a row variable stands for, as members.
pub const OwnerTermKind = code_reifier.InstanceTables.OwnerTermKind;

/// An owner type: a type of the store of `owner_modules[module]`, with the
/// term each variable of it a description fixed stands for (a span of
/// `owner_bindings`). A variable no binding names is free, and lowering
/// seals it as it seals any free variable.
///
/// A row term (`record_rest`, `tag_rest`) is the closed row of its
/// `members` (a span of `owner_members`). It is exactly the rest of the row
/// its variable ends: no nearer link of that row names a member's label.
/// `ty` is the whole row the use matched, and `bindings` is empty.
pub const OwnerTermRecord = extern struct {
    module: u32,
    kind: OwnerTermKind = .type,
    ty: CheckedTypeId,
    bindings: Span,
    members: Span = .{},
};

/// A field or a tag of a row term: its label in the store of
/// `owner_modules[module]`, the field's kind, and a span of
/// `owner_member_terms` (one term for a field, one per payload for a tag).
pub const OwnerMemberRecord = extern struct {
    module: u32,
    label: u32,
    kind: checked_artifact.CheckedFieldKind = .{},
    terms: Span,
};

/// One variable of an owner term and the term it stands for.
pub const OwnerBindingRecord = extern struct {
    variable: CheckedTypeId,
    /// An index of `owner_terms`.
    term: u32,
};

/// The bound entry a bound literal root reads.
pub const RootBoundRecord = extern struct {
    root: ComptimeRootId,
    /// An index of `bound_entries`.
    entry: u32,
};

/// The code descriptions of one module.
pub const CodeOutput = struct {
    state: State = .pending,
    /// Sorted by node.
    sites: []const SiteRecord = &.{},
    /// Sorted by node.
    identities: []const IdentityRecord = &.{},
    /// Sorted by edge (`EdgeKey.order`). A `for` loop's closing use is
    /// keyed by the loop's body.
    edge_tables: []const EdgeTableRecord = &.{},
    tables: []const TableRecord = &.{},
    table_entries: []const EntryRecord = &.{},
    bound_entries: []const BoundEntryRecord = &.{},
    first_slots: []const u32 = &.{},
    /// Sorted by call.
    bindings: []const BindingRecord = &.{},
    /// Sorted by root.
    root_bounds: []const RootBoundRecord = &.{},
    slots: []const CheckedCodeSlot = &.{},
    slot_steps: []const CheckedCodeSlotStep = &.{},
    /// Words of `checked_artifact.CodeValueShape`.
    slot_shapes: []const u32 = &.{},
    reads: []const CheckedCodeRead = &.{},
    /// In the order the description step built the tables.
    implicit_instances: []const ImplicitInstanceRecord = &.{},
    owner_terms: []const OwnerTermRecord = &.{},
    owner_bindings: []const OwnerBindingRecord = &.{},
    owner_members: []const OwnerMemberRecord = &.{},
    /// Indices of `owner_terms`.
    owner_member_terms: []const u32 = &.{},
    owner_modules: []const CheckedModuleArtifactKey = &.{},
    provenance: CodeProvenanceTable = .{},

    /// Process-local: a cached output is complete (`Serialized.deserialize`).
    pub const serde_transient_fields = [_][]const u8{"state"};

    pub const Serialized = extern struct {
        sites: SerializedSlice(SiteRecord) = .{},
        identities: SerializedSlice(IdentityRecord) = .{},
        edge_tables: SerializedSlice(EdgeTableRecord) = .{},
        tables: SerializedSlice(TableRecord) = .{},
        table_entries: SerializedSlice(EntryRecord) = .{},
        bound_entries: SerializedSlice(BoundEntryRecord) = .{},
        first_slots: SerializedSlice(u32) = .{},
        bindings: SerializedSlice(BindingRecord) = .{},
        root_bounds: SerializedSlice(RootBoundRecord) = .{},
        slots: SerializedSlice(CheckedCodeSlot) = .{},
        slot_steps: SerializedSlice(CheckedCodeSlotStep) = .{},
        slot_shapes: SerializedSlice(u32) = .{},
        reads: SerializedSlice(CheckedCodeRead) = .{},
        implicit_instances: SerializedSlice(ImplicitInstanceRecord) = .{},
        owner_terms: SerializedSlice(OwnerTermRecord) = .{},
        owner_bindings: SerializedSlice(OwnerBindingRecord) = .{},
        owner_members: SerializedSlice(OwnerMemberRecord) = .{},
        owner_member_terms: SerializedSlice(u32) = .{},
        owner_modules: SerializedSlice(CheckedModuleArtifactKey) = .{},
        provenance: CodeProvenanceTable.Serialized = .{},

        const Serde = artifact_serialize.SliceStoreSerde(CodeOutput, @This());

        /// Only a complete output is written: a module is cached after its
        /// evaluation, and the description step runs first in it.
        pub fn serialize(self: *@This(), output: *const CodeOutput, gpa: Allocator, writer: *@import("collections").CompactWriter) Allocator.Error!void {
            output.assertComplete();
            return Serde.serialize(self, output, gpa, writer);
        }

        /// A cached output is complete: the description step ran in the
        /// evaluation that wrote it.
        pub fn deserialize(self: *const @This(), base_addr: usize) CodeOutput {
            var output = Serde.deserialize(self, base_addr);
            output.state = .complete;
            return output;
        }
    };

    /// Whether every span and index of a cached output lies inside its
    /// pools, and every keyed column is sorted by its key.
    pub fn validate(self: *const CodeOutput) error{CorruptArtifact}!void {
        var previous: ?u32 = null;
        for (self.sites) |record| {
            try ascending(&previous, @backingInt(record.node));
            try checkSpan(record.reads, self.reads.len);
        }
        previous = null;
        for (self.identities) |record| try ascending(&previous, @backingInt(record.node));
        var previous_edge: ?EdgeKey = null;
        for (self.edge_tables) |record| {
            if (previous_edge) |last| if (EdgeKey.order(last, record.edge) != .lt) return error.CorruptArtifact;
            previous_edge = record.edge;
            if (record.outcome == .value) try checkTable(record.table, self.tables.len);
        }
        for (self.tables) |record| {
            try checkSpan(record.entries, self.table_entries.len);
            try checkSpan(record.bound_entries, self.bound_entries.len);
        }
        for (self.table_entries) |record| switch (record.kind) {
            .node => try checkSpan(record.reads, self.reads.len),
            .refused => {},
            .forward => try checkTable(@fromBackingInt(record.value), self.tables.len),
        };
        for (self.bound_entries) |record| {
            try checkSpan(record.slots, self.slots.len);
            try checkSpan(record.first_slots, self.first_slots.len);
        }
        previous = null;
        for (self.bindings) |record| {
            try ascending(&previous, @backingInt(record.call));
            try checkSpan(record.slots, self.slots.len);
        }
        previous = null;
        for (self.root_bounds) |record| {
            try ascending(&previous, @backingInt(record.root));
            if (record.entry >= self.bound_entries.len) return error.CorruptArtifact;
        }
        for (self.slots) |slot| {
            try checkSpan(.{ .start = slot.steps_start, .len = slot.steps_len }, self.slot_steps.len);
            try checkSpan(.{ .start = slot.shape_start, .len = slot.shape_len }, self.slot_shapes.len);
        }
        for (self.implicit_instances) |record| {
            if (record.owner >= self.owner_terms.len) return error.CorruptArtifact;
            if (record.outcome == .value) try checkTable(record.table, self.tables.len);
        }
        for (self.owner_terms) |term| {
            if (term.module >= self.owner_modules.len) return error.CorruptArtifact;
            try checkSpan(term.bindings, self.owner_bindings.len);
            try checkSpan(term.members, self.owner_members.len);
        }
        for (self.owner_bindings) |owner_binding| if (owner_binding.term >= self.owner_terms.len) return error.CorruptArtifact;
        for (self.owner_members) |member| {
            if (member.module >= self.owner_modules.len) return error.CorruptArtifact;
            try checkSpan(member.terms, self.owner_member_terms.len);
        }
        for (self.owner_member_terms) |term| if (term >= self.owner_terms.len) return error.CorruptArtifact;
        try self.provenance.validate();
    }

    fn ascending(previous: *?u32, key: u32) error{CorruptArtifact}!void {
        if (previous.*) |last| if (last >= key) return error.CorruptArtifact;
        previous.* = key;
    }

    fn checkTable(table: TableId, len: usize) error{CorruptArtifact}!void {
        if (@backingInt(table) >= len) return error.CorruptArtifact;
    }

    fn assertComplete(self: *const CodeOutput) void {
        std.debug.assert(self.state == .complete);
    }

    fn readSpan(self: *const CodeOutput, span: Span) []const CheckedCodeRead {
        return self.reads[span.start..][0..span.len];
    }

    fn slotSpan(self: *const CodeOutput, span: Span) []const CheckedCodeSlot {
        return self.slots[span.start..][0..span.len];
    }

    /// The description or refusal of the site at `node`. The site is no
    /// instance site: an instance site is described in the tables of its
    /// closing uses.
    pub fn site(self: *const CodeOutput, node: CIR.Expr.Idx) SiteOutcome {
        self.assertComplete();
        const record = findByNode(SiteRecord, self.sites, node) orelse invariant("a code site had no description");
        return switch (record.outcome) {
            .value => .{ .described = .{
                .value = record.value,
                .reads = self.readSpan(record.reads),
                .first_slot = record.first_slot,
            } },
            .refused => .refused,
        };
    }

    /// The constant or refusal of the identity call at `node`. The call is
    /// no instance entry.
    pub fn identity(self: *const CodeOutput, node: CIR.Expr.Idx) Identity {
        self.assertComplete();
        const record = findByNode(IdentityRecord, self.identities, node) orelse invariant("a code identity call had no constant");
        return switch (record.outcome) {
            .value => .{ .value = record.value },
            .refused => .refused,
        };
    }

    /// The table or refusal of the closing edge `edge`, or null for an edge
    /// that is no closing edge: a use or evidence node that selects no
    /// template with an inventory, or a forward edge.
    pub fn edgeTable(self: *const CodeOutput, edge: CodeEdge) ?Use {
        self.assertComplete();
        const key = EdgeKey.of(edge);
        const index = std.sort.binarySearch(EdgeTableRecord, self.edge_tables, key, struct {
            fn order(target: EdgeKey, item: EdgeTableRecord) std.math.Order {
                return EdgeKey.order(target, item.edge);
            }
        }.order) orelse return null;
        const record = self.edge_tables[index];
        return useOf(record.outcome, record.table);
    }

    /// The template `table` serves.
    pub fn tableTemplate(self: *const CodeOutput, table: TableId) TableTemplate {
        return self.tables[@backingInt(table)].template;
    }

    /// Entry `index` of `table`, in the inventory order of its template.
    pub fn entry(self: *const CodeOutput, table: TableId, index: u32) Entry {
        self.assertComplete();
        const span = self.tables[@backingInt(table)].entries;
        if (index >= span.len) invariant("a table entry was out of range");
        const record = self.table_entries[span.start + index];
        return switch (record.kind) {
            .node => .{ .node = .{ .value = @fromBackingInt(record.value), .reads = self.readSpan(record.reads) } },
            .refused => .refused,
            .forward => .{ .forward = @fromBackingInt(record.value) },
        };
    }

    /// The bound entries of `table`, one per generic bound call of its
    /// template, in call order.
    pub fn tableBoundEntries(self: *const CodeOutput, table: TableId) []const BoundEntryRecord {
        const span = self.tables[@backingInt(table)].bound_entries;
        return self.bound_entries[span.start..][0..span.len];
    }

    /// One bound entry with its slots.
    pub fn boundEntry(self: *const CodeOutput, record: BoundEntryRecord) BoundEntry {
        return .{
            .call = record.call,
            .slots = self.slotSpan(record.slots),
            .first_slots = self.first_slots[record.first_slots.start..][0..record.first_slots.len],
        };
    }

    /// The input slots or refusal of the bound call at `call`, or null for
    /// a node that is no bound call of a site this module describes.
    pub fn binding(self: *const CodeOutput, call: CIR.Expr.Idx) ?Binding {
        self.assertComplete();
        const record = binarySearch(BindingRecord, self.bindings, @backingInt(call), bindingKey) orelse return null;
        return switch (record.outcome) {
            .value => .{ .slots = self.slotSpan(record.slots) },
            .refused => .refused,
        };
    }

    /// The bound entry the bound literal root `root` reads, or null for a
    /// root with none.
    pub fn rootBound(self: *const CodeOutput, root: ComptimeRootId) ?BoundEntry {
        self.assertComplete();
        const record = binarySearch(RootBoundRecord, self.root_bounds, @backingInt(root), rootKey) orelse return null;
        return self.boundEntry(self.bound_entries[record.entry]);
    }

    /// The bindings of an owner term (Q17).
    pub fn ownerBindings(self: *const CodeOutput, term: OwnerTermRecord) []const OwnerBindingRecord {
        return self.owner_bindings[term.bindings.start..][0..term.bindings.len];
    }

    /// The members of a row term (Q17).
    pub fn ownerMembers(self: *const CodeOutput, term: OwnerTermRecord) []const OwnerMemberRecord {
        return self.owner_members[term.members.start..][0..term.members.len];
    }

    /// The terms of a row term's member: a field's type, or a tag's
    /// payloads.
    pub fn ownerMemberTerms(self: *const CodeOutput, member: OwnerMemberRecord) []const u32 {
        return self.owner_member_terms[member.terms.start..][0..member.terms.len];
    }

    /// The table `record` names, or null for a refused instance.
    pub fn implicitTable(record: ImplicitInstanceRecord) ?TableId {
        return switch (record.outcome) {
            .value => record.table,
            .refused => null,
        };
    }

    /// The projections of one input slot.
    pub fn slotSteps(self: *const CodeOutput, slot: CheckedCodeSlot) []const CheckedCodeSlotStep {
        return self.slot_steps[slot.steps_start..][0..slot.steps_len];
    }

    /// The shape words of one input slot.
    pub fn slotShape(self: *const CodeOutput, slot: CheckedCodeSlot) []const u32 {
        return self.slot_shapes[slot.shape_start..][0..slot.shape_len];
    }

    pub fn deinit(self: *CodeOutput, allocator: Allocator) void {
        allocator.free(self.sites);
        allocator.free(self.identities);
        allocator.free(self.edge_tables);
        allocator.free(self.tables);
        allocator.free(self.table_entries);
        allocator.free(self.bound_entries);
        allocator.free(self.first_slots);
        allocator.free(self.bindings);
        allocator.free(self.root_bounds);
        allocator.free(self.slots);
        allocator.free(self.slot_steps);
        allocator.free(self.slot_shapes);
        allocator.free(self.reads);
        allocator.free(self.implicit_instances);
        allocator.free(self.owner_terms);
        allocator.free(self.owner_bindings);
        allocator.free(self.owner_members);
        allocator.free(self.owner_member_terms);
        allocator.free(self.owner_modules);
        self.provenance.deinit(allocator);
        self.* = .{};
    }

    fn useOf(outcome: Outcome, table: TableId) Use {
        return switch (outcome) {
            .value => .{ .table = table },
            .refused => .refused,
        };
    }

    fn findByNode(comptime Record: type, items: []const Record, node: CIR.Expr.Idx) ?Record {
        return binarySearch(Record, items, @backingInt(node), nodeKey(Record));
    }

    fn nodeKey(comptime Record: type) fn (Record) u32 {
        return struct {
            fn key(record: Record) u32 {
                return @backingInt(record.node);
            }
        }.key;
    }

    fn bindingKey(record: BindingRecord) u32 {
        return @backingInt(record.call);
    }

    fn rootKey(record: RootBoundRecord) u32 {
        return @backingInt(record.root);
    }

    fn binarySearch(comptime Record: type, items: []const Record, key: u32, comptime keyOf: fn (Record) u32) ?Record {
        const index = std.sort.binarySearch(Record, items, key, struct {
            fn order(target: u32, item: Record) std.math.Order {
                return std.math.order(target, keyOf(item));
            }
        }.order) orelse return null;
        return items[index];
    }
};

/// The provenance of the module's `Code` sites (normal-form 3.10, plan I9):
/// per site key, where each node of the site's graph came from. Nothing a
/// translator reads holds it; a refusal reads it to report a node at its
/// source regions.
///
/// | Slice | One entry per | Holds |
/// |---|---|---|
/// | `sites` | site | its key, and its spans of `sources` and `rows` |
/// | `sources` | source of a site | the module, by index into `modules`, and the region |
/// | `rows` | row of a site's graph, in graph order | its span of `nodes` |
/// | `nodes` | node of a row, in the row's node order | its span of `chains` |
/// | `chains` | origin of a node | its span of `links` |
/// | `links` | step of an origin | a source, by index into the site's sources: the node's own, then each call that reached it |
/// | `node_intrinsics` | node of a row, as `nodes` | its span of `intrinsics` |
/// | `intrinsics` | intrinsic a node's `Prim` names, its own or in its evidence | its name, `owner.method`, as a span of `text` |
pub const CodeProvenanceTable = struct {
    pub const Site = extern struct { key: u64, sources: Span, rows: Span };
    pub const Source = extern struct { module: u32, region_start: u32, region_end: u32 };

    sites: []const Site = &.{},
    sources: []const Source = &.{},
    modules: []const CheckedModuleArtifactKey = &.{},
    rows: []const Span = &.{},
    nodes: []const Span = &.{},
    chains: []const Span = &.{},
    links: []const u32 = &.{},
    node_intrinsics: []const Span = &.{},
    intrinsics: []const Span = &.{},
    text: []const u8 = &.{},

    pub const Serialized = extern struct {
        sites: SerializedSlice(Site) = .{},
        sources: SerializedSlice(Source) = .{},
        modules: SerializedSlice(CheckedModuleArtifactKey) = .{},
        rows: SerializedSlice(Span) = .{},
        nodes: SerializedSlice(Span) = .{},
        chains: SerializedSlice(Span) = .{},
        links: SerializedSlice(u32) = .{},
        node_intrinsics: SerializedSlice(Span) = .{},
        intrinsics: SerializedSlice(Span) = .{},
        text: SerializedSlice(u8) = .{},
        const Serde = artifact_serialize.SliceStoreSerde(CodeProvenanceTable, @This());
        pub const serialize = Serde.serialize;
        pub const deserialize = Serde.deserialize;
    };

    /// Whether every span of a cached table lies inside its pools.
    pub fn validate(self: CodeProvenanceTable) error{CorruptArtifact}!void {
        for (self.sites) |s| {
            try checkSpan(s.sources, self.sources.len);
            try checkSpan(s.rows, self.rows.len);
        }
        for (self.sources) |src| if (src.module >= self.modules.len or src.region_start > src.region_end) return error.CorruptArtifact;
        for (self.rows) |r| try checkSpan(r, self.nodes.len);
        for (self.nodes) |n| try checkSpan(n, self.chains.len);
        for (self.chains) |c| try checkSpan(c, self.links.len);
        if (self.node_intrinsics.len != self.nodes.len) return error.CorruptArtifact;
        for (self.node_intrinsics) |n| try checkSpan(n, self.intrinsics.len);
        for (self.intrinsics) |i| try checkSpan(i, self.text.len);
    }

    /// The table of the sites `published` describes, in their order.
    pub fn init(allocator: Allocator, published: []const code_reifier.SiteProvenance) Allocator.Error!CodeProvenanceTable {
        var sites: std.ArrayList(Site) = .empty;
        defer sites.deinit(allocator);
        var sources: std.ArrayList(Source) = .empty;
        defer sources.deinit(allocator);
        var modules: std.ArrayList(CheckedModuleArtifactKey) = .empty;
        defer modules.deinit(allocator);
        var rows: std.ArrayList(Span) = .empty;
        defer rows.deinit(allocator);
        var nodes: std.ArrayList(Span) = .empty;
        defer nodes.deinit(allocator);
        var chains: std.ArrayList(Span) = .empty;
        defer chains.deinit(allocator);
        var links: std.ArrayList(u32) = .empty;
        defer links.deinit(allocator);
        var node_intrinsics: std.ArrayList(Span) = .empty;
        defer node_intrinsics.deinit(allocator);
        var intrinsics: std.ArrayList(Span) = .empty;
        defer intrinsics.deinit(allocator);
        var text: std.ArrayList(u8) = .empty;
        defer text.deinit(allocator);
        for (published) |entry| {
            const sources_start: u32 = @intCast(sources.items.len);
            for (entry.sources) |src| {
                const module: u32 = for (modules.items, 0..) |m, i| {
                    if (std.meta.eql(m, src.module)) break @intCast(i);
                } else blk: {
                    try modules.append(allocator, src.module);
                    break :blk @intCast(modules.items.len - 1);
                };
                try sources.append(allocator, .{ .module = module, .region_start = src.region.start.offset, .region_end = src.region.end.offset });
            }
            const rows_start: u32 = @intCast(rows.items.len);
            const emitted = &entry.origins;
            for (emitted.rows.items) |row| {
                const nodes_start: u32 = @intCast(nodes.items.len);
                for (emitted.nodes.items[row.start..][0..row.len]) |node| {
                    const chains_start: u32 = @intCast(chains.items.len);
                    for (emitted.chains.items[node.start..][0..node.len]) |chain| {
                        const links_start: u32 = @intCast(links.items.len);
                        for (emitted.links.items[chain.start..][0..chain.len]) |link| try links.append(allocator, link.index());
                        try chains.append(allocator, .{ .start = links_start, .len = chain.len });
                    }
                    try nodes.append(allocator, .{ .start = chains_start, .len = node.len });
                }
                for (emitted.node_intrinsics.items[row.start..][0..row.len]) |named| {
                    const intrinsics_start: u32 = @intCast(intrinsics.items.len);
                    for (emitted.intrinsics.items[named.start..][0..named.len]) |span| {
                        const text_start: u32 = @intCast(text.items.len);
                        try text.appendSlice(allocator, emitted.intrinsicText(span));
                        try intrinsics.append(allocator, .{ .start = text_start, .len = span.len });
                    }
                    try node_intrinsics.append(allocator, .{ .start = intrinsics_start, .len = named.len });
                }
                try rows.append(allocator, .{ .start = nodes_start, .len = row.len });
            }
            try sites.append(allocator, .{
                .key = entry.key,
                .sources = .{ .start = sources_start, .len = @intCast(entry.sources.len) },
                .rows = .{ .start = rows_start, .len = @intCast(emitted.rows.items.len) },
            });
        }
        var table: CodeProvenanceTable = .{};
        errdefer table.deinit(allocator);
        table.sites = try sites.toOwnedSlice(allocator);
        table.sources = try sources.toOwnedSlice(allocator);
        table.modules = try modules.toOwnedSlice(allocator);
        table.rows = try rows.toOwnedSlice(allocator);
        table.nodes = try nodes.toOwnedSlice(allocator);
        table.chains = try chains.toOwnedSlice(allocator);
        table.links = try links.toOwnedSlice(allocator);
        table.node_intrinsics = try node_intrinsics.toOwnedSlice(allocator);
        table.intrinsics = try intrinsics.toOwnedSlice(allocator);
        table.text = try text.toOwnedSlice(allocator);
        return table;
    }

    /// The site whose `Code` value carries `key`.
    pub fn site(self: CodeProvenanceTable, key: u64) ?Site {
        for (self.sites) |s| if (s.key == key) return s;
        return null;
    }

    /// The origins of node `node` of row `row` of `s`'s graph, each a span of
    /// `links`, or null where the graph has no such node.
    pub fn origins(self: CodeProvenanceTable, s: Site, row: u32, node: u32) ?[]const Span {
        if (row >= s.rows.len) return null;
        const r = self.rows[s.rows.start + row];
        if (node >= r.len) return null;
        const n = self.nodes[r.start + node];
        return self.chains[n.start..][0..n.len];
    }

    /// One step of an origin: the source it names in `s`.
    pub fn source(self: CodeProvenanceTable, s: Site, link: u32) Source {
        return self.sources[s.sources.start + link];
    }

    /// The intrinsics node `node` of row `row` of `s`'s graph names, each
    /// a span of `text`, or null where the graph has no such node.
    pub fn intrinsicsOf(self: CodeProvenanceTable, s: Site, row: u32, node: u32) ?[]const Span {
        if (row >= s.rows.len) return null;
        const r = self.rows[s.rows.start + row];
        if (node >= r.len) return null;
        const named = self.node_intrinsics[r.start + node];
        return self.intrinsics[named.start..][0..named.len];
    }

    /// The name of one intrinsic `intrinsicsOf` gives.
    pub fn intrinsicText(self: CodeProvenanceTable, span: Span) []const u8 {
        return self.text[span.start..][0..span.len];
    }

    pub fn deinit(self: *CodeProvenanceTable, allocator: Allocator) void {
        allocator.free(self.sites);
        allocator.free(self.sources);
        allocator.free(self.modules);
        allocator.free(self.rows);
        allocator.free(self.nodes);
        allocator.free(self.chains);
        allocator.free(self.links);
        allocator.free(self.node_intrinsics);
        allocator.free(self.intrinsics);
        allocator.free(self.text);
        self.* = .{};
    }
};
