//! The normal-form IR: rows, regions with terminators, and nodes.
//!
//! One IR with two invariant levels, raw and normal (plan 1.3). Nodes live in
//! struct-of-arrays columns with `u32` ids; a node's arguments, output types,
//! owned regions and immediates are spans into shared pools.

const std = @import("std");
const collections = @import("collections");
const prims = @import("prims.zig");
const provenance = @import("provenance.zig");

const Allocator = std.mem.Allocator;

/// One value per row, kept in the order each row was first added: a dense
/// column from a row to its position, beside the rows and their values in
/// that order. A pass that writes rows out in the order it reached them
/// reads both lists directly.
pub fn RowTable(comptime V: type) type {
    return struct {
        const Self = @This();

        position: collections.DenseMapUnmanaged(RowId, u32) = .empty,
        rows: std.ArrayList(RowId) = .empty,
        entries: std.ArrayList(V) = .empty,

        /// A table holding no row.
        pub const empty: Self = .{};

        /// What `getOrPut` found or added.
        pub const GetOrPutResult = struct {
            value_ptr: *V,
            found_existing: bool,
        };

        pub fn deinit(self: *Self, gpa: Allocator) void {
            self.position.deinit(gpa);
            self.rows.deinit(gpa);
            self.entries.deinit(gpa);
        }

        /// The rows, in the order they were added.
        pub fn keys(self: *const Self) []const RowId {
            return self.rows.items;
        }

        /// The values, parallel to `keys`.
        pub fn values(self: *const Self) []V {
            return self.entries.items;
        }

        /// How many rows the table holds.
        pub fn count(self: *const Self) usize {
            return self.rows.items.len;
        }

        /// Whether the table holds `row`.
        pub fn contains(self: *const Self, row: RowId) bool {
            return self.position.contains(row);
        }

        /// Where `row` stands in `keys`, or null when the table does not hold it.
        pub fn getIndex(self: *const Self, row: RowId) ?usize {
            const at = self.position.get(row) orelse return null;
            return at;
        }

        /// The value of `row`, or null when the table does not hold it.
        pub fn get(self: *const Self, row: RowId) ?V {
            const at = self.position.get(row) orelse return null;
            return self.entries.items[at];
        }

        /// The value of `row`, added undefined at the end when the table
        /// does not hold it yet.
        pub fn getOrPut(self: *Self, gpa: Allocator, row: RowId) Allocator.Error!GetOrPutResult {
            if (self.position.get(row)) |at| return .{ .value_ptr = &self.entries.items[at], .found_existing = true };
            try self.rows.ensureUnusedCapacity(gpa, 1);
            try self.entries.ensureUnusedCapacity(gpa, 1);
            try self.position.put(gpa, row, @intCast(self.rows.items.len));
            self.rows.appendAssumeCapacity(row);
            self.entries.appendAssumeCapacity(undefined);
            return .{ .value_ptr = &self.entries.items[self.entries.items.len - 1], .found_existing = false };
        }

        /// Set the value of `row`, adding it at the end when the table does
        /// not hold it yet.
        pub fn put(self: *Self, gpa: Allocator, row: RowId, value: V) Allocator.Error!void {
            (try self.getOrPut(gpa, row)).value_ptr.* = value;
        }
    };
}

/// A row: one function body of the normal form.
pub const RowId = enum(u32) {
    _,

    /// The row with this index.
    pub fn of(i: u32) RowId {
        return @fromBackingInt(@intCast(i));
    }

    /// This row's index.
    pub fn index(self: RowId) u32 {
        return @backingInt(self);
    }
};

/// A region: a row body, a switch arm or join, an `And`/`Or` operand, or a loop body.
pub const RegionId = enum(u32) {
    _,

    /// No region: the owner of a row body, or the parent of a row body.
    pub const none: RegionId = @fromBackingInt(@intCast(std.math.maxInt(u32)));

    /// The region with this index.
    pub fn of(i: u32) RegionId {
        return @fromBackingInt(@intCast(i));
    }

    /// This region's index.
    pub fn index(self: RegionId) u32 {
        return @backingInt(self);
    }
};

/// A node: one operation with its arguments, output types and owned regions.
pub const NodeId = enum(u32) {
    _,

    /// No node: the owner of a row body.
    pub const none: NodeId = @fromBackingInt(@intCast(std.math.maxInt(u32)));

    /// The node with this index.
    pub fn of(i: u32) NodeId {
        return @fromBackingInt(@intCast(i));
    }

    /// This node's index.
    pub fn index(self: NodeId) u32 {
        return @backingInt(self);
    }
};

/// An interned type (`types.zig`).
pub const TyId = enum(u32) {
    _,

    /// The type with this index.
    pub fn of(i: u32) TyId {
        return @fromBackingInt(@intCast(i));
    }

    /// This type's index.
    pub fn index(self: TyId) u32 {
        return @backingInt(self);
    }
};

/// A builtin of the builtin table (`prims.zig`).
pub const PrimId = enum(u32) {
    _,

    /// The builtin with this index.
    pub fn of(i: u32) PrimId {
        return @fromBackingInt(@intCast(i));
    }

    /// This builtin's index.
    pub fn index(self: PrimId) u32 {
        return @backingInt(self);
    }
};

/// An interned literal value of one type.
pub const LitId = enum(u32) {
    _,

    /// The literal with this index.
    pub fn of(i: u32) LitId {
        return @fromBackingInt(@intCast(i));
    }

    /// This literal's index.
    pub fn index(self: LitId) u32 {
        return @backingInt(self);
    }
};

/// A contiguous range of a pool.
pub const Span = struct {
    start: u32,
    len: u32,

    /// The empty span.
    pub const empty: Span = .{ .start = 0, .len = 0 };
};

/// A value reference: a row parameter, a region parameter, one output of a
/// node, or an input slot of the root (N18).
///
/// Region parameters are loop slots, a `ForRange` index, a `ForList` element,
/// and join parameters. A reference names what it reads positionally; no
/// name exists anywhere in the IR (N2).
pub const Ref = packed struct(u64) {
    kind: Kind,
    output: u30,
    target: u32,

    /// What a reference reads.
    pub const Kind = enum(u2) { node, row_param, region_param, input };

    /// Output `output` of node `n`.
    pub fn node(n: NodeId, output: u30) Ref {
        return .{ .kind = .node, .output = output, .target = n.index() };
    }

    /// The single output of node `n`.
    pub fn of(n: NodeId) Ref {
        return node(n, 0);
    }

    /// Parameter `k` of the row this reference appears in.
    pub fn rowParam(k: u30) Ref {
        return .{ .kind = .row_param, .output = k, .target = 0 };
    }

    /// Parameter `k` of region `r`.
    pub fn regionParam(r: RegionId, k: u30) Ref {
        return .{ .kind = .region_param, .output = k, .target = r.index() };
    }

    /// Input slot `s` of the store's slot table (N18).
    pub fn input(s: SlotId) Ref {
        return .{ .kind = .input, .output = 0, .target = s.index() };
    }

    /// The node this reference reads, or `none` for a parameter or a slot.
    pub fn nodeId(self: Ref) NodeId {
        return switch (self.kind) {
            .node => NodeId.of(self.target),
            .row_param, .region_param, .input => NodeId.none,
        };
    }

    /// The region whose parameter this reference reads.
    pub fn regionId(self: Ref) RegionId {
        return switch (self.kind) {
            .region_param => RegionId.of(self.target),
            .node, .row_param, .input => RegionId.none,
        };
    }

    /// The slot this reference reads.
    pub fn slotId(self: Ref) SlotId {
        std.debug.assert(self.kind == .input);
        return SlotId.of(self.target);
    }
};

/// An input slot of the root (N18): a value the program supplies at run time.
pub const SlotId = enum(u32) {
    _,

    /// The slot with this index.
    pub fn of(i: u32) SlotId {
        return @fromBackingInt(@intCast(i));
    }

    /// This slot's index.
    pub fn index(self: SlotId) u32 {
        return @backingInt(self);
    }
};

/// One input slot: a run-time name the walk cannot replay, or a projection of
/// another slot (N18b). `leaf` names the run-time name for the walk, which
/// keeps what each leaf stands for; the normal form reads only `ty`.
pub const Slot = struct {
    ty: TyId,
    source: Source,

    pub const Source = union(enum) {
        /// The run-time name the walk numbered `leaf`.
        leaf: u32,
        /// A read of slot `of`: field `k` in the record type's order, element
        /// `k` of a tuple, or the backing of a nominal.
        field: struct { of: SlotId, k: u32 },
        index: struct { of: SlotId, k: u32 },
        unwrap: SlotId,
    };
};

/// The operation of a node. The declaration order is the op precedence the
/// orientation check of `roc-reify-rule-derivation.md` 2.2 breaks ties with.
pub const Op = enum(u8) {
    lit,
    crash,
    derived,
    record,
    tuple,
    list,
    tag,
    wrap,
    closure,
    field,
    index,
    payload,
    elem,
    opt_field,
    unwrap,
    prim,
    call,
    and_,
    or_,
    switch_,
    for_range,
    for_list,
    loop,
    lambda,
    /// A call through a function value the walk does not know: the value is
    /// the first argument, the call's arguments follow. It exists only
    /// during simplification (N8i); a normal row holds none (N8j).
    apply,

    /// Whether the op owns regions.
    pub fn ownsRegions(self: Op) bool {
        return switch (self) {
            .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda => true,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .apply => false,
        };
    }

    /// Whether the op is a loop.
    pub fn isLoop(self: Op) bool {
        return switch (self) {
            .for_range, .for_list, .loop => true,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .lambda, .apply => false,
        };
    }
};

/// How a `record` node says which members of its type it sets. A node that
/// sets every member holds one argument per member, in the type's order. A
/// node that leaves an optional member unset holds one argument per member it
/// sets, and `aux` lists those members' positions in the type's order. A value
/// has one form, so a node never lists the members when it sets all of them.
pub const RecordForm = enum {
    every_member,
    listed_members,
};

/// Why a region exists; the verifier and the evaluator read it.
pub const RegionKind = enum(u8) {
    row_body,
    arm,
    join,
    operand,
    loop_body,
    lambda_body,
};

/// How a region ends.
pub const EndKind = enum(u8) {
    /// Not closed yet; only while the builder has the region open.
    open,
    /// `Value(refs)`: the region's results.
    value,
    /// `Jump(join, refs)`: `target` is the join region.
    jump,
    /// `Return(ref)`: leaves the row.
    return_,
    /// `Branch(switch)`: `target` is the exiting switch node.
    branch,
    /// `Continue(refs)`: the next turn of the innermost loop.
    continue_,
    /// `Break(refs)`: leaves the innermost loop with one value per output of the loop.
    break_,
};

/// A region's terminator.
pub const End = struct {
    kind: EndKind,
    target: u32,
    refs: Span,
};

/// Node flags.
pub const Flags = packed struct(u8) {
    speculatable: bool = false,
    _pad: u7 = 0,
};

/// One node's row in the node columns.
pub const Node = struct {
    op: Op,
    flags: Flags,
    /// What `Node.payload` holds for each op.
    ///
    /// | op | payload |
    /// |---|---|
    /// | `lit` | `LitId` |
    /// | `prim` | `PrimId` |
    /// | `call`, `closure` | `RowId` |
    /// | `tag` | the tag's name (`types.NameId`) |
    /// | `field`, `index`, `opt_field` | field or element index in the type's order |
    /// | `payload` | the tag's name (`types.NameId`); the payload position is `aux[0]` |
    /// | `switch_` | number of arms; the remaining regions are joins. A tag switch has one arm per member of its scrutinee's own type, in name order. |
    /// | `derived` | the method's name (`types.NameId`); the subject type is `aux[0]` |
    /// | `for_range` | 1 when the range includes its end, else 0 |
    /// | every other op | 0 |
    ///
    /// A `crash` reads its message as its one argument, a `closure` its
    /// captured values as its arguments, and an `apply` the function value
    /// and then the call's arguments.
    ///
    /// Loops read their arguments and give their body parameters this way. A
    /// `for_range` or `for_list` has one output per slot; a `loop` has the
    /// outputs its `Break`s carry, which are its `tys` and need not be its
    /// slots:
    ///
    /// | op | args | body params |
    /// |---|---|---|
    /// | `for_range` | start, end, initial slots | index, slots |
    /// | `for_list` | list, initial slots | index, element, slots |
    /// | `loop` | initial slots | slots |
    ///
    /// A switch's `aux` holds its keys when it switches on a literal: one
    /// `LitId` per arm but the last, which is the default arm.
    payload: u32,
    region: RegionId,
    args: Span,
    tys: Span,
    regions: Span,
    aux: Span,
};

/// One region's row in the region columns.
pub const Region = struct {
    kind: RegionKind,
    row: RowId,
    /// The region the owner node sits in; `none` for a row body.
    parent: RegionId,
    /// The node that owns this region; `none` for a row body and while the owner is being built.
    owner: NodeId,
    params: Span,
    end: End,
    depth: u32,
    /// Whether every node in the region, nested regions included, is speculatable.
    speculatable: bool,
};

/// One row's entry in the row table.
pub const Row = struct {
    params: Span,
    result: TyId,
    body: RegionId,
    recursive: bool,
    /// Whether a call of the row is speculatable: its body is, and it ends in `Value`.
    speculatable: bool,
    /// The row's digest (N8g), set when the row is finalized.
    digest: ?u128 = null,
    /// The row this one merged into at finalize (N8g). Nothing calls a row
    /// that merged, and no closure names it.
    merged_into: ?RowId = null,
    /// Whether the row keeps its parameters as they are at finalize (N8f):
    /// the root, whose parameters are the type in `Code(fn)`, and a row
    /// that gives a closure its type's calling convention.
    fixed_params: bool = false,
};

/// A literal's value. Floats and integers are compared by their bits.
pub const LitValue = union(enum) {
    int: u128,
    float: u64,
    bool_: bool,
    str: Span,
    /// A `Dec`, by the bits of its `i128` representation.
    dec: u128,
    /// The contents of an embedded file, as a `List(U8)`.
    bytes: Span,
};

/// The role the checker gave a builtin iterator procedure (N11k), which the
/// walk records on the primitive it names. A rule that reads an iterator
/// loop reads this role and never the name of the type, so a function of
/// another package with the same names has no role.
pub const IteratorRole = enum(u8) {
    /// Any other primitive.
    none,
    /// `Iter.iter`: an iterator is its own iterator.
    identity,
    /// `Iter.next`: the iterator protocol's step.
    next,
    /// `List.iter`: an iterator that yields every element of a list in index
    /// order, one per step, and never skips.
    list_iter,
};

/// A primitive the builtin table does not hold, by the names its owner gives
/// it: a builtin such as `Num.F32` and `sin`, or a function of another
/// package that does not expose its body (N8h), such as `Glsl.Vec3` and
/// `scale`. Its `PrimId` is `prims.table.len` plus its index here.
pub const NamedPrim = struct {
    owner: Span,
    method: Span,
    role: IteratorRole = .none,
};

/// A primitive's owner and method names, and the role of an iterator
/// procedure.
pub const PrimName = struct {
    owner: []const u8,
    method: []const u8,
    role: IteratorRole = .none,
};

/// One literal's entry: its type and value.
pub const Lit = struct {
    ty: TyId,
    value: LitValue,
};

/// The IR of one module's reification: every row, region, node and literal.
pub const Store = struct {
    gpa: Allocator,
    nodes: std.MultiArrayList(Node) = .empty,
    regions: std.MultiArrayList(Region) = .empty,
    rows: std.ArrayList(Row) = .empty,
    lits: std.ArrayList(Lit) = .empty,
    refs: std.ArrayList(Ref) = .empty,
    tys: std.ArrayList(TyId) = .empty,
    region_ids: std.ArrayList(RegionId) = .empty,
    words: std.ArrayList(u32) = .empty,
    bytes: std.ArrayList(u8) = .empty,
    named_prims: std.ArrayList(NamedPrim) = .empty,
    /// The input slots the walk made (N18), in the order it made them.
    slots: std.ArrayList(Slot) = .empty,
    /// Per node, where it came from (N10). Nothing in the normal form reads it.
    provenance: provenance.Provenance = .{},

    pub fn init(gpa: Allocator) Store {
        return .{ .gpa = gpa };
    }

    pub fn deinit(self: *Store) void {
        self.nodes.deinit(self.gpa);
        self.regions.deinit(self.gpa);
        self.rows.deinit(self.gpa);
        self.lits.deinit(self.gpa);
        self.refs.deinit(self.gpa);
        self.tys.deinit(self.gpa);
        self.region_ids.deinit(self.gpa);
        self.words.deinit(self.gpa);
        self.bytes.deinit(self.gpa);
        self.named_prims.deinit(self.gpa);
        self.slots.deinit(self.gpa);
        self.provenance.deinit(self.gpa);
    }

    /// Append `items` to the ref pool.
    pub fn addRefs(self: *Store, items: []const Ref) Allocator.Error!Span {
        const start: u32 = @intCast(self.refs.items.len);
        try self.refs.appendSlice(self.gpa, items);
        return .{ .start = start, .len = @intCast(items.len) };
    }

    /// Append `items` to the type pool.
    pub fn addTys(self: *Store, items: []const TyId) Allocator.Error!Span {
        const start: u32 = @intCast(self.tys.items.len);
        try self.tys.appendSlice(self.gpa, items);
        return .{ .start = start, .len = @intCast(items.len) };
    }

    /// Append `items` to the region-id pool.
    pub fn addRegionIds(self: *Store, items: []const RegionId) Allocator.Error!Span {
        const start: u32 = @intCast(self.region_ids.items.len);
        try self.region_ids.appendSlice(self.gpa, items);
        return .{ .start = start, .len = @intCast(items.len) };
    }

    /// Append `items` to the immediate pool.
    pub fn addWords(self: *Store, items: []const u32) Allocator.Error!Span {
        const start: u32 = @intCast(self.words.items.len);
        try self.words.appendSlice(self.gpa, items);
        return .{ .start = start, .len = @intCast(items.len) };
    }

    /// Append `items` to the byte pool.
    pub fn addBytes(self: *Store, items: []const u8) Allocator.Error!Span {
        const start: u32 = @intCast(self.bytes.items.len);
        try self.bytes.appendSlice(self.gpa, items);
        return .{ .start = start, .len = @intCast(items.len) };
    }

    /// The refs of a span.
    pub fn refSlice(self: *const Store, span: Span) []const Ref {
        return self.refs.items[span.start..][0..span.len];
    }

    /// The types of a span.
    pub fn tySlice(self: *const Store, span: Span) []const TyId {
        return self.tys.items[span.start..][0..span.len];
    }

    /// The region ids of a span.
    pub fn regionSlice(self: *const Store, span: Span) []const RegionId {
        return self.region_ids.items[span.start..][0..span.len];
    }

    /// The immediates of a span.
    pub fn wordSlice(self: *const Store, span: Span) []const u32 {
        return self.words.items[span.start..][0..span.len];
    }

    /// The bytes of a span.
    pub fn byteSlice(self: *const Store, span: Span) []const u8 {
        return self.bytes.items[span.start..][0..span.len];
    }

    /// The node with id `n`.
    pub fn node(self: *const Store, n: NodeId) Node {
        return self.nodes.get(n.index());
    }

    /// The region with id `r`.
    pub fn region(self: *const Store, r: RegionId) Region {
        return self.regions.get(r.index());
    }

    /// The row with id `r`.
    pub fn row(self: *const Store, r: RowId) Row {
        return self.rows.items[r.index()];
    }

    /// The names of primitive `id`, whether the table holds it or this store.
    pub fn primName(self: *const Store, id: PrimId) PrimName {
        if (prims.lookup(id)) |p| return .{ .owner = p.owner.text(), .method = prims.methodName(p.method) };
        const named = self.named_prims.items[id.index() - prims.table.len];
        return .{ .owner = self.byteSlice(named.owner), .method = self.byteSlice(named.method), .role = named.role };
    }

    /// The literal with id `l`.
    pub fn lit(self: *const Store, l: LitId) Lit {
        return self.lits.items[l.index()];
    }

    /// The number of nodes.
    pub fn nodeCount(self: *const Store) u32 {
        return @intCast(self.nodes.len);
    }

    /// The number of regions.
    pub fn regionCount(self: *const Store) u32 {
        return @intCast(self.regions.len);
    }

    /// Append a node and return its id.
    pub fn appendNode(self: *Store, n: Node) Allocator.Error!NodeId {
        const id = NodeId.of(@intCast(self.nodes.len));
        try self.nodes.append(self.gpa, n);
        return id;
    }

    /// Append a region and return its id.
    pub fn appendRegion(self: *Store, r: Region) Allocator.Error!RegionId {
        const id = RegionId.of(@intCast(self.regions.len));
        try self.regions.append(self.gpa, r);
        return id;
    }

    /// Set the terminator of region `r`.
    pub fn setEnd(self: *Store, r: RegionId, end: End) void {
        self.regions.items(.end)[r.index()] = end;
    }

    /// Set the owner of region `r`.
    pub fn setOwner(self: *Store, r: RegionId, owner: NodeId) void {
        self.regions.items(.owner)[r.index()] = owner;
    }

    /// Whether region `outer` encloses region `inner`, or is it.
    pub fn encloses(self: *const Store, outer: RegionId, inner: RegionId) bool {
        const parents = self.regions.items(.parent);
        const depths = self.regions.items(.depth);
        const outer_depth = depths[outer.index()];
        var cur = inner;
        while (cur != RegionId.none) {
            if (cur == outer) return true;
            if (depths[cur.index()] <= outer_depth) return false;
            cur = parents[cur.index()];
        }
        return false;
    }

    /// The call a row's body only makes, when the row is finalized, not
    /// recursive, and its body only calls another row over its own
    /// parameters (N8c over calls). A call of the row is that call.
    pub fn forwardingCall(self: *const Store, r: RowId) ?NodeId {
        const info = self.row(r);
        if (info.digest == null or info.recursive) return null;
        const end = self.region(info.body).end;
        if (end.kind != .value or end.refs.len != 1) return null;
        const ref = self.refSlice(end.refs)[0];
        if (ref.kind != .node) return null;
        const n = ref.nodeId();
        const nd = self.node(n);
        if (nd.op != .call or nd.region != info.body or nd.payload == r.index()) return null;
        for (self.refSlice(nd.args)) |a| if (a.kind != .row_param) return null;
        return n;
    }

    /// The type of the value `ref` reads.
    pub fn refTy(self: *const Store, row_id: RowId, ref: Ref) TyId {
        return switch (ref.kind) {
            .node => self.tySlice(self.nodes.items(.tys)[ref.target])[ref.output],
            .row_param => self.tySlice(self.row(row_id).params)[ref.output],
            .region_param => self.tySlice(self.regions.items(.params)[ref.target])[ref.output],
            .input => self.slots.items[ref.target].ty,
        };
    }

    /// The slot `source` names, made the first time it is asked for, so one
    /// leaf or one projection of a slot is one slot.
    pub fn slot(self: *Store, ty: TyId, source: Slot.Source) Allocator.Error!SlotId {
        for (self.slots.items, 0..) |existing, i| {
            if (std.meta.eql(existing.source, source)) {
                std.debug.assert(existing.ty == ty);
                return SlotId.of(@intCast(i));
            }
        }
        const id = SlotId.of(@intCast(self.slots.items.len));
        try self.slots.append(self.gpa, .{ .ty = ty, .source = source });
        return id;
    }
};

test "encloses follows the parent chain" {
    var store = Store.init(std.testing.allocator);
    defer store.deinit();
    const row = RowId.of(0);
    const body = try store.appendRegion(.{ .kind = .row_body, .row = row, .parent = .none, .owner = .none, .params = .empty, .end = .{ .kind = .open, .target = 0, .refs = .empty }, .depth = 0, .speculatable = true });
    const arm = try store.appendRegion(.{ .kind = .arm, .row = row, .parent = body, .owner = .none, .params = .empty, .end = .{ .kind = .open, .target = 0, .refs = .empty }, .depth = 1, .speculatable = true });
    const other = try store.appendRegion(.{ .kind = .arm, .row = row, .parent = body, .owner = .none, .params = .empty, .end = .{ .kind = .open, .target = 0, .refs = .empty }, .depth = 1, .speculatable = true });
    try std.testing.expect(store.encloses(body, arm));
    try std.testing.expect(store.encloses(arm, arm));
    try std.testing.expect(!store.encloses(arm, body));
    try std.testing.expect(!store.encloses(arm, other));
}
