//! The normal form written into a module's `ConstStore` as the `Code` value
//! `Builtin.roc` declares (I8).
//!
//! A site's value is `Code`'s backing, `{ graph, site, version }`. The graph
//! holds the rows the site's root reaches through `Call` and `Closure`, root
//! first, and each row holds only what its ends reach. The nominals of the
//! value are transparent (`:=`), so the emitter writes bare tags and records,
//! and a record's fields in label order, which is the order a constant record
//! is restored in.
//!
//! Rows and nodes are numbered canonically (N9, `reify.number`): a row's
//! nodes in the post-order of a walk from its body's end, and a region's
//! nodes in that order. The walk numbers a node's arguments before it, so
//! every `Val` names a node with a smaller index than its reader, or a
//! parameter.

const std = @import("std");
const collections = @import("collections");
const reify = @import("reify");
const const_store = @import("const_store.zig");

const Allocator = std.mem.Allocator;
const ConstNodeId = const_store.ConstNodeId;
const ConstStore = const_store.ConstStore;
const ir = reify.ir;
const types_mod = reify.types;
const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const RowId = ir.RowId;
const Ref = ir.Ref;
const TyId = ir.TyId;

/// The normal-form version a `Code` value carries (I11): the rules, the
/// speculatable list and the builtin table change only with it.
pub const version: u32 = reify.normal_form_version;

/// Writes the `Code` values of one module's sites, which share one store and
/// one type table.
pub const Emitter = struct {
    gpa: Allocator,
    out: *ConstStore,
    store: *const ir.Store,
    types: *const types_mod.Types,
    /// Per node: its index in its row's numbering, while that row is written.
    index: []u32,
    /// Per region of the row being written: its nodes, in numbering order.
    region_nodes: collections.DenseMapUnmanaged(RegionId, std.ArrayList(NodeId)) = .empty,
    ty_cache: collections.DenseMapUnmanaged(TyId, ConstNodeId) = .empty,
    str_cache: std.StringHashMapUnmanaged(ConstNodeId) = .empty,
    /// Per row of the site being written: its index in the graph.
    row_index: collections.DenseMapUnmanaged(RowId, u32) = .empty,
    /// The input slots the root of the graph last written reads, in slot
    /// order (N18d). `Input(k)` reads `slot_order[k]`.
    slot_order: []ir.SlotId = &.{},

    /// An emitter over `store`, whose rows are in their normal form.
    pub fn init(gpa: Allocator, out: *ConstStore, store: *const ir.Store, types: *const types_mod.Types) Allocator.Error!Emitter {
        const index = try gpa.alloc(u32, store.nodeCount());
        @memset(index, std.math.maxInt(u32));
        return .{ .gpa = gpa, .out = out, .store = store, .types = types, .index = index };
    }

    pub fn deinit(self: *Emitter) void {
        self.clearRegions();
        self.region_nodes.deinit(self.gpa);
        self.gpa.free(self.index);
        self.ty_cache.deinit(self.gpa);
        var keys = self.str_cache.keyIterator();
        while (keys.next()) |k| self.gpa.free(k.*);
        self.str_cache.deinit(self.gpa);
        self.row_index.deinit(self.gpa);
        self.gpa.free(self.slot_order);
    }

    fn clearRegions(self: *Emitter) void {
        var lists = self.region_nodes.valueIterator();
        while (lists.next()) |l| l.deinit(self.gpa);
        self.region_nodes.clearRetainingCapacity();
    }

    /// The `Code` backing for the site whose root is `root`: the rows it
    /// reaches, the site's key, and the version.
    pub fn site(self: *Emitter, root: RowId, site_key: u64) Allocator.Error!ConstNodeId {
        return self.siteOf(try self.graph(root), site_key);
    }

    /// The `Code` backing over a graph already written, for another site
    /// with the same normal form (P1).
    pub fn siteOf(self: *Emitter, graph_node: ConstNodeId, site_key: u64) Allocator.Error!ConstNodeId {
        return self.record(&.{ graph_node, try self.scalar(.{ .u64 = site_key }), try self.u32Node(version) });
    }

    /// The `Graph` of the site whose root is `root`: the rows it reaches.
    pub fn graph(self: *Emitter, root: RowId) Allocator.Error!ConstNodeId {
        self.row_index.clearRetainingCapacity();
        var returns = try reify.live.Returns.init(self.gpa, self.store);
        defer returns.deinit(self.gpa);
        var rows: reify.ir.RowTable(reify.number.Numbering) = .empty;
        defer {
            for (rows.values()) |*n| n.deinit(self.gpa);
            rows.deinit(self.gpa);
        }
        try reify.number.siteRows(self.gpa, self.store, &returns, root, &rows);
        for (rows.keys(), 0..) |r, i| try self.row_index.put(self.gpa, r, @intCast(i));
        self.gpa.free(self.slot_order);
        self.slot_order = &.{};
        self.slot_order = try reify.number.slotOrder(self.gpa, self.store, root, &rows.values()[0]);
        const row_nodes = try self.gpa.alloc(ConstNodeId, rows.count());
        defer self.gpa.free(row_nodes);
        for (rows.keys(), rows.values(), row_nodes) |r, *numbering, *node| node.* = try self.rowValue(r, numbering);
        const slot_tys = try self.gpa.alloc(TyId, self.slot_order.len);
        defer self.gpa.free(slot_tys);
        for (self.slot_order, slot_tys) |slot, *t| t.* = self.store.slots.items[slot.index()].ty;
        // `Graph := { root, rows, slots }`, in label order.
        return self.record(&.{ try self.u32Node(0), try self.listOf(row_nodes), try self.tyList(slot_tys) });
    }

    // `Row := { id, params, result, nodes, body, recursive }`.
    fn rowValue(self: *Emitter, r: RowId, numbering: *const reify.number.Numbering) Allocator.Error!ConstNodeId {
        const info = self.store.row(r);
        const order = numbering.order.items;
        self.clearRegions();
        const regions = self.store.nodes.items(.region);
        for (order, 0..) |n, i| {
            self.index[n.index()] = @intCast(i);
            const gop = try self.region_nodes.getOrPut(self.gpa, regions[n.index()]);
            if (!gop.found_existing) gop.value_ptr.* = .empty;
            try gop.value_ptr.append(self.gpa, n);
        }
        const nodes = try self.gpa.alloc(ConstNodeId, order.len);
        defer self.gpa.free(nodes);
        for (order, nodes) |n, *out| out.* = try self.nodeValue(r, n);
        return self.record(&.{
            try self.regionValue(info.body),
            try self.u32Node(self.row_index.get(r).?),
            try self.listOf(nodes),
            try self.tyList(self.store.tySlice(info.params)),
            try self.boolNode(info.recursive),
            try self.ty(info.result),
        });
    }

    // `Region := { params, nodes, end }`.
    fn regionValue(self: *Emitter, id: RegionId) Allocator.Error!ConstNodeId {
        const info = self.store.region(id);
        const members: []const NodeId = if (self.region_nodes.get(id)) |list| list.items else &.{};
        const indices = try self.gpa.alloc(ConstNodeId, members.len);
        defer self.gpa.free(indices);
        for (members, indices) |n, *out| out.* = try self.u32Node(self.index[n.index()]);
        return self.record(&.{ try self.end(info.end), try self.listOf(indices), try self.tyList(self.store.tySlice(info.params)) });
    }

    fn end(self: *Emitter, e: ir.End) Allocator.Error!ConstNodeId {
        const refs = self.store.refSlice(e.refs);
        return switch (e.kind) {
            .open => invariant("a region the emitter reads is not closed"),
            .value => self.tag("Value", &.{try self.vals(refs)}),
            .continue_ => self.tag("Continue", &.{try self.vals(refs)}),
            .break_ => self.tag("Break", &.{try self.vals(refs)}),
            .return_ => self.tag("Return", &.{try self.val(refs[0])}),
            .branch => self.tag("Branch", &.{try self.u32Node(self.index[e.target])}),
            .jump => blk: {
                const join = RegionId.of(e.target);
                const sw = self.store.node(self.store.region(join).owner);
                const joins = self.store.regionSlice(sw.regions)[sw.payload..];
                const at = positionOf(joins, join) orelse invariant("a jump to a region that is not a join of its switch");
                break :blk self.tag("Jump", &.{try self.record(&.{ try self.vals(refs), try self.u32Node(@intCast(at)) })});
            },
        };
    }

    fn vals(self: *Emitter, refs: []const Ref) Allocator.Error!ConstNodeId {
        const out = try self.gpa.alloc(ConstNodeId, refs.len);
        defer self.gpa.free(out);
        for (refs, out) |ref, *o| o.* = try self.val(ref);
        return self.listOf(out);
    }

    fn val(self: *Emitter, ref: Ref) Allocator.Error!ConstNodeId {
        return switch (ref.kind) {
            .row_param => self.tag("Param", &.{try self.u32Node(ref.output)}),
            .input => blk: {
                const k = std.mem.findScalar(ir.SlotId, self.slot_order, ref.slotId()) orelse
                    invariant("a live value reads an input slot the root's slot order does not hold");
                break :blk self.tag("Input", &.{try self.u32Node(@intCast(k))});
            },
            .region_param => blk: {
                const owner = self.store.region(ref.regionId()).owner;
                break :blk self.tag("Arg", &.{try self.record(&.{ try self.u32Node(ref.output), try self.u32Node(self.index[owner.index()]) })});
            },
            .node => blk: {
                const n = ref.nodeId();
                const at = self.index[n.index()];
                if (at == std.math.maxInt(u32)) invariant("a live value reads a node outside its row");
                if (self.store.node(n).tys.len == 1) break :blk self.tag("Node", &.{try self.u32Node(at)});
                break :blk self.tag("Out", &.{try self.record(&.{ try self.u32Node(ref.output), try self.u32Node(at) })});
            },
        };
    }

    // `Node := { op, args, ty, speculatable }`.
    fn nodeValue(self: *Emitter, r: RowId, n: NodeId) Allocator.Error!ConstNodeId {
        const nd = self.store.node(n);
        const tys = self.store.tySlice(nd.tys);
        const node_ty = switch (tys.len) {
            1 => try self.ty(tys[0]),
            else => try self.tag("Tuple", &.{try self.tyList(tys)}),
        };
        return self.record(&.{
            try self.vals(self.store.refSlice(nd.args)),
            try self.op(r, nd),
            try self.boolNode(nd.flags.speculatable),
            node_ty,
        });
    }

    fn op(self: *Emitter, r: RowId, nd: ir.Node) Allocator.Error!ConstNodeId {
        const args = self.store.refSlice(nd.args);
        const regions = self.store.regionSlice(nd.regions);
        const tys = self.store.tySlice(nd.tys);
        return switch (nd.op) {
            .lit => self.tag("Lit", &.{try self.lit(ir.LitId.of(nd.payload))}),
            .prim => blk: {
                const name = self.store.primName(ir.PrimId.of(nd.payload));
                break :blk self.tag("Prim", &.{try self.record(&.{ try self.str(name.method), try self.str(name.owner) })});
            },
            .call => self.tag("Call", &.{try self.u32Node(self.row_index.get(RowId.of(nd.payload)).?)}),
            .closure => self.tag("Closure", &.{try self.u32Node(self.row_index.get(RowId.of(nd.payload)).?)}),
            .record => blk: {
                // The names of the fields the node sets: every field of the
                // type, or the ones it lists where it leaves a field unset
                // (`ir.RecordForm`).
                const fields = self.types.memberSlice(self.types.get(tys[0]).record);
                const set = self.store.wordSlice(nd.aux);
                const names = try self.gpa.alloc(ConstNodeId, args.len);
                defer self.gpa.free(names);
                for (names, 0..) |*o, at| {
                    const field = if (args.len == fields.len) fields[at] else fields[set[at]];
                    o.* = try self.str(self.types.nameText(field.name));
                }
                break :blk self.tag("Record", &.{try self.listOf(names)});
            },
            .tuple => self.tag("Tuple", &.{}),
            .list => self.tag("List", &.{}),
            .tag => self.tag("Tag", &.{try self.str(self.types.nameText(types_mod.NameId.of(nd.payload)))}),
            .wrap => self.tag("Wrap", &.{try self.str(self.types.nameText(self.types.get(tys[0]).nominal.name))}),
            .unwrap => self.tag("Unwrap", &.{}),
            .field => self.tag("Field", &.{try self.str(self.fieldName(self.store.refTy(r, args[0]), nd.payload))}),
            .opt_field => self.tag("OptField", &.{try self.str(self.fieldName(self.store.refTy(r, args[0]), nd.payload))}),
            .index => self.tag("Index", &.{try self.scalar(.{ .u64 = nd.payload })}),
            .payload => self.tag("Payload", &.{
                try self.str(self.types.nameText(types_mod.NameId.of(nd.payload))),
                try self.scalar(.{ .u64 = self.store.wordSlice(nd.aux)[0] }),
            }),
            .elem => self.tag("Item", &.{}),
            .crash => self.tag("Crash", &.{}),
            .derived => self.tag("Derived", &.{
                try self.str(self.types.nameText(types_mod.NameId.of(nd.payload))),
                try self.ty(TyId.of(self.store.wordSlice(nd.aux)[0])),
            }),
            .and_ => self.tag("And", &.{try self.regionList(regions)}),
            .or_ => self.tag("Or", &.{try self.regionList(regions)}),
            .for_range => self.tag("ForRange", &.{try self.record(&.{ try self.regionValue(regions[0]), try self.boolNode(nd.payload == 1) })}),
            .for_list => self.tag("ForList", &.{try self.regionValue(regions[0])}),
            .loop => self.tag("Loop", &.{try self.record(&.{
                try self.regionValue(regions[0]),
                try self.tyList(self.store.tySlice(nd.tys)),
            })}),
            .lambda => self.tag("Lambda", &.{try self.regionValue(regions[0])}),
            .switch_ => self.switchOp(r, nd, args[0], regions),
            // An `Apply` a site reaches refuses the site before it is emitted (N8j).
            .apply => invariant("an Apply reached the emitter"),
        };
    }

    // `Switch({ arms : List({ key, region }), joins, outputs })`.
    fn switchOp(self: *Emitter, r: RowId, nd: ir.Node, scrutinee: Ref, regions: []const RegionId) Allocator.Error!ConstNodeId {
        const arms = regions[0..nd.payload];
        const keys = self.store.wordSlice(nd.aux);
        const on = self.store.refTy(r, scrutinee);
        const arm_nodes = try self.gpa.alloc(ConstNodeId, arms.len);
        defer self.gpa.free(arm_nodes);
        for (arms, arm_nodes, 0..) |arm, *o, k| {
            const key = if (keys.len > 0)
                if (k < keys.len) try self.tag("Lit", &.{try self.lit(ir.LitId.of(keys[k]))}) else try self.tag("Default", &.{})
            else switch (self.types.get(on)) {
                .bool_ => try self.tag("Lit", &.{try self.tag("Bool", &.{try self.boolNode(k == 1)})}),
                .tag_union => try self.tag("Tag", &.{try self.str(self.memberName(on, @intCast(k)))}),
                .str, .int, .float, .dec, .record, .tuple, .list, .nominal, .func, .opaque_, .recursive => invariant("a switch without keys on a type that is neither Bool nor a tag union"),
            };
            o.* = try self.record(&.{ key, try self.regionValue(arm) });
        }
        return self.tag("Switch", &.{try self.record(&.{
            try self.listOf(arm_nodes),
            try self.regionList(regions[nd.payload..]),
            try self.tyList(self.store.tySlice(nd.tys)),
        })});
    }

    fn regionList(self: *Emitter, regions: []const RegionId) Allocator.Error!ConstNodeId {
        const out = try self.gpa.alloc(ConstNodeId, regions.len);
        defer self.gpa.free(out);
        for (regions, out) |sub, *o| o.* = try self.regionValue(sub);
        return self.listOf(out);
    }

    /// The name of member `k` of the tag union `union_ty`.
    fn memberName(self: *Emitter, union_ty: TyId, k: u32) []const u8 {
        const tags = self.types.memberSlice(self.types.get(union_ty).tag_union);
        return self.types.nameText(tags[k].name);
    }

    fn fieldName(self: *Emitter, record_ty: TyId, k: u32) []const u8 {
        const fields = self.types.memberSlice(self.types.get(record_ty).record);
        return self.types.nameText(fields[k].name);
    }

    // `Lit := [Int(I128, Ty), Frac(F64, Ty), Fixed(Dec), Bool(Bool), Str(Str), Bytes(List(U8))]`.
    fn lit(self: *Emitter, id: ir.LitId) Allocator.Error!ConstNodeId {
        const l = self.store.lit(id);
        return switch (l.value) {
            .int => |bits| self.tag("Int", &.{ try self.scalar(.{ .i128 = @bitCast(bits) }), try self.ty(l.ty) }),
            .float => |bits| blk: {
                const value: f64 = switch (self.types.get(l.ty).float) {
                    .f64 => @bitCast(bits),
                    .f32 => @as(f32, @bitCast(@as(u32, @intCast(bits)))),
                };
                break :blk self.tag("Frac", &.{ try self.scalar(.{ .f64_bits = @bitCast(value) }), try self.ty(l.ty) });
            },
            .dec => |bits| self.tag("Fixed", &.{try self.scalar(.{ .dec_bits = @bitCast(bits) })}),
            .bool_ => |b| self.tag("Bool", &.{try self.boolNode(b)}),
            .str => |span| self.tag("Str", &.{try self.str(self.store.byteSlice(span))}),
            .bytes => |span| blk: {
                const bytes = self.store.byteSlice(span);
                const data = try self.out.addBlobData(bytes);
                const packed_node = try self.out.append(.{ .list = .{ .packed_bytes = .{
                    .bytes = .{ .data = data, .offset = 0, .len = @intCast(bytes.len) },
                    .len = @intCast(bytes.len),
                    .element = .u8,
                } } });
                break :blk self.tag("Bytes", &.{packed_node});
            },
        };
    }

    // `Ty`, as `Builtin.roc` declares it.
    fn ty(self: *Emitter, id: TyId) Allocator.Error!ConstNodeId {
        if (self.ty_cache.get(id)) |cached| return cached;
        const node = switch (self.types.get(id)) {
            .bool_ => try self.tag("Bool", &.{}),
            .str => try self.tag("Str", &.{}),
            .dec => try self.tag("Dec", &.{}),
            .int => |int| try self.tag(switch (int) {
                .u8 => "U8",
                .i8 => "I8",
                .u16 => "U16",
                .i16 => "I16",
                .u32 => "U32",
                .i32 => "I32",
                .u64 => "U64",
                .i64 => "I64",
                .u128 => "U128",
                .i128 => "I128",
            }, &.{}),
            .float => |float| try self.tag(switch (float) {
                .f32 => "F32",
                .f64 => "F64",
            }, &.{}),
            .list => |elem| try self.tag("ListOf", &.{try self.ty(elem)}),
            .tuple => |span| try self.tag("Tuple", &.{try self.tyList(self.types.tySlice(span))}),
            .record => |span| blk: {
                const fields = self.types.memberSlice(span);
                const entries = try self.gpa.alloc(ConstNodeId, fields.len);
                defer self.gpa.free(entries);
                for (fields, entries) |f, *o| o.* = try self.record(&.{
                    try self.str(self.types.nameText(f.name)),
                    try self.tag(if (f.optional) "Optional" else "Required", &.{}),
                    try self.ty(self.types.tySlice(f.tys)[0]),
                });
                break :blk try self.tag("Record", &.{try self.listOf(entries)});
            },
            .tag_union => |span| blk: {
                const tags = self.types.memberSlice(span);
                const entries = try self.gpa.alloc(ConstNodeId, tags.len);
                defer self.gpa.free(entries);
                for (tags, entries) |t, *o| o.* = try self.record(&.{
                    try self.str(self.types.nameText(t.name)),
                    try self.tyList(self.types.tySlice(t.tys)),
                });
                break :blk try self.tag("TagUnion", &.{try self.listOf(entries)});
            },
            .nominal => |n| try self.tag("Named", &.{ try self.str(self.types.nameText(n.name)), try self.ty(n.backing) }),
            .func => |f| try self.tag("Fn", &.{ try self.tyList(self.types.tySlice(f.params)), try self.ty(f.ret) }),
            .opaque_ => |o| try self.tag("Opaque", &.{ try self.str(self.types.nameText(o.name)), try self.tyList(self.types.tySlice(o.args)) }),
            .recursive => |name| try self.tag("Recursive", &.{try self.str(self.types.nameText(name))}),
        };
        try self.ty_cache.put(self.gpa, id, node);
        return node;
    }

    fn tyList(self: *Emitter, ids: []const TyId) Allocator.Error!ConstNodeId {
        const out = try self.gpa.alloc(ConstNodeId, ids.len);
        defer self.gpa.free(out);
        for (ids, out) |id, *o| o.* = try self.ty(id);
        return self.listOf(out);
    }

    fn tag(self: *Emitter, name: []const u8, payloads: []const ConstNodeId) Allocator.Error!ConstNodeId {
        return self.out.append(.{ .tag = .{ .tag_name = name, .payloads = payloads } });
    }

    fn record(self: *Emitter, fields: []const ConstNodeId) Allocator.Error!ConstNodeId {
        return self.out.append(.{ .record = fields });
    }

    fn listOf(self: *Emitter, items: []const ConstNodeId) Allocator.Error!ConstNodeId {
        return self.out.append(.{ .list = .{ .nodes = items } });
    }

    fn scalar(self: *Emitter, value: const_store.ConstScalar) Allocator.Error!ConstNodeId {
        return self.out.append(.{ .scalar = value });
    }

    fn u32Node(self: *Emitter, value: u32) Allocator.Error!ConstNodeId {
        return self.scalar(.{ .u32 = value });
    }

    fn boolNode(self: *Emitter, value: bool) Allocator.Error!ConstNodeId {
        return self.tag(if (value) "True" else "False", &.{});
    }

    // A `Str`, shared with every other node of the same text.
    fn str(self: *Emitter, text: []const u8) Allocator.Error!ConstNodeId {
        if (self.str_cache.get(text)) |existing| return existing;
        const data = try self.out.addBlobData(text);
        const node = try self.out.append(.{ .str = .{ .data = data, .offset = 0, .len = @intCast(text.len) } });
        const key = try self.gpa.dupe(u8, text);
        errdefer self.gpa.free(key);
        try self.str_cache.put(self.gpa, key, node);
        return node;
    }
};

fn invariant(comptime message: []const u8) noreturn {
    @import("base").invariant("code_emit invariant violated: " ++ message, .{});
}

const testing = std.testing;

test "a site's value holds its reached rows root first, with the nodes it reaches numbered in post-order" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = reify.builder.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const bool_ty = try types.boolTy();
    const i64_ty = try types.intTy(.i64);
    // callee(x) = x * x
    const callee = try b.beginRow(&.{i64_ty}, i64_ty);
    try b.endRow(.{ .value = &.{try b.call(.i64, .times, &.{ Ref.rowParam(0), Ref.rowParam(0) })} });
    // root(c, x) = if c { callee(x) } else { x }, with a dead node
    const root = try b.beginRow(&.{ bool_ty, i64_ty }, i64_ty);
    _ = try b.call(.i64, .plus, &.{ Ref.rowParam(1), Ref.rowParam(1) });
    const arm0 = try b.openArm(Ref.rowParam(0), 0);
    try b.close(.{ .value = &.{Ref.rowParam(1)} });
    const arm1 = try b.openArm(Ref.rowParam(0), 1);
    try b.close(.{ .value = &.{try b.callRow(callee, &.{Ref.rowParam(1)})} });
    const sw = try b.switchOn(Ref.rowParam(0), &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{});
    try b.endRow(.{ .value = &.{sw} });

    var out = ConstStore.init(testing.allocator);
    defer out.deinit();
    var emitter = try Emitter.init(testing.allocator, &out, &store, &types);
    defer emitter.deinit();
    const code = try emitter.site(root, 7);

    const backing = out.get(code).record;
    try testing.expectEqual(@as(u64, 7), out.get(backing[1]).scalar.u64);
    try testing.expectEqual(version, out.get(backing[2]).scalar.u32);
    const rows = out.get(out.get(backing[0]).record[1]).list.nodes;
    try testing.expectEqual(@as(usize, 2), rows.len);
    // The root is row 0; its nodes are the call in the switch's arm and then
    // the switch, and the dead `plus` is not among them.
    const root_row = out.get(rows[0]).record;
    const root_nodes = out.get(root_row[2]).list.nodes;
    try testing.expectEqual(@as(usize, 2), root_nodes.len);
    const first_op = out.get(out.get(root_nodes[0]).record[1]).tag;
    try testing.expectEqualStrings("Call", first_op.tag_name);
    try testing.expectEqual(@as(u32, 1), out.get(first_op.payloads[0]).scalar.u32);
    const second_op = out.get(out.get(root_nodes[1]).record[1]).tag;
    try testing.expectEqualStrings("Switch", second_op.tag_name);
    // The callee is row 1, and its node is a `Prim` named by owner and method.
    const callee_nodes = out.get(out.get(rows[1]).record[2]).list.nodes;
    const prim = out.get(out.get(callee_nodes[0]).record[1]).tag;
    try testing.expectEqualStrings("Prim", prim.tag_name);
    const names = out.get(prim.payloads[0]).record;
    try testing.expectEqualStrings("times", out.strBytes(out.get(names[0]).str));
    try testing.expectEqualStrings("Num.I64", out.strBytes(out.get(names[1]).str));
}

/// Where `join` first sits in `joins`.
fn positionOf(joins: []const RegionId, join: RegionId) ?usize {
    for (joins, 0..) |each, index| {
        if (each == join) return index;
    }
    return null;
}
