//! 128-bit content digests of nodes and regions (I4, plan 1.7).
//!
//! Merkle style: a node's digest comes from its op, payload, types,
//! immediates, its arguments' digests and its regions' digests; a region's
//! from its kind, parameter types, its end and its loops that can end the
//! row in `Return` (`live.exits`), read or not. A region parameter is named by
//! its position and by the region that binds it: the owner's op, payload,
//! types, immediates and arguments, and the region's place among the owner's
//! regions. So two loops over one start computing one thing have equal body
//! digests, and no digest reads where a node or a region is placed, which
//! the number stage moves (N5b). Equal digests are confirmed structurally
//! before anything merges, so a collision never merges two computations.

const std = @import("std");
const collections = @import("collections");
const ir = @import("ir.zig");
const live = @import("live.zig");
const types_mod = @import("types.zig");

const Allocator = std.mem.Allocator;
const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const TyId = ir.TyId;

/// A content digest.
pub const Digest = u128;

/// The digests of every node and region of a store.
pub const Digests = struct {
    nodes: []Digest,
    regions: []Digest,

    pub fn deinit(self: *Digests, gpa: Allocator) void {
        gpa.free(self.nodes);
        gpa.free(self.regions);
    }
};

const Hasher = struct {
    h: std.crypto.hash.sha2.Sha256 = .init(.{}),

    fn words(self: *Hasher, ws: []const u32) void {
        self.h.update(std.mem.sliceAsBytes(ws));
    }

    fn word(self: *Hasher, w: u32) void {
        self.words(&.{w});
    }

    fn digest(self: *Hasher, d: Digest) void {
        self.h.update(std.mem.asBytes(&d));
    }

    fn text(self: *Hasher, bytes: []const u8) void {
        self.word(@intCast(bytes.len));
        self.h.update(bytes);
    }

    // A type, by its id, or by its content where `ctx` reads content.
    fn ty(self: *Hasher, ctx: anytype, t: TyId) Allocator.Error!void {
        if (ctx.contentOf()) |c| self.digest(try c.ty(t)) else self.word(t.index());
    }

    fn final(self: *Hasher) Digest {
        var out: [32]u8 = undefined;
        self.h.final(&out);
        return std.mem.readInt(u128, out[0..16], .little);
    }
};

/// Compute the digest of every node and region. Nodes are visited in id
/// order, which puts every argument and every owned region's nodes first.
pub fn compute(gpa: Allocator, store: *const ir.Store) Allocator.Error!Digests {
    const nodes = try gpa.alloc(Digest, store.nodeCount());
    errdefer gpa.free(nodes);
    const regions = try gpa.alloc(Digest, store.regionCount());
    errdefer gpa.free(regions);
    const done = try gpa.alloc(bool, store.regionCount());
    defer gpa.free(done);
    @memset(done, false);
    var d: Digests = .{ .nodes = nodes, .regions = regions };
    const ctx: Filled = .{ .d = &d };
    for (0..store.nodeCount()) |i| {
        const nd = store.node(NodeId.of(@intCast(i)));
        for (store.regionSlice(nd.regions)) |r| {
            regions[r.index()] = try regionDigest(store, ctx, r);
            done[r.index()] = true;
        }
        nodes[i] = try nodeDigest(store, ctx, nd);
    }
    for (0..store.regionCount()) |i| {
        if (!done[i]) regions[i] = try regionDigest(store, ctx, RegionId.of(@intCast(i)));
    }
    return d;
}

/// The digest of region `r`, computed over only what its end reaches.
pub fn ofRegion(gpa: Allocator, store: *const ir.Store, r: RegionId) Allocator.Error!Digest {
    var memo: Memo = .{ .gpa = gpa, .store = store };
    defer memo.deinit();
    return memo.regionD(r);
}

/// What names a row that a `Call` or a `Closure` reads: the row's digest,
/// or its place in the component being finalized (N8g).
pub const RowNamer = struct {
    ctx: *const anyopaque,
    name: *const fn (ctx: *const anyopaque, row: ir.RowId) Digest,
};

/// The digest of row `row` (N8g): its parameter and result types and its
/// body, where every `Call` and `Closure` names its row by `names`. So a
/// row has one digest wherever it came from, and whatever its callees were
/// called.
pub fn ofRow(gpa: Allocator, store: *const ir.Store, row: ir.RowId, names: RowNamer) Allocator.Error!Digest {
    var memo: Memo = .{ .gpa = gpa, .store = store, .names = names };
    defer memo.deinit();
    return rowDigest(store, &memo, row);
}

/// The digest of row `row` as `ofRow` gives it, but with every type,
/// literal, primitive and name hashed by what `content` reads it to hold
/// instead of by its id. So equal rows in two stores with two type tables
/// have one digest (P1).
pub fn ofRowContent(gpa: Allocator, store: *const ir.Store, row: ir.RowId, names: RowNamer, content: *Content) Allocator.Error!Digest {
    var memo: Memo = .{ .gpa = gpa, .store = store, .names = names, .content = content };
    defer memo.deinit();
    return rowDigest(store, &memo, row);
}

/// The digest of every node of the rows a site reaches (V5a), for the
/// `inline` view: `rows` in the order the emitter numbers them, and for
/// each, its nodes in numbering order (`orders`). The result holds one
/// slice per row, with one digest per node.
///
/// A node's digest is its content digest: its op, immediates and types
/// hashed by content, so two sites with one normal form give each node one
/// digest, whatever their type ids and row ids were. A `Call` or `Closure`
/// that `inline` leaves names its row by the row's place in `rows` and the
/// content of the row's own body, so a change inside a recursive helper
/// changes its callers' digests.
pub fn ofSite(
    gpa: Allocator,
    store: *const ir.Store,
    types: *const types_mod.Types,
    rows: []const ir.RowId,
    orders: []const []const NodeId,
) Allocator.Error![]const []const Digest {
    std.debug.assert(rows.len == orders.len);
    var content: Content = .{ .gpa = gpa, .types = types };
    defer content.deinit();
    const names = try siteRowNames(gpa, store, rows, &content);
    defer gpa.free(names);
    const names_slice: []Digest = names;
    const named: RowNamer = .{ .ctx = @ptrCast(&names_slice), .name = ByPlace.name };
    var memo: Memo = .{ .gpa = gpa, .store = store, .names = named, .content = &content };
    defer memo.deinit();
    const out = try gpa.alloc([]const Digest, rows.len);
    var made: usize = 0;
    errdefer {
        for (out[0..made]) |each| gpa.free(each);
        gpa.free(out);
    }
    for (orders, out) |order, *slot| {
        const row_digests = try gpa.alloc(Digest, order.len);
        errdefer gpa.free(row_digests);
        for (order, row_digests) |n, *d| d.* = try memo.nodeD(n);
        slot.* = row_digests;
        made += 1;
    }
    return out;
}

/// Per row of the store, by index: the name a `Call` or `Closure` of it
/// has in the digests of a site whose rows are `rows`, in the order the
/// emitter numbers them (V5a). A row is named by its place in `rows` and the
/// content of its own body, in which every row it reaches is named by its
/// place alone, so a row that calls itself has a name. A row outside `rows`
/// is named 0. The caller frees the result.
pub fn siteRowNames(gpa: Allocator, store: *const ir.Store, rows: []const ir.RowId, content: *Content) Allocator.Error![]Digest {
    const place = try gpa.alloc(Digest, store.rows.items.len);
    defer gpa.free(place);
    @memset(place, 0);
    for (rows, 0..) |r, i| place[r.index()] = @as(Digest, i) | (@as(Digest, 1) << 64);
    const place_slice: []Digest = place;
    const shallow: RowNamer = .{ .ctx = @ptrCast(&place_slice), .name = ByPlace.name };
    const names = try gpa.alloc(Digest, store.rows.items.len);
    errdefer gpa.free(names);
    @memset(names, 0);
    for (rows) |r| {
        var h: Hasher = .{};
        h.digest(place[r.index()]);
        h.digest(try ofRowContent(gpa, store, r, shallow, content));
        names[r.index()] = h.final();
    }
    return names;
}

const ByPlace = struct {
    fn name(ctx: *const anyopaque, row: ir.RowId) Digest {
        const table: *const []Digest = @ptrCast(@alignCast(ctx));
        return table.*[row.index()];
    }
};

/// The digest of node `nd`'s own content, by what its ids name
/// (`ofRowContent`): its op, payload, types and immediates, and not its
/// arguments or regions. A `Call` or `Closure` names its row by `row_name`.
pub fn localContent(store: *const ir.Store, content: *Content, nd: ir.Node, row_name: ?Digest) Allocator.Error!Digest {
    var h: Hasher = .{};
    const ctx: ContentOnly = .{ .content = content };
    if (row_name) |d| {
        h.words(&.{ @backingInt(nd.op), std.math.maxInt(u32) });
        h.digest(d);
        h.word(nd.tys.len);
        for (store.tySlice(nd.tys)) |t| h.digest(try content.ty(t));
        h.word(nd.aux.len);
        h.words(store.wordSlice(nd.aux));
    } else try immediates(store, ctx, &h, nd);
    h.word(nd.args.len);
    h.word(nd.regions.len);
    return h.final();
}

/// The digest of literal `l`'s type and value.
pub fn litContent(store: *const ir.Store, content: *Content, l: ir.LitId) Allocator.Error!Digest {
    var h: Hasher = .{};
    try content.lit(&h, store, l);
    return h.final();
}

// Content read for `localContent`, which reads no child.
const ContentOnly = struct {
    content: *Content,

    fn contentOf(self: ContentOnly) ?*Content {
        return self.content;
    }
};

/// Free what `ofSite` returned.
pub fn freeSite(gpa: Allocator, digests: []const []const Digest) void {
    for (digests) |each| gpa.free(each);
    gpa.free(digests);
}

fn rowDigest(store: *const ir.Store, memo: *Memo, row: ir.RowId) Allocator.Error!Digest {
    const info = store.row(row);
    var h: Hasher = .{};
    h.word(info.params.len);
    for (store.tySlice(info.params)) |t| try h.ty(memo, t);
    try h.ty(memo, info.result);
    h.digest(try memo.regionD(info.body));
    return h.final();
}

/// The content of the types of one type table, each hashed once: its
/// structure, with names by their text.
pub const Content = struct {
    gpa: Allocator,
    types: *const types_mod.Types,
    tys: collections.DenseMapUnmanaged(TyId, Digest) = .empty,

    pub fn deinit(self: *Content) void {
        self.tys.deinit(self.gpa);
    }

    /// The digest of type `t`'s structure, with names by their text.
    pub fn ty(self: *Content, t: TyId) Allocator.Error!Digest {
        if (self.tys.get(t)) |d| return d;
        const types = self.types;
        const shape = types.get(t);
        var h: Hasher = .{};
        h.word(@backingInt(shape));
        switch (shape) {
            .bool_, .str, .dec => {},
            .int => |int| h.word(@backingInt(int)),
            .float => |float| h.word(@backingInt(float)),
            .record, .tag_union => |span| {
                const members = types.memberSlice(span);
                h.word(@intCast(members.len));
                for (members) |m| {
                    self.name(&h, m.name);
                    h.word(@intFromBool(m.optional));
                    const tys = types.tySlice(m.tys);
                    h.word(@intCast(tys.len));
                    for (tys) |mt| h.digest(try self.ty(mt));
                }
            },
            .tuple => |span| try self.list(&h, types.tySlice(span)),
            .list => |elem| h.digest(try self.ty(elem)),
            .nominal => |n| {
                self.name(&h, n.name);
                h.digest(try self.ty(n.backing));
            },
            .func => |f| {
                try self.list(&h, types.tySlice(f.params));
                h.digest(try self.ty(f.ret));
            },
            .opaque_ => |o| {
                self.name(&h, o.name);
                try self.list(&h, types.tySlice(o.args));
            },
            .recursive => |n| self.name(&h, n),
        }
        const d = h.final();
        try self.tys.put(self.gpa, t, d);
        return d;
    }

    fn list(self: *Content, h: *Hasher, tys: []const TyId) Allocator.Error!void {
        h.word(@intCast(tys.len));
        for (tys) |t| h.digest(try self.ty(t));
    }

    fn name(self: *Content, h: *Hasher, n: types_mod.NameId) void {
        h.text(self.types.nameText(n));
    }

    fn lit(self: *Content, h: *Hasher, store: *const ir.Store, l: ir.LitId) Allocator.Error!void {
        const entry = store.lit(l);
        h.digest(try self.ty(entry.ty));
        h.word(@backingInt(entry.value));
        switch (entry.value) {
            .int, .dec => |v| h.h.update(std.mem.asBytes(&v)),
            .float => |v| h.h.update(std.mem.asBytes(&v)),
            .bool_ => |v| h.word(@intFromBool(v)),
            .str, .bytes => |span| h.text(store.byteSlice(span)),
        }
    }
};

// Child digests read from `compute`'s arrays, filled before they are read.
const Filled = struct {
    d: *const Digests,

    fn nodeD(self: Filled, n: NodeId) Allocator.Error!Digest {
        return self.d.nodes[n.index()];
    }

    fn rowName(_: Filled, _: ir.RowId) ?Digest {
        return null;
    }

    fn contentOf(_: Filled) ?*Content {
        return null;
    }

    fn regionD(self: Filled, r: RegionId) Allocator.Error!Digest {
        return self.d.regions[r.index()];
    }
};

// Child digests computed on demand, each once.
const Memo = struct {
    gpa: Allocator,
    store: *const ir.Store,
    nodes: collections.DenseMapUnmanaged(NodeId, Digest) = .empty,
    regions: collections.DenseMapUnmanaged(RegionId, Digest) = .empty,
    /// Where set, a `Call` or `Closure` names its row through it, and
    /// otherwise by its id.
    names: ?RowNamer = null,
    /// Where set, types, literals, primitives and names are hashed by
    /// their content, and otherwise by their ids.
    content: ?*Content = null,

    fn deinit(self: *Memo) void {
        self.nodes.deinit(self.gpa);
        self.regions.deinit(self.gpa);
    }

    fn nodeD(self: *Memo, n: NodeId) Allocator.Error!Digest {
        if (self.nodes.get(n)) |v| return v;
        const v = try nodeDigest(self.store, self, self.store.node(n));
        try self.nodes.put(self.gpa, n, v);
        return v;
    }

    fn rowName(self: *Memo, row: ir.RowId) ?Digest {
        const names = self.names orelse return null;
        return names.name(names.ctx, row);
    }

    fn contentOf(self: *Memo) ?*Content {
        return self.content;
    }

    fn regionD(self: *Memo, r: RegionId) Allocator.Error!Digest {
        if (self.regions.get(r)) |v| return v;
        const v = try regionDigest(self.store, self, r);
        try self.regions.put(self.gpa, r, v);
        return v;
    }
};

fn refDigest(store: *const ir.Store, ctx: anytype, ref: ir.Ref) Allocator.Error!Digest {
    var h: Hasher = .{};
    switch (ref.kind) {
        .node => {
            h.word(0);
            h.digest(try ctx.nodeD(ref.nodeId()));
            h.word(ref.output);
        },
        .row_param => h.words(&.{ 1, ref.output }),
        .input => h.words(&.{ 3, ref.target }),
        .region_param => {
            h.words(&.{ 2, ref.output });
            h.digest(try binderDigest(store, ctx, ref.regionId()));
        },
    }
    return h.final();
}

// The region that binds a parameter, by its owner's op, payload, types,
// immediates and arguments, and its place among the owner's regions. The
// arguments stand outside the owner, so their digests are known first.
fn binderDigest(store: *const ir.Store, ctx: anytype, r: RegionId) Allocator.Error!Digest {
    const owner = store.node(store.region(r).owner);
    var h: Hasher = .{};
    try immediates(store, ctx, &h, owner);
    h.word(owner.args.len);
    for (store.refSlice(owner.args)) |a| h.digest(try refDigest(store, ctx, a));
    h.word(@intCast(std.mem.findScalar(RegionId, store.regionSlice(owner.regions), r).?));
    return h.final();
}

fn nodeDigest(store: *const ir.Store, ctx: anytype, nd: ir.Node) Allocator.Error!Digest {
    var h: Hasher = .{};
    const named: ?Digest = switch (nd.op) {
        .call, .closure => ctx.rowName(ir.RowId.of(nd.payload)),
        .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => null,
    };
    if (named) |d| {
        h.words(&.{ @backingInt(nd.op), std.math.maxInt(u32) });
        h.digest(d);
        h.word(nd.tys.len);
        for (store.tySlice(nd.tys)) |t| try h.ty(ctx, t);
        h.word(nd.aux.len);
        h.words(store.wordSlice(nd.aux));
    } else try immediates(store, ctx, &h, nd);
    h.word(nd.args.len);
    for (store.refSlice(nd.args)) |a| h.digest(try refDigest(store, ctx, a));
    h.word(nd.regions.len);
    for (store.regionSlice(nd.regions)) |r| h.digest(try ctx.regionD(r));
    return h.final();
}

// A node's op, payload, types and aux words. Where `ctx` reads content, a
// payload or an aux word that names a literal, a primitive, a name (a
// method, or the tag of a `Tag` or `Payload`) or a type is hashed by what it
// names.
fn immediates(store: *const ir.Store, ctx: anytype, h: *Hasher, nd: ir.Node) Allocator.Error!void {
    const content = ctx.contentOf() orelse {
        h.words(&.{ @backingInt(nd.op), nd.payload, nd.tys.len });
        for (store.tySlice(nd.tys)) |t| h.word(t.index());
        h.word(nd.aux.len);
        h.words(store.wordSlice(nd.aux));
        return;
    };
    h.word(@backingInt(nd.op));
    const aux = store.wordSlice(nd.aux);
    switch (nd.op) {
        .lit => try content.lit(h, store, ir.LitId.of(nd.payload)),
        .prim => {
            const name = store.primName(ir.PrimId.of(nd.payload));
            h.text(name.owner);
            h.text(name.method);
            if (name.role != .none) h.word(@backingInt(name.role));
        },
        // A tag is its name, and one store interns names in its own order.
        .derived, .tag, .payload => content.name(h, types_mod.NameId.of(nd.payload)),
        .call, .closure, .crash, .record, .tuple, .list, .wrap, .field, .index, .elem, .opt_field, .unwrap, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => h.word(nd.payload),
    }
    h.word(nd.tys.len);
    for (store.tySlice(nd.tys)) |t| h.digest(try content.ty(t));
    h.word(@intCast(aux.len));
    switch (nd.op) {
        .derived => h.digest(try content.ty(TyId.of(aux[0]))),
        .switch_ => for (aux) |l| try content.lit(h, store, ir.LitId.of(l)),
        .lit, .prim, .call, .closure, .crash, .record, .tuple, .list, .tag, .wrap, .field, .index, .payload, .elem, .opt_field, .unwrap, .and_, .or_, .for_range, .for_list, .loop, .lambda, .apply => h.words(aux),
    }
}

fn regionDigest(store: *const ir.Store, ctx: anytype, r: RegionId) Allocator.Error!Digest {
    const reg = store.region(r);
    var h: Hasher = .{};
    h.words(&.{ @backingInt(reg.kind), reg.params.len });
    for (store.tySlice(reg.params)) |t| try h.ty(ctx, t);
    h.words(&.{ @backingInt(reg.end.kind), reg.end.refs.len });
    switch (reg.end.kind) {
        // A join is named by its position among its switch's regions.
        .jump => {
            const join = RegionId.of(reg.end.target);
            const owner = store.region(join).owner;
            const siblings = store.regionSlice(store.node(owner).regions);
            h.word(@intCast(std.mem.findScalar(RegionId, siblings, join).?));
        },
        .branch => h.digest(try ctx.nodeD(NodeId.of(reg.end.target))),
        .open, .value, .return_, .continue_, .break_ => {},
    }
    for (store.refSlice(reg.end.refs)) |ref| h.digest(try refDigest(store, ctx, ref));
    // Its loops that can return, read or not, in the order they run, as the
    // structural comparison reads them (`equal.zig`).
    var loops = live.ExitLoops.of(store, r);
    while (loops.next()) |m| h.digest(try ctx.nodeD(m));
    return h.final();
}

const testing = std.testing;
const builder_mod = @import("builder.zig");

test "two arms that compute one value have one digest, wherever the node sits" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    _ = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const c = try b.call(.i64, .is_lt, &.{ ir.Ref.rowParam(0), ir.Ref.rowParam(1) });
    const outside = try b.call(.i64, .plus_wrap, &.{ ir.Ref.rowParam(0), ir.Ref.rowParam(1) });
    const arm0 = try b.openArm(c, 0);
    try b.close(.{ .value = &.{outside} });
    const arm1 = try b.openArm(c, 1);
    try b.close(.{ .value = &.{outside} });
    const arm2 = try b.openArm(c, 0);
    try b.close(.{ .value = &.{ir.Ref.rowParam(0)} });
    const sw = try b.switchOn(c, &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{});
    try b.endRow(.{ .value = &.{sw} });

    var d = try compute(testing.allocator, &store);
    defer d.deinit(testing.allocator);
    try testing.expectEqual(d.regions[arm0.index()], d.regions[arm1.index()]);
    try testing.expect(d.regions[arm0.index()] != d.regions[arm2.index()]);
}

test "two loops that compute the same thing in two arms have one body digest" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    _ = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const c = try b.call(.i64, .is_lt, &.{ ir.Ref.rowParam(0), ir.Ref.rowParam(1) });
    const zero = try b.litInt(i64_ty, 0);
    var bodies: [2]RegionId = undefined;
    var loops: [2]ir.Ref = undefined;
    var arms: [2]RegionId = undefined;
    for (&bodies, &loops, &arms, 0..) |*body, *loop, *arm, key| {
        arm.* = try b.openArm(c, @intCast(key));
        body.* = try b.openRegion(.loop_body, &.{ i64_ty, i64_ty });
        const next = try b.call(.i64, .plus_wrap, &.{ ir.Ref.regionParam(body.*, 1), ir.Ref.regionParam(body.*, 0) });
        try b.close(.{ .continue_ = &.{next} });
        loop.* = try b.loopOf(.for_range, &.{ zero, ir.Ref.rowParam(0), zero }, body.*, &.{i64_ty});
        try b.close(.{ .value = &.{loop.*} });
    }
    const sw = try b.switchOn(c, &arms, &.{}, &.{i64_ty}, &.{});
    try b.endRow(.{ .value = &.{sw} });

    var d = try compute(testing.allocator, &store);
    defer d.deinit(testing.allocator);
    try testing.expect(loops[0] != loops[1]);
    try testing.expectEqual(d.regions[bodies[0].index()], d.regions[bodies[1].index()]);
    try testing.expectEqual(d.nodes[loops[0].target], d.nodes[loops[1].target]);
}
