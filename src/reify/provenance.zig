//! Provenance (N10, I9): per node, the sources it came from, each with the
//! call path that reached it (normal-form 3.10).
//!
//! The table is not in the normal form: no rule, digest, numbering or view
//! reads it, so a translator cannot branch on it. The walk names a source by
//! a `SourceId` it maps to a module and a region; this module knows nothing
//! of either.
//!
//! | Event | Origins of the node |
//! |---|---|
//! | the walk builds it | the origin the walk is building under |
//! | hash-consing finds it again (N5a) | its origins and the new ones |
//! | a rebuild copies it | the old node's |
//! | a view inlines a call or a closure (V1, V2) | the callee node's, each reached through the call's or closure's |
//! | two rows merge (N8g) | its own, and those of every node of the dropped row the row comparison paired with it (`rows.zig` `mergeInto`) |

const std = @import("std");
const ir = @import("ir.zig");
const live_mod = @import("live.zig");
const number = @import("number.zig");

const Allocator = std.mem.Allocator;
const NodeId = ir.NodeId;

/// A source the walk names, in the order it named them.
pub const SourceId = enum(u32) {
    _,

    pub fn of(i: u32) SourceId {
        return @fromBackingInt(@intCast(i));
    }

    pub fn index(self: SourceId) u32 {
        return @backingInt(self);
    }
};

/// One origin of a node: a source, and the origin of the call it was
/// inlined through, or `none` where the source is in the row it stands in.
pub const Origin = struct {
    source: SourceId,
    via: OriginId,
};

/// An interned origin.
pub const OriginId = enum(u32) {
    none = std.math.maxInt(u32),
    _,

    pub fn of(i: u32) OriginId {
        return @fromBackingInt(@intCast(i));
    }

    pub fn index(self: OriginId) u32 {
        return @backingInt(self);
    }
};

/// The provenance of one store's nodes.
pub const Provenance = struct {
    origins: std.ArrayList(Origin) = .empty,
    interned: std.AutoHashMapUnmanaged(Origin, OriginId) = .empty,
    /// Per node, by id: its origins, sorted, in `pool`.
    sets: std.ArrayList(ir.Span) = .empty,
    pool: std.ArrayList(OriginId) = .empty,

    pub fn deinit(self: *Provenance, gpa: Allocator) void {
        self.origins.deinit(gpa);
        self.interned.deinit(gpa);
        self.sets.deinit(gpa);
        self.pool.deinit(gpa);
    }

    /// The origin `o`, interned.
    pub fn intern(self: *Provenance, gpa: Allocator, o: Origin) Allocator.Error!OriginId {
        const gop = try self.interned.getOrPut(gpa, o);
        if (!gop.found_existing) {
            gop.value_ptr.* = OriginId.of(@intCast(self.origins.items.len));
            try self.origins.append(gpa, o);
        }
        return gop.value_ptr.*;
    }

    pub fn origin(self: *const Provenance, id: OriginId) Origin {
        return self.origins.items[id.index()];
    }

    /// The origins of node `n`.
    pub fn of(self: *const Provenance, n: NodeId) []const OriginId {
        if (n.index() >= self.sets.items.len) return &.{};
        const span = self.sets.items[n.index()];
        return self.pool.items[span.start..][0..span.len];
    }

    /// Add `more` to the origins of node `n`.
    pub fn add(self: *Provenance, gpa: Allocator, n: NodeId, more: []const OriginId) Allocator.Error!void {
        if (more.len == 0) return;
        while (self.sets.items.len <= n.index()) try self.sets.append(gpa, ir.Span.empty);
        const have = self.of(n);
        var merged: std.ArrayList(OriginId) = .empty;
        defer merged.deinit(gpa);
        try merged.appendSlice(gpa, have);
        for (more) |m| if (std.mem.findScalar(OriginId, merged.items, m) == null) try merged.append(gpa, m);
        if (merged.items.len == have.len) return;
        std.mem.sort(OriginId, merged.items, {}, lessThan);
        const start: u32 = @intCast(self.pool.items.len);
        try self.pool.appendSlice(gpa, merged.items);
        self.sets.items[n.index()] = .{ .start = start, .len = @intCast(merged.items.len) };
    }

    /// `o` reached through the call whose origin is `call`: `o` with `call`
    /// at the end of its call path.
    pub fn through(self: *Provenance, gpa: Allocator, o: OriginId, call: OriginId) Allocator.Error!OriginId {
        if (o == OriginId.none) return call;
        const x = self.origin(o);
        return self.intern(gpa, .{ .source = x.source, .via = try self.through(gpa, x.via, call) });
    }

    fn lessThan(_: void, a: OriginId, b: OriginId) bool {
        return a.index() < b.index();
    }
};

/// The origins of every node a site's graph holds, in the order the emitter
/// writes the graph (`number.siteRows`, then each row's numbering): per row,
/// its nodes; per node, its origins; per origin, its sources, the node's
/// own first and then each call that reached it.
pub const Emitted = struct {
    rows: std.ArrayList(ir.Span) = .empty,
    nodes: std.ArrayList(ir.Span) = .empty,
    chains: std.ArrayList(ir.Span) = .empty,
    links: std.ArrayList(SourceId) = .empty,

    pub fn deinit(self: *Emitted, gpa: Allocator) void {
        self.rows.deinit(gpa);
        self.nodes.deinit(gpa);
        self.chains.deinit(gpa);
        self.links.deinit(gpa);
    }

    pub fn clone(self: *const Emitted, gpa: Allocator) Allocator.Error!Emitted {
        var out: Emitted = .{};
        errdefer out.deinit(gpa);
        try out.rows.appendSlice(gpa, self.rows.items);
        try out.nodes.appendSlice(gpa, self.nodes.items);
        try out.chains.appendSlice(gpa, self.chains.items);
        try out.links.appendSlice(gpa, self.links.items);
        return out;
    }

    /// The origins of node `node` of row `row`, each a span of `links`.
    pub fn of(self: *const Emitted, row: u32, node: u32) ?[]const ir.Span {
        if (row >= self.rows.items.len) return null;
        const r = self.rows.items[row];
        if (node >= r.len) return null;
        const n = self.nodes.items[r.start + node];
        return self.chains.items[n.start..][0..n.len];
    }
};

/// The origins of the graph the site of `root` emits.
pub fn emitted(gpa: Allocator, store: *const ir.Store, root: ir.RowId) Allocator.Error!Emitted {
    var returns = try live_mod.Returns.init(gpa, store);
    defer returns.deinit(gpa);
    var reached: ir.RowTable(number.Numbering) = .empty;
    defer {
        for (reached.values()) |*n| n.deinit(gpa);
        reached.deinit(gpa);
    }
    try number.siteRows(gpa, store, &returns, root, &reached);
    var out: Emitted = .{};
    errdefer out.deinit(gpa);
    const prov = &store.provenance;
    for (reached.values()) |numbering| {
        const row_start: u32 = @intCast(out.nodes.items.len);
        for (numbering.order.items) |n| {
            const node_start: u32 = @intCast(out.chains.items.len);
            for (prov.of(n)) |o| {
                const link_start: u32 = @intCast(out.links.items.len);
                var at = o;
                while (at != OriginId.none) : (at = prov.origin(at).via) try out.links.append(gpa, prov.origin(at).source);
                try out.chains.append(gpa, .{ .start = link_start, .len = @as(u32, @intCast(out.links.items.len)) - link_start });
            }
            try out.nodes.append(gpa, .{ .start = node_start, .len = @as(u32, @intCast(out.chains.items.len)) - node_start });
        }
        try out.rows.append(gpa, .{ .start = row_start, .len = @as(u32, @intCast(out.nodes.items.len)) - row_start });
    }
    return out;
}

/// A digest of every node's origins, as sources: two walks that built equal
/// rows and give equal digests here give equal origins to every node they
/// built, so one normal form's provenance serves both (P1).
pub fn digest(store: *const ir.Store) u128 {
    var h = std.crypto.hash.sha2.Sha256.init(.{});
    const prov = &store.provenance;
    const count: u32 = @intCast(store.nodeCount());
    h.update(std.mem.asBytes(&count));
    for (0..store.nodeCount()) |i| {
        const set = prov.of(NodeId.of(@intCast(i)));
        const len: u32 = @intCast(set.len);
        h.update(std.mem.asBytes(&len));
        for (set) |o| {
            var at = o;
            while (at != OriginId.none) : (at = prov.origin(at).via) h.update(std.mem.asBytes(&prov.origin(at).source));
            h.update(&.{0xff});
        }
    }
    var out: [32]u8 = undefined;
    h.final(&out);
    return std.mem.readInt(u128, out[0..16], .little);
}

const testing = std.testing;
const types_mod = @import("types.zig");
const builder_mod = @import("builder.zig");
const driver = @import("driver.zig");
const Ref = ir.Ref;
const RowId = ir.RowId;

const Fixture = struct {
    store: ir.Store,
    types: types_mod.Types,
    b: builder_mod.Builder,
    one: [1]OriginId = undefined,

    fn init(self: *Fixture) void {
        self.store = ir.Store.init(testing.allocator);
        self.types = types_mod.Types.init(testing.allocator);
        self.b = builder_mod.Builder.init(testing.allocator, &self.store, &self.types);
    }

    fn deinit(self: *Fixture) void {
        self.b.deinit();
        self.types.deinit();
        self.store.deinit();
    }

    // Build what follows as written at source `k`.
    fn at(self: *Fixture, k: u32) Allocator.Error!void {
        self.one[0] = try self.store.provenance.intern(testing.allocator, .{ .source = SourceId.of(k), .via = .none });
        self.b.origins = &self.one;
    }

    // The origins of the node `ref` reads, each as its source and then the
    // sources of the calls that reached it, innermost first: `s1<s4`.
    fn expectOrigins(self: *Fixture, ref: Ref, want: []const u8) (Allocator.Error || std.Io.Writer.Error || error{TestExpectedEqual})!void {
        var out: std.Io.Writer.Allocating = .init(testing.allocator);
        defer out.deinit();
        const prov = &self.store.provenance;
        for (prov.of(ref.nodeId()), 0..) |o, i| {
            if (i > 0) try out.writer.writeAll(" ");
            var at_o = o;
            var first = true;
            while (at_o != OriginId.none) : (at_o = prov.origin(at_o).via) {
                try out.writer.print("{s}s{d}", .{ if (first) "" else "<", prov.origin(at_o).source.index() });
                first = false;
            }
        }
        try testing.expectEqualStrings(want, out.written());
    }

    // The value the body of `row` ends in.
    fn result(self: *Fixture, row: RowId) Ref {
        const end = self.store.region(self.store.row(row).body).end;
        return self.store.refSlice(end.refs)[0];
    }

    // Argument `k` of the node `ref` reads.
    fn arg(self: *Fixture, ref: Ref, k: usize) Ref {
        return self.store.refSlice(self.store.node(ref.nodeId()).args)[k];
    }
};

test "N10: a node hash-consing found twice comes from both sources (N5a)" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const root = try f.b.beginRow(&.{i64_ty}, i64_ty);
    try f.at(1);
    const x = try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) });
    try f.at(2);
    const y = try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) });
    try f.at(3);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ x, y })} });
    _ = try driver.run(testing.allocator, &f.b, root, &.{});
    const sum = f.result(root);
    try f.expectOrigins(sum, "s3");
    try f.expectOrigins(f.arg(sum, 0), "s1 s2");
}

test "N10: a node every arm computes, merged before the switch, comes from every arm (N5c)" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const bool_ty = try f.types.boolTy();
    const root = try f.b.beginRow(&.{ bool_ty, i64_ty }, i64_ty);
    const arm0 = try f.b.openArm(Ref.rowParam(0), 0);
    try f.at(1);
    try f.b.close(.{ .value = &.{try f.b.call(.i64, .div_trunc, &.{ Ref.rowParam(1), Ref.rowParam(1) })} });
    const arm1 = try f.b.openArm(Ref.rowParam(0), 1);
    try f.at(2);
    const q = try f.b.call(.i64, .div_trunc, &.{ Ref.rowParam(1), Ref.rowParam(1) });
    try f.b.close(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ q, q })} });
    try f.at(3);
    const sw = try f.b.switchOn(Ref.rowParam(0), &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{});
    try f.b.endRow(.{ .value = &.{sw} });
    _ = try driver.run(testing.allocator, &f.b, root, &.{});
    // The division stands before the switch now, and the switch's first arm
    // reads it as its value.
    const out = f.result(root);
    const arm = f.store.regionSlice(f.store.node(out.nodeId()).regions)[0];
    const merged = f.store.refSlice(f.store.region(arm).end.refs)[0];
    try testing.expect(f.store.node(merged.nodeId()).region == f.store.row(root).body);
    try f.expectOrigins(merged, "s1 s2");
}

test "N10: two rows N8g merges give each node the origins of both" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    var helpers: [2]RowId = undefined;
    for (&helpers, [_]u32{ 1, 2 }) |*h, k| {
        h.* = try f.b.beginRow(&.{i64_ty}, i64_ty);
        try f.at(k);
        try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) })} });
    }
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    try f.at(3);
    const a = try f.b.callRow(helpers[0], &.{Ref.rowParam(0)});
    const b = try f.b.callRow(helpers[1], &.{Ref.rowParam(1)});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ a, b })} });
    _ = try driver.run(testing.allocator, &f.b, root, &.{});
    // Both calls name the row the two merged into, which V1 keeps.
    const call = f.arg(f.result(root), 0);
    const row = RowId.of(f.store.node(call.nodeId()).payload);
    try f.expectOrigins(f.result(row), "s1 s2");
}

test "N10: an inlined node comes from its own source, reached through the call (V1, V2)" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const sq = try f.b.beginRow(&.{i64_ty}, i64_ty);
    try f.at(1);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) })} });
    // `outer` calls `sq` from one place, and the root calls `outer` twice.
    const outer = try f.b.beginRow(&.{i64_ty}, i64_ty);
    try f.at(2);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ try f.b.callRow(sq, &.{Ref.rowParam(0)}), try f.b.litInt(i64_ty, 1) })} });
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    try f.at(3);
    const x = try f.b.callRow(outer, &.{Ref.rowParam(0)});
    try f.at(4);
    const y = try f.b.callRow(outer, &.{Ref.rowParam(1)});
    try f.at(5);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ x, y })} });
    _ = try driver.runTo(testing.allocator, &f.b, root, &.{}, .inline_);
    // `sq`'s node, inlined into `outer` (V1) and then into the root at the
    // call written at source 4 (V2).
    const second = f.arg(f.result(root), 1);
    try f.expectOrigins(second, "s2<s4");
    try f.expectOrigins(f.arg(second, 0), "s1<s2<s4");
}
