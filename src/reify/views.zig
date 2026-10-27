//! The views of a site (normal-form 5.1, plan 1.3 "views").
//!
//! | View | Step | Rows it keeps |
//! |---|---|---|
//! | `graph` | V1 | recursive components, rows whose body can end in `Return` (see below), rows called from two or more places, and rows a closure names; a row called from one place is inlined there, and the count is taken again until it stops changing |
//! | `inline` | V2 | recursive components, and rows whose body can end in `Return` (see below); every other call is inlined, and a `Closure` of a non-recursive row is a `Lambda` region in place |
//! | `outline` | V3 | the rows of `inline`, and a row per computation that repeats (normal-form 5.3, `outlineSelect`) |
//!
//! The driver runs V1 once every component is final, then simplifies the
//! rows it changed and finalizes the site's rows again (plan 3.5), because
//! inlining can merge two calls that were distinct only because their
//! arguments differed before simplification. V2 runs over the `graph` view
//! the same way, and V3 over the `inline` view, finalizing the rows again
//! after each pass without simplifying them.
//!
//! A row whose body can end in `Return`, in its own region or in any region
//! nested in it but a lambda body, is not inlined: inlining it would
//! turn each `Return` into a jump to the code after the call, which the
//! rebuild does not build yet (plan 4.1, M3). Its closures still become
//! lambdas, because a `Return` in a lambda body ends the lambda.

const std = @import("std");
const collections = @import("collections");
const ir = @import("ir.zig");
const live_mod = @import("live.zig");
const number = @import("number.zig");
const digest_mod = @import("digest.zig");
const types_mod = @import("types.zig");
const rows_mod = @import("rows.zig");
const rebuild = @import("rebuild.zig");

const Allocator = std.mem.Allocator;
const RowId = ir.RowId;
const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const Ref = ir.Ref;
const TyId = ir.TyId;

/// What a view inlines in one turn: the rows whose calls it inlines, the
/// rows whose closures become lambdas, and the rows that hold those calls
/// and closures.
pub const Turn = struct {
    inlined: []RowId,
    lambdas: []RowId,
    callers: []RowId,

    pub fn deinit(self: *Turn, gpa: Allocator) void {
        gpa.free(self.inlined);
        gpa.free(self.lambdas);
        gpa.free(self.callers);
    }
};

/// V1 over the site of `root`: every row but the root that is not
/// recursive, that one `Call` names and no `Closure` does, and whose body
/// ends in one value; and the rows that hold those calls, in the order the
/// site reaches them.
pub fn singleUse(gpa: Allocator, store: *const ir.Store, root: RowId) Allocator.Error!Turn {
    return turnOf(gpa, store, root, .graph);
}

/// V2 over the site of `root`: every row but the root that is not
/// recursive, that a `Call` names, and whose body ends in one value; every
/// row but the root that is not recursive and that a `Closure` names; and
/// the rows that hold those calls and closures, in the order the site
/// reaches them.
pub fn everyHelper(gpa: Allocator, store: *const ir.Store, root: RowId) Allocator.Error!Turn {
    return turnOf(gpa, store, root, .inline_);
}

const Kind = enum { graph, inline_ };

fn turnOf(gpa: Allocator, store: *const ir.Store, root: RowId, kind: Kind) Allocator.Error!Turn {
    var returns = try live_mod.Returns.init(gpa, store);
    defer returns.deinit(gpa);
    var reached: ir.RowTable(number.Numbering) = .empty;
    defer {
        for (reached.values()) |*n| n.deinit(gpa);
        reached.deinit(gpa);
    }
    try number.siteRows(gpa, store, &returns, root, &reached);
    const calls = try gpa.alloc(u32, store.rows.items.len);
    defer gpa.free(calls);
    @memset(calls, 0);
    const named = try gpa.alloc(bool, store.rows.items.len);
    defer gpa.free(named);
    @memset(named, false);
    var inlined: std.ArrayList(RowId) = .empty;
    defer inlined.deinit(gpa);
    var lambdas: std.ArrayList(RowId) = .empty;
    defer lambdas.deinit(gpa);
    for (reached.values()) |numbering| for (numbering.order.items) |n| {
        const nd = store.node(n);
        switch (nd.op) {
            .call => calls[nd.payload] +|= 1,
            .closure => named[nd.payload] = true,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => {},
        }
    };
    for (reached.keys()) |r| {
        const info = store.row(r);
        if (r == root or info.recursive) continue;
        const end = store.region(info.body).end;
        // A `Return` nested in a loop or an arm would end the caller if
        // the body were inlined, so such a row is not one value.
        const one_value = end.kind == .value and end.refs.len == 1 and !returns.regionHolds(store, info.body);
        switch (kind) {
            .graph => if (calls[r.index()] == 1 and !named[r.index()] and one_value) try inlined.append(gpa, r),
            .inline_ => {
                if (calls[r.index()] > 0 and one_value) try inlined.append(gpa, r);
                if (named[r.index()]) try lambdas.append(gpa, r);
            },
        }
    }
    var callers: std.ArrayList(RowId) = .empty;
    errdefer callers.deinit(gpa);
    for (reached.keys(), reached.values()) |r, numbering| for (numbering.order.items) |n| {
        const nd = store.node(n);
        const set = switch (nd.op) {
            .call => inlined.items,
            .closure => lambdas.items,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => continue,
        };
        if (std.mem.findScalar(RowId, set, RowId.of(nd.payload)) == null) continue;
        if (std.mem.findScalar(RowId, callers.items, r) == null) try callers.append(gpa, r);
        break;
    };
    const inlined_out = try inlined.toOwnedSlice(gpa);
    errdefer gpa.free(inlined_out);
    const lambdas_out = try lambdas.toOwnedSlice(gpa);
    errdefer gpa.free(lambdas_out);
    return .{ .inlined = inlined_out, .lambdas = lambdas_out, .callers = try callers.toOwnedSlice(gpa) };
}

// V3: the `outline` view (normal-form 5.3), a function of `inline` alone.
//
// | Step | Here |
// |---|---|
// | cones | `Analysis.forest`: a node's cone is its subtree in a forest whose parent of a node is the nearest node that every reader of it lies under, at a region the node's region is in or inside |
// | shapes | `Analysis.shapeOf`: per node, from its content and its children's shapes, with each stopping point a hole numbered by first occurrence |
// | candidates | `outlineSelect`: a shape at two or more places whose cone has at least K nodes |
// | selection | `outlineSelect`: (occurrences x (size - 1)) descending, then size descending, then shape ascending; a candidate keeps its occurrences that overlap none already taken |
// | rows | `driver.zig`: each chosen shape becomes a row over its holes (`rebuild.cone`), each occurrence a `Call` of it, and the passes repeat until none is chosen |
//
// A cone stops at row parameters, input slots, the parameters of a region
// no node of the cone owns, and nodes something outside the cone reads. A
// literal is part of every cone that reads it, as `to_tree` substitutes it
// at every read (normal-form 5.4), and a cone's size does not count it. A
// cone is a candidate only when outlining it keeps its meaning: its root has
// one output, no region in it ends by leaving it (a `Return` of the row, a
// `Continue` or `Break` of a loop outside it, a `Jump` to a join outside
// it), and, in a recursive row, it calls or names no row of that row's
// component, so outlining never joins a new row to a recursive component.

/// K: the least size of a cone `outline` makes a row of, literals not
/// counted. A constant of the language version (normal-form 5.3). It is at
/// least 3, so every pass removes nodes: c occurrences of a cone of size s
/// leave c calls and one row of s nodes, and (c - 1)(s - 1) > 1.
pub const outline_min_size: u32 = 4;

comptime {
    std.debug.assert(outline_min_size >= 3);
}

/// One pass of `outline`: the shapes it chose, in selection order, and per
/// row that holds an occurrence, what the row's copy replaces.
pub const Selection = struct {
    arena: std.heap.ArenaAllocator,
    shapes: []const Chosen = &.{},
    edits: []const Edit = &.{},

    /// One place a shape occurs at: its root, in its row, and the stopping
    /// points of its cone in hole order.
    pub const Occurrence = struct { row: RowId, root: NodeId, holes: []const Ref };

    /// A chosen shape. Its row is copied from `rep`, the first of its
    /// occurrences in site order.
    pub const Chosen = struct {
        rep: Occurrence,
        /// The nodes of `rep`'s cone, its root among them.
        nodes: std.AutoHashMapUnmanaged(NodeId, void),
        /// The literals `rep`'s cone reads from its root's region or a region
        /// around it, in site order.
        lits: []const NodeId,
        /// Per node of `rep`'s cone: the nodes of the other occurrences it
        /// stands for, whose origins its copy takes too (N10).
        also: collections.DenseMapUnmanaged(NodeId, []const NodeId),
        occurrences: []const Occurrence,
    };

    /// One row's occurrences: each root becomes a `Call` of shape `shape`'s
    /// row over its holes, and `skip` holds the nodes only those cones read.
    pub const Edit = struct {
        row: RowId,
        calls: []const Call,
        skip: []const NodeId,

        pub const Call = struct { root: NodeId, shape: u32, holes: []const Ref };
    };

    pub fn deinit(self: *Selection) void {
        self.arena.deinit();
    }
};

/// The size of a site: the rows it reaches, and their nodes, literals not
/// counted, which every pass of `outline` lowers.
pub const SiteSize = struct { nodes: u32 = 0, rows: u32 = 0 };

/// The size of the site of `root`.
pub fn siteSize(gpa: Allocator, store: *const ir.Store, root: RowId) Allocator.Error!SiteSize {
    var returns = try live_mod.Returns.init(gpa, store);
    defer returns.deinit(gpa);
    var reached: ir.RowTable(number.Numbering) = .empty;
    defer {
        for (reached.values()) |*n| n.deinit(gpa);
        reached.deinit(gpa);
    }
    try number.siteRows(gpa, store, &returns, root, &reached);
    var total: u32 = 0;
    for (reached.values()) |numbering| for (numbering.order.items) |n| {
        if (store.nodes.items(.op)[n.index()] != .lit) total += 1;
    };
    return .{ .nodes = total, .rows = @intCast(reached.count()) };
}

/// The shapes one pass of `outline` takes over the site of `root`, whose
/// rows are at `inline` or at an earlier pass, with K = `min_size`.
pub fn outlineSelect(gpa: Allocator, store: *const ir.Store, types: *const types_mod.Types, root: RowId, min_size: u32) Allocator.Error!Selection {
    var a: Analysis = .{ .gpa = gpa, .store = store, .content = .{ .gpa = gpa, .types = types }, .scratch = std.heap.ArenaAllocator.init(gpa) };
    defer a.deinit();
    try a.index(root);
    try a.forest();
    try a.euler();
    try a.bottomUp();

    var out: Selection = .{ .arena = std.heap.ArenaAllocator.init(gpa) };
    errdefer out.deinit();
    const arena = out.arena.allocator();

    // Candidates: groups of one shape, two or more strong, of size at least K.
    const Cand = struct { shape: u128, at: u32 };
    var cands: std.ArrayList(Cand) = .empty;
    defer cands.deinit(gpa);
    for (0..a.count()) |i| {
        if (a.valid[i] and a.size[i] >= min_size) try cands.append(gpa, .{ .shape = a.shape[i], .at = @intCast(i) });
    }
    std.mem.sort(Cand, cands.items, {}, struct {
        fn less(_: void, x: Cand, y: Cand) bool {
            return if (x.shape != y.shape) x.shape < y.shape else x.at < y.at;
        }
    }.less);
    const Group = struct { shape: u128, size: u32, start: u32, len: u32 };
    var groups: std.ArrayList(Group) = .empty;
    defer groups.deinit(gpa);
    var start: usize = 0;
    while (start < cands.items.len) {
        var end = start + 1;
        while (end < cands.items.len and cands.items[end].shape == cands.items[start].shape) end += 1;
        if (end - start >= 2) try groups.append(gpa, .{ .shape = cands.items[start].shape, .size = a.size[cands.items[start].at], .start = @intCast(start), .len = @intCast(end - start) });
        start = end;
    }
    std.mem.sort(Group, groups.items, {}, struct {
        fn less(_: void, x: Group, y: Group) bool {
            const gx = @as(u64, x.len) * (x.size - 1);
            const gy = @as(u64, y.len) * (y.size - 1);
            if (gx != gy) return gx > gy;
            if (x.size != y.size) return x.size > y.size;
            return x.shape < y.shape;
        }
    }.less);

    // Selection: an occurrence inside or around one already taken is dropped.
    var cover = try Fenwick.init(gpa, a.count());
    defer cover.deinit(gpa);
    var taken_roots = try Fenwick.init(gpa, a.count());
    defer taken_roots.deinit(gpa);
    var chosen: std.ArrayList(Selection.Chosen) = .empty;
    var kept: std.ArrayList(u32) = .empty;
    defer kept.deinit(gpa);
    var confirmed: std.ArrayList(u32) = .empty;
    defer confirmed.deinit(gpa);
    var pairs: std.ArrayList([2]NodeId) = .empty;
    defer pairs.deinit(gpa);
    var also: collections.DenseMapUnmanaged(NodeId, std.ArrayList(NodeId)) = .empty;
    defer {
        var lists = also.valueIterator();
        while (lists.next()) |l| l.deinit(gpa);
        also.deinit(gpa);
    }
    for (groups.items) |g| {
        kept.clearRetainingCapacity();
        for (cands.items[g.start..][0..g.len]) |c| {
            const i = c.at;
            if (cover.at(a.tin[i]) > 0) continue;
            if (taken_roots.sum(a.tin[i], a.tout[i]) > 0) continue;
            try kept.append(gpa, i);
        }
        if (kept.items.len < 2) continue;
        // Equal shapes are confirmed structurally, so a hash collision
        // never outlines two computations as one.
        const rep = kept.items[0];
        confirmed.clearRetainingCapacity();
        try confirmed.append(gpa, rep);
        {
            var lists = also.valueIterator();
            while (lists.next()) |l| l.deinit(gpa);
            also.clearRetainingCapacity();
        }
        for (kept.items[1..]) |other| {
            pairs.clearRetainingCapacity();
            if (!try a.sameCone(rep, other, &pairs)) continue;
            try confirmed.append(gpa, other);
            for (pairs.items) |pair| {
                const gop = try also.getOrPut(gpa, pair[0]);
                if (!gop.found_existing) gop.value_ptr.* = .empty;
                try gop.value_ptr.append(gpa, pair[1]);
            }
        }
        if (confirmed.items.len < 2) continue;
        for (confirmed.items) |i| {
            cover.addRange(a.tin[i], a.tout[i], 1);
            taken_roots.addAt(a.tin[i], 1);
        }
        const occurrences = try arena.alloc(Selection.Occurrence, confirmed.items.len);
        for (confirmed.items, occurrences) |i, *o| {
            o.* = a.occurrence(i);
            o.holes = try arena.dupe(Ref, o.holes);
        }
        var nodes: std.AutoHashMapUnmanaged(NodeId, void) = .empty;
        for (a.euler_order[a.tin[rep] .. a.tout[rep] + 1]) |m| try nodes.put(arena, a.nodes.items[m], {});
        var also_out: collections.DenseMapUnmanaged(NodeId, []const NodeId) = .empty;
        var it = also.iterator();
        while (it.next()) |e| try also_out.put(arena, e.key_ptr.*, try arena.dupe(NodeId, e.value_ptr.items));
        try chosen.append(arena, .{
            .rep = occurrences[0],
            .nodes = nodes,
            .lits = try a.coneLits(arena, rep),
            .also = also_out,
            .occurrences = occurrences,
        });
    }
    out.shapes = try chosen.toOwnedSlice(arena);

    // Per row, in site order: the calls, the nodes inside the cones, and
    // the literals only the cones read.
    var edits: std.ArrayList(Selection.Edit) = .empty;
    for (a.rows, 0..) |r, row_pos| {
        var calls: std.ArrayList(Selection.Edit.Call) = .empty;
        var skip: std.ArrayList(NodeId) = .empty;
        for (out.shapes, 0..) |shape, s| for (shape.occurrences) |o| {
            if (o.row != r) continue;
            try calls.append(arena, .{ .root = o.root, .shape = @intCast(s), .holes = o.holes });
            const i = a.local[o.root.index()];
            for (a.euler_order[a.tin[i] + 1 .. a.tout[i] + 1]) |m| try skip.append(arena, a.nodes.items[m]);
        };
        if (calls.items.len == 0) continue;
        for (a.row_start[row_pos]..a.row_start[row_pos + 1]) |l| {
            if (!a.is_lit[l]) continue;
            const read_outside = for (a.anchorsOf(@intCast(l))) |x| {
                if (x == Analysis.top or cover.at(a.tin[x]) == 0) break true;
            } else false;
            if (!read_outside) try skip.append(arena, a.nodes.items[l]);
        }
        try edits.append(arena, .{ .row = r, .calls = try calls.toOwnedSlice(arena), .skip = try skip.toOwnedSlice(arena) });
    }
    out.edits = try edits.toOwnedSlice(arena);
    return out;
}

// A Fenwick tree over positions 0..n, for the overlap test of selection.
const Fenwick = struct {
    tree: []i64,

    fn init(gpa: Allocator, n: usize) Allocator.Error!Fenwick {
        const tree = try gpa.alloc(i64, n + 2);
        @memset(tree, 0);
        return .{ .tree = tree };
    }

    fn deinit(self: *Fenwick, gpa: Allocator) void {
        gpa.free(self.tree);
    }

    // Add `v` at position `i`.
    fn addAt(self: *Fenwick, i: u32, v: i64) void {
        var k: usize = @as(usize, i) + 1;
        while (k < self.tree.len) : (k += k & (~k + 1)) self.tree[k] += v;
    }

    // The sum over positions 0..=i.
    fn prefix(self: *const Fenwick, i: u32) i64 {
        var k: usize = @as(usize, i) + 1;
        var total: i64 = 0;
        while (k > 0) : (k -= k & (~k + 1)) total += self.tree[k];
        return total;
    }

    // The sum over positions lo..=hi.
    fn sum(self: *const Fenwick, lo: u32, hi: u32) i64 {
        return self.prefix(hi) - (if (lo == 0) 0 else self.prefix(lo - 1));
    }

    // Add `v` at every position lo..=hi, read back with `at`.
    fn addRange(self: *Fenwick, lo: u32, hi: u32, v: i64) void {
        self.addAt(lo, v);
        self.addAt(hi + 1, -v);
    }

    // What `addRange` added at position `i`.
    fn at(self: *const Fenwick, i: u32) i64 {
        return self.prefix(i);
    }
};

// The cones, shapes and validity of every node of a site's rows. Nodes are
// indexed locally, row by row in site order, each row's in its numbering
// (N9), which is a post-order: a node's arguments and the nodes of the
// regions it owns come before it.
const Analysis = struct {
    gpa: Allocator,
    store: *const ir.Store,
    content: digest_mod.Content,
    scratch: std.heap.ArenaAllocator,
    rows: []const RowId = &.{},
    reached: ir.RowTable(number.Numbering) = .empty,
    /// Per row of the store: how `Call` and `Closure` name it (`digest.siteRowNames`).
    names: []digest_mod.Digest = &.{},
    /// Per row of the store: its component among the site's rows.
    comp: []u32 = &.{},
    nodes: std.ArrayList(NodeId) = .empty,
    /// Per node of the store: its local index, or `none`.
    local: []u32 = &.{},
    /// Per row position: where its nodes start; the last entry is the count.
    row_start: []u32 = &.{},
    row_of: []u32 = &.{},
    is_lit: []bool = &.{},
    /// Per node: what reads it, by local index, or `top` for the row's body.
    anchor_start: []u32 = &.{},
    anchor_list: []u32 = &.{},
    /// Per region: its nodes that nothing reads, which its end stands for.
    unread: collections.DenseMapUnmanaged(RegionId, std.ArrayList(u32)) = .empty,
    parent: []u32 = &.{},
    depth: []u32 = &.{},
    /// Binary lifting: `up[j * count + i]` is the 2^j-th ancestor of `i`.
    up: []u32 = &.{},
    levels: u32 = 0,
    child_start: []u32 = &.{},
    child_list: []u32 = &.{},
    tin: []u32 = &.{},
    tout: []u32 = &.{},
    /// Per Euler position: the node there.
    euler_order: []u32 = &.{},
    size: []u32 = &.{},
    valid: []bool = &.{},
    shape: []u128 = &.{},
    holes: [][]const Ref = &.{},
    // Scratch of `shapeOf`.
    points: std.AutoHashMapUnmanaged(u64, u32) = .empty,
    hole_buf: std.ArrayList(Ref) = .empty,
    frames: std.ArrayList(Frame) = .empty,

    const none: u32 = std.math.maxInt(u32);
    const top: u32 = std.math.maxInt(u32) - 1;
    /// The output a join is named by where it stands among a cone's points.
    const join_output: u30 = std.math.maxInt(u30);

    const Frame = struct { refs: []const Ref, pos: u32 };

    fn deinit(self: *Analysis) void {
        const gpa = self.gpa;
        for (self.reached.values()) |*n| n.deinit(gpa);
        self.reached.deinit(gpa);
        self.content.deinit();
        gpa.free(self.names);
        self.nodes.deinit(gpa);
        var lists = self.unread.valueIterator();
        while (lists.next()) |l| l.deinit(gpa);
        self.unread.deinit(gpa);
        self.points.deinit(gpa);
        self.hole_buf.deinit(gpa);
        self.frames.deinit(gpa);
        self.scratch.deinit();
    }

    fn count(self: *const Analysis) u32 {
        return @intCast(self.nodes.items.len);
    }

    fn node(self: *const Analysis, i: u32) ir.Node {
        return self.store.node(self.nodes.items[i]);
    }

    fn anchorsOf(self: *const Analysis, i: u32) []const u32 {
        return self.anchor_list[self.anchor_start[i]..self.anchor_start[i + 1]];
    }

    fn childrenOf(self: *const Analysis, i: u32) []const u32 {
        return self.child_list[self.child_start[i]..self.child_start[i + 1]];
    }

    fn regionDepth(self: *const Analysis, i: u32) u32 {
        return self.store.region(self.node(i).region).depth;
    }

    fn localOf(self: *const Analysis, n: NodeId) u32 {
        const l = self.local[n.index()];
        std.debug.assert(l != none);
        return l;
    }

    // The site's rows, their components and names, and the local index of
    // every node they reach, with what reads each.
    fn index(self: *Analysis, root: RowId) Allocator.Error!void {
        const gpa = self.gpa;
        const arena = self.scratch.allocator();
        const store = self.store;
        {
            var returns = try live_mod.Returns.init(gpa, store);
            defer returns.deinit(gpa);
            try number.siteRows(gpa, store, &returns, root, &self.reached);
        }
        self.rows = self.reached.keys();
        self.names = try digest_mod.siteRowNames(gpa, store, self.rows, &self.content);
        self.comp = try arena.alloc(u32, store.rows.items.len);
        @memset(self.comp, none);
        {
            const g = try rows_mod.graph(gpa, store, .references);
            defer rows_mod.freeGraph(gpa, g);
            const comps = try rows_mod.components(gpa, g, self.rows);
            defer rows_mod.freeComponents(gpa, comps);
            for (comps, 0..) |c, ci| for (c) |r| {
                self.comp[r.index()] = @intCast(ci);
            };
        }
        self.local = try arena.alloc(u32, store.nodeCount());
        @memset(self.local, none);
        self.row_start = try arena.alloc(u32, self.rows.len + 1);
        for (self.reached.values(), 0..) |numbering, ri| {
            self.row_start[ri] = self.count();
            for (numbering.order.items) |n| {
                self.local[n.index()] = self.count();
                try self.nodes.append(gpa, n);
            }
        }
        self.row_start[self.rows.len] = self.count();
        const total = self.count();
        self.row_of = try arena.alloc(u32, total);
        self.is_lit = try arena.alloc(bool, total);
        for (0..self.rows.len) |ri| for (self.row_start[ri]..self.row_start[ri + 1]) |i| {
            self.row_of[i] = @intCast(ri);
            self.is_lit[i] = self.node(@intCast(i)).op == .lit;
        };

        // What reads each node: a node, or the owner of a region whose end reads it.
        const Edge = struct { to: u32, from: u32 };
        var edges: std.ArrayList(Edge) = .empty;
        defer edges.deinit(gpa);
        for (0..total) |idx| {
            const i: u32 = @intCast(idx);
            const nd = self.node(i);
            for (store.refSlice(nd.args)) |x| if (x.kind == .node) try edges.append(gpa, .{ .to = self.localOf(x.nodeId()), .from = i });
            for (store.regionSlice(nd.regions)) |r| try self.endEdges(&edges, r, i);
        }
        for (self.rows) |r| try self.endEdges(&edges, store.row(r).body, top);
        const counts = try arena.alloc(u32, total + 1);
        @memset(counts, 0);
        for (edges.items) |e| counts[e.to] += 1;
        // A node nothing reads stands for its region's end.
        for (0..total) |idx| {
            if (counts[idx] != 0) continue;
            const region = self.node(@intCast(idx)).region;
            const owner = store.region(region).owner;
            try edges.append(gpa, .{ .to = @intCast(idx), .from = if (owner == NodeId.none) top else self.localOf(owner) });
            counts[idx] = 1;
            const gop = try self.unread.getOrPut(gpa, region);
            if (!gop.found_existing) gop.value_ptr.* = .empty;
            try gop.value_ptr.append(gpa, @intCast(idx));
        }
        self.anchor_start = try arena.alloc(u32, total + 1);
        var at: u32 = 0;
        for (0..total) |idx| {
            self.anchor_start[idx] = at;
            at += counts[idx];
        }
        self.anchor_start[total] = at;
        self.anchor_list = try arena.alloc(u32, at);
        const fill = try gpa.dupe(u32, self.anchor_start[0..total]);
        defer gpa.free(fill);
        for (edges.items) |e| {
            self.anchor_list[fill[e.to]] = e.from;
            fill[e.to] += 1;
        }
    }

    fn endEdges(self: *Analysis, edges: anytype, r: RegionId, from: u32) Allocator.Error!void {
        const end = self.store.region(r).end;
        for (self.store.refSlice(end.refs)) |x| if (x.kind == .node) try edges.append(self.gpa, .{ .to = self.localOf(x.nodeId()), .from = from });
        if (end.kind == .branch) try edges.append(self.gpa, .{ .to = self.localOf(NodeId.of(end.target)), .from = from });
    }

    // The forest of cones, from the readers down: a node's parent is the
    // nearest common ancestor of what reads it, raised until that node's
    // region holds the node's own region. A node read by a row's end, a
    // literal, and a node no such ancestor exists for, are roots.
    fn forest(self: *Analysis) Allocator.Error!void {
        const arena = self.scratch.allocator();
        const total = self.count();
        self.parent = try arena.alloc(u32, total);
        self.depth = try arena.alloc(u32, total);
        self.levels = 1;
        while ((@as(u64, 1) << @intCast(self.levels)) <= total) self.levels += 1;
        self.up = try arena.alloc(u32, @as(usize, self.levels) * total);
        @memset(self.up, none);
        var idx: usize = total;
        while (idx > 0) {
            idx -= 1;
            const i: u32 = @intCast(idx);
            const p = if (self.is_lit[i]) none else self.parentOf(i);
            self.parent[i] = p;
            self.depth[i] = if (p == none) 0 else self.depth[p] + 1;
            self.up[i] = p;
            for (1..self.levels) |j| {
                const mid = self.up[(j - 1) * total + i];
                self.up[j * total + i] = if (mid == none) none else self.up[(j - 1) * total + mid];
            }
        }
    }

    fn parentOf(self: *const Analysis, i: u32) u32 {
        var l: u32 = none;
        for (self.anchorsOf(i), 0..) |x, k| {
            if (x == top) return none;
            std.debug.assert(x > i and !self.is_lit[x]);
            l = if (k == 0) x else self.lca(l, x);
            if (l == none) return none;
        }
        // The first ancestor whose region holds the node's region.
        const want = self.regionDepth(i);
        if (self.regionDepth(l) <= want) return l;
        const total = self.count();
        var j: usize = self.levels;
        while (j > 0) {
            j -= 1;
            const next = self.up[j * total + l];
            if (next != none and self.regionDepth(next) > want) l = next;
        }
        return self.parent[l];
    }

    fn lca(self: *const Analysis, x_in: u32, y_in: u32) u32 {
        const total = self.count();
        var x = x_in;
        var y = y_in;
        if (self.depth[x] < self.depth[y]) std.mem.swap(u32, &x, &y);
        var diff = self.depth[x] - self.depth[y];
        var j: usize = 0;
        while (diff > 0) : (j += 1) {
            if (diff & 1 == 1) x = self.up[j * total + x];
            diff >>= 1;
        }
        if (x == y) return x;
        j = self.levels;
        while (j > 0) {
            j -= 1;
            const ux = self.up[j * total + x];
            const uy = self.up[j * total + y];
            if (ux != uy) {
                x = ux;
                y = uy;
            }
        }
        // Roots of two trees have no common ancestor.
        return if (self.parent[x] == self.parent[y]) self.parent[x] else none;
    }

    // Children in local order, and each subtree's span of Euler positions.
    fn euler(self: *Analysis) Allocator.Error!void {
        const arena = self.scratch.allocator();
        const total = self.count();
        const counts = try arena.alloc(u32, total + 1);
        @memset(counts, 0);
        for (self.parent) |p| if (p != none) {
            counts[p] += 1;
        };
        self.child_start = try arena.alloc(u32, total + 1);
        var at: u32 = 0;
        for (0..total) |i| {
            self.child_start[i] = at;
            at += counts[i];
        }
        self.child_start[total] = at;
        self.child_list = try arena.alloc(u32, at);
        const fill = try self.gpa.dupe(u32, self.child_start[0..total]);
        defer self.gpa.free(fill);
        for (self.parent, 0..) |p, i| if (p != none) {
            self.child_list[fill[p]] = @intCast(i);
            fill[p] += 1;
        };
        self.tin = try arena.alloc(u32, total);
        self.tout = try arena.alloc(u32, total);
        self.euler_order = try arena.alloc(u32, total);
        var clock: u32 = 0;
        var stack: std.ArrayList(struct { node: u32, next: u32 }) = .empty;
        defer stack.deinit(self.gpa);
        for (0..total) |r| {
            if (self.parent[r] != none) continue;
            try stack.append(self.gpa, .{ .node = @intCast(r), .next = 0 });
            self.tin[r] = clock;
            self.euler_order[clock] = @intCast(r);
            clock += 1;
            while (stack.items.len > 0) {
                const frame = &stack.items[stack.items.len - 1];
                const kids = self.childrenOf(frame.node);
                if (frame.next == kids.len) {
                    self.tout[frame.node] = clock - 1;
                    _ = stack.pop();
                    continue;
                }
                const c = kids[frame.next];
                frame.next += 1;
                self.tin[c] = clock;
                self.euler_order[clock] = c;
                clock += 1;
                try stack.append(self.gpa, .{ .node = c, .next = 0 });
            }
        }
        std.debug.assert(clock == total);
    }

    // Sizes, validity and shapes, children before parents.
    fn bottomUp(self: *Analysis) Allocator.Error!void {
        const arena = self.scratch.allocator();
        const store = self.store;
        const total = self.count();
        self.size = try arena.alloc(u32, total);
        self.valid = try arena.alloc(bool, total);
        self.shape = try arena.alloc(u128, total);
        self.holes = try arena.alloc([]const Ref, total);
        // Per node: the least depth a region end in its cone leaves to, and
        // whether its cone names a row of its own row's recursive component.
        const exit_depth = try self.gpa.alloc(i64, total);
        defer self.gpa.free(exit_depth);
        const names_comp = try self.gpa.alloc(bool, total);
        defer self.gpa.free(names_comp);
        for (0..total) |idx| {
            const i: u32 = @intCast(idx);
            const nd = self.node(i);
            var size: u32 = if (self.is_lit[i]) 0 else 1;
            var least: i64 = std.math.maxInt(i64);
            const row = self.rows[self.row_of[i]];
            var named = switch (nd.op) {
                .call, .closure => store.row(row).recursive and self.comp[nd.payload] == self.comp[row.index()],
                .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => false,
            };
            for (store.regionSlice(nd.regions)) |r| least = @min(least, self.exitOf(r));
            for (self.childrenOf(i)) |c| {
                std.debug.assert(c < i);
                size += self.size[c];
                least = @min(least, exit_depth[c]);
                named = named or names_comp[c];
            }
            self.size[i] = size;
            exit_depth[i] = least;
            names_comp[i] = named;
            self.valid[i] = !self.is_lit[i] and nd.tys.len == 1 and least >= self.depth[i] and !named;
            try self.shapeOf(i);
        }
    }

    // The depth of the node a region's end leaves to, or -1 for the row:
    // the lambda or the row a `Return` leaves, the loop a `Continue` or a
    // `Break` goes to, the switch whose join a `Jump` reaches. An end that
    // stays in its region leaves to nothing.
    fn exitOf(self: *const Analysis, r: RegionId) i64 {
        const store = self.store;
        const end = store.region(r).end;
        const target: NodeId = switch (end.kind) {
            .value, .branch, .open => return std.math.maxInt(i64),
            .jump => store.region(RegionId.of(end.target)).owner,
            .return_, .continue_, .break_ => blk: {
                const want: ir.RegionKind = if (end.kind == .return_) .lambda_body else .loop_body;
                var at = r;
                while (true) {
                    const reg = store.region(at);
                    if (reg.kind == want) break :blk reg.owner;
                    if (reg.kind == .row_body or reg.kind == .lambda_body) {
                        // Only a `Return` leaves a row; a loop's ends stay in its lambda.
                        std.debug.assert(end.kind == .return_);
                        return -1;
                    }
                    at = reg.parent;
                }
            },
        };
        return self.depth[self.localOf(target)];
    }

    fn occurrence(self: *const Analysis, i: u32) Selection.Occurrence {
        return .{ .row = self.rows[self.row_of[i]], .root = self.nodes.items[i], .holes = self.holes[i] };
    }

    // Whether `i` is a node of the cone of `root`.
    fn inCone(self: *const Analysis, root: u32, i: u32) bool {
        return !self.is_lit[i] and self.tin[root] <= self.tin[i] and self.tin[i] <= self.tout[root];
    }

    // The literals the cone of `i` reads from `i`'s region or a region
    // around it, which a copy of the cone builds in its body.
    fn coneLits(self: *const Analysis, arena: Allocator, i: u32) Allocator.Error![]const NodeId {
        const store = self.store;
        const home = self.regionDepth(i);
        var found: std.ArrayList(u32) = .empty;
        defer found.deinit(self.gpa);
        for (self.euler_order[self.tin[i] .. self.tout[i] + 1]) |m| {
            const nd = self.node(m);
            for (store.refSlice(nd.args)) |x| try self.noteLit(&found, x, home);
            for (store.regionSlice(nd.regions)) |r| for (store.refSlice(store.region(r).end.refs)) |x| try self.noteLit(&found, x, home);
        }
        std.mem.sort(u32, found.items, {}, std.sort.asc(u32));
        const out = try arena.alloc(NodeId, found.items.len);
        for (found.items, out) |l, *o| o.* = self.nodes.items[l];
        return out;
    }

    fn noteLit(self: *const Analysis, found: *std.ArrayList(u32), x: Ref, home: u32) Allocator.Error!void {
        if (x.kind != .node) return;
        const l = self.localOf(x.nodeId());
        if (!self.is_lit[l] or self.regionDepth(l) > home) return;
        if (std.mem.findScalar(u32, found.items, l) == null) try found.append(self.gpa, l);
    }

    const Tag = enum(u32) { lit, ref, child, param, join, hole };

    // The shape of the cone of `i` and its holes. Every value the cone reads
    // is one of its points, numbered in the order the walk first meets it:
    // the node's arguments, then per region its end and the nodes nothing
    // reads, and at the first meeting of a child, the child's holes in their
    // order. A child is named by its own shape, so the shape of `i` reads
    // each node of its cone once.
    fn shapeOf(self: *Analysis, i: u32) Allocator.Error!void {
        const store = self.store;
        const nd = self.node(i);
        self.points.clearRetainingCapacity();
        self.hole_buf.clearRetainingCapacity();
        var h = Sha256.init(.{});
        const name: ?digest_mod.Digest = switch (nd.op) {
            .call, .closure => self.names[nd.payload],
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => null,
        };
        putDigest(&h, try digest_mod.localContent(store, &self.content, nd, name));
        for (store.refSlice(nd.args)) |x| try self.token(&h, i, x);
        for (store.regionSlice(nd.regions)) |r| {
            const reg = store.region(r);
            putWords(&h, &.{ @backingInt(reg.kind), reg.params.len });
            for (store.tySlice(reg.params)) |t| putDigest(&h, try self.content.ty(t));
            putWords(&h, &.{ @backingInt(reg.end.kind), reg.end.refs.len });
            switch (reg.end.kind) {
                .jump => try self.token(&h, i, joinRef(RegionId.of(reg.end.target))),
                .branch => try self.token(&h, i, Ref.of(NodeId.of(reg.end.target))),
                .open, .value, .return_, .continue_, .break_ => {},
            }
            for (store.refSlice(reg.end.refs)) |x| try self.token(&h, i, x);
            if (self.unread.get(r)) |list| {
                putWords(&h, &.{@intCast(list.items.len)});
                for (list.items) |m| try self.token(&h, i, Ref.of(self.nodes.items[m]));
            }
        }
        var out: [32]u8 = undefined;
        h.final(&out);
        self.shape[i] = std.mem.readInt(u128, out[0..16], .little);
        self.holes[i] = try self.scratch.allocator().dupe(Ref, self.hole_buf.items);
    }

    fn joinRef(j: RegionId) Ref {
        return .{ .kind = .region_param, .output = join_output, .target = j.index() };
    }

    // One point read by the cone of `at`, and the holes of every child it
    // meets for the first time, depth first.
    fn token(self: *Analysis, h: *Sha256, at: u32, x: Ref) Allocator.Error!void {
        self.frames.clearRetainingCapacity();
        try self.emit(h, at, x);
        while (self.frames.items.len > 0) {
            const frame = &self.frames.items[self.frames.items.len - 1];
            if (frame.pos == frame.refs.len) {
                _ = self.frames.pop();
                continue;
            }
            const next = frame.refs[frame.pos];
            frame.pos += 1;
            try self.emit(h, at, next);
        }
    }

    fn emit(self: *Analysis, h: *Sha256, at: u32, x: Ref) Allocator.Error!void {
        const store = self.store;
        const Class = enum { child, param, join, hole };
        var key = rebuild.refKey(x);
        const class: Class = switch (x.kind) {
            .node => blk: {
                const m = self.localOf(x.nodeId());
                if (self.is_lit[m]) {
                    putWords(h, &.{ @intFromEnum(Tag.lit), x.output });
                    putDigest(h, try digest_mod.litContent(store, &self.content, ir.LitId.of(self.node(m).payload)));
                    return;
                }
                if (self.parent[m] == at) {
                    key = rebuild.refKey(Ref.of(x.nodeId()));
                    break :blk .child;
                }
                break :blk .hole;
            },
            .row_param, .input => .hole,
            .region_param => blk: {
                const owner = store.region(x.regionId()).owner;
                const bound = owner != NodeId.none and self.localOf(owner) == at;
                if (x.output == join_output) break :blk if (bound) .join else .hole;
                break :blk if (bound) .param else .hole;
            },
        };
        // Only a node's output is part of the shape: the index of a row
        // parameter, a slot or a region parameter outside the cone is the
        // hole's own, and a region parameter inside it is named by its place.
        const output: u32 = if (x.kind == .node) x.output else 0;
        if (self.points.get(key)) |seen| {
            putWords(h, &.{ @intFromEnum(Tag.ref), seen, output });
            return;
        }
        try self.points.put(self.gpa, key, self.points.count());
        switch (class) {
            .child => {
                const m = self.localOf(x.nodeId());
                putWords(h, &.{ @intFromEnum(Tag.child), x.output });
                putDigest(h, self.shape[m]);
                try self.frames.append(self.gpa, .{ .refs = self.holes[m], .pos = 0 });
            },
            .param, .join => {
                const r = x.regionId();
                const owner = store.node(store.region(r).owner);
                const pos = std.mem.findScalar(RegionId, store.regionSlice(owner.regions), r).?;
                putWords(h, &.{ @intFromEnum(if (class == .param) Tag.param else Tag.join), @intCast(pos), x.output });
                if (class == .param) putDigest(h, try self.content.ty(store.tySlice(store.region(r).params)[x.output]));
            },
            .hole => {
                putWords(h, &.{ @intFromEnum(Tag.hole), output });
                if (!(x.kind == .region_param and x.output == join_output)) {
                    putDigest(h, try self.content.ty(store.refTy(self.rows[self.row_of[at]], x)));
                }
                try self.hole_buf.append(self.gpa, x);
            },
        }
    }

    // Whether the cones of `a` and `b` are one computation: a walk of both
    // in step that pairs their nodes, the regions they own and their holes
    // one to one. `pairs` receives each pair of nodes, literals included.
    fn sameCone(self: *Analysis, a: u32, b: u32, pairs: *std.ArrayList([2]NodeId)) Allocator.Error!bool {
        const gpa = self.gpa;
        var w: Pairing = .{ .an = self, .a = a, .b = b, .pairs = pairs };
        defer w.deinit(gpa);
        try w.nodes.put(gpa, self.nodes.items[a], self.nodes.items[b]);
        try w.work.append(gpa, .{ self.nodes.items[a], self.nodes.items[b] });
        try pairs.append(gpa, .{ self.nodes.items[a], self.nodes.items[b] });
        while (w.work.pop()) |pair| {
            if (!try w.compare(pair[0], pair[1])) return false;
        }
        // The holes pair in hole order, so a call passes the occurrence's
        // holes where the row reads the representative's.
        const ha = self.holes[a];
        const hb = self.holes[b];
        if (ha.len != hb.len) return false;
        for (ha, hb) |x, y| if (w.holes_ab.get(rebuild.refKey(x)) != rebuild.refKey(y)) return false;
        return true;
    }
};

// The walk of `Analysis.sameCone`.
const Pairing = struct {
    an: *const Analysis,
    a: u32,
    b: u32,
    pairs: *std.ArrayList([2]NodeId),
    nodes: std.AutoHashMapUnmanaged(NodeId, NodeId) = .empty,
    regions: std.AutoHashMapUnmanaged(RegionId, RegionId) = .empty,
    holes_ab: std.AutoHashMapUnmanaged(u64, u64) = .empty,
    holes_ba: std.AutoHashMapUnmanaged(u64, u64) = .empty,
    work: std.ArrayList([2]NodeId) = .empty,

    fn deinit(self: *Pairing, allocator: Allocator) void {
        self.nodes.deinit(allocator);
        self.regions.deinit(allocator);
        self.holes_ab.deinit(allocator);
        self.holes_ba.deinit(allocator);
        self.work.deinit(allocator);
    }

    fn gpa(self: *const Pairing) Allocator {
        return self.an.gpa;
    }

    fn compare(self: *Pairing, x: NodeId, y: NodeId) Allocator.Error!bool {
        const store = self.an.store;
        const nx = store.node(x);
        const ny = store.node(y);
        if (nx.op != ny.op or nx.payload != ny.payload) return false;
        if (!std.mem.eql(TyId, store.tySlice(nx.tys), store.tySlice(ny.tys))) return false;
        if (!std.mem.eql(u32, store.wordSlice(nx.aux), store.wordSlice(ny.aux))) return false;
        const ax = store.refSlice(nx.args);
        const ay = store.refSlice(ny.args);
        if (ax.len != ay.len) return false;
        const rx = store.regionSlice(nx.regions);
        const ry = store.regionSlice(ny.regions);
        if (rx.len != ry.len) return false;
        for (rx, ry) |p, q| try self.regions.put(self.gpa(), p, q);
        for (ax, ay) |p, q| if (!try self.ref(p, q)) return false;
        for (rx, ry) |p, q| {
            const gp = store.region(p);
            const gq = store.region(q);
            if (gp.kind != gq.kind or gp.end.kind != gq.end.kind) return false;
            if (!std.mem.eql(TyId, store.tySlice(gp.params), store.tySlice(gq.params))) return false;
            switch (gp.end.kind) {
                .jump => if (!try self.ref(Analysis.joinRef(RegionId.of(gp.end.target)), Analysis.joinRef(RegionId.of(gq.end.target)))) return false,
                .branch => if (!try self.ref(Ref.of(NodeId.of(gp.end.target)), Ref.of(NodeId.of(gq.end.target)))) return false,
                .open, .value, .return_, .continue_, .break_ => {},
            }
            const ep = store.refSlice(gp.end.refs);
            const eq = store.refSlice(gq.end.refs);
            if (ep.len != eq.len) return false;
            for (ep, eq) |s, t| if (!try self.ref(s, t)) return false;
            const up: []const u32 = if (self.an.unread.get(p)) |l| l.items else &.{};
            const uq: []const u32 = if (self.an.unread.get(q)) |l| l.items else &.{};
            if (up.len != uq.len) return false;
            for (up, uq) |s, t| if (!try self.ref(Ref.of(self.an.nodes.items[s]), Ref.of(self.an.nodes.items[t]))) return false;
        }
        return true;
    }

    // Where a value stands in a cone: inside it, a literal, or a hole.
    const Place = enum { inside, lit, hole };

    fn placeOf(self: *const Pairing, root: u32, x: Ref) Place {
        const an = self.an;
        return switch (x.kind) {
            .node => blk: {
                const l = an.localOf(x.nodeId());
                if (an.is_lit[l]) break :blk .lit;
                break :blk if (an.inCone(root, l)) .inside else .hole;
            },
            .row_param, .input => .hole,
            .region_param => blk: {
                const owner = an.store.region(x.regionId()).owner;
                if (owner == NodeId.none) break :blk .hole;
                break :blk if (an.inCone(root, an.localOf(owner))) .inside else .hole;
            },
        };
    }

    fn ref(self: *Pairing, x: Ref, y: Ref) Allocator.Error!bool {
        const store = self.an.store;
        const px = self.placeOf(self.a, x);
        if (px != self.placeOf(self.b, y)) return false;
        switch (px) {
            .lit => {
                if (x.output != y.output or store.node(x.nodeId()).payload != store.node(y.nodeId()).payload) return false;
                try self.pairs.append(self.gpa(), .{ x.nodeId(), y.nodeId() });
                return true;
            },
            .inside => switch (x.kind) {
                .node => {
                    if (y.kind != .node or x.output != y.output) return false;
                    const gop = try self.nodes.getOrPut(self.gpa(), x.nodeId());
                    if (gop.found_existing) return gop.value_ptr.* == y.nodeId();
                    gop.value_ptr.* = y.nodeId();
                    try self.work.append(self.gpa(), .{ x.nodeId(), y.nodeId() });
                    try self.pairs.append(self.gpa(), .{ x.nodeId(), y.nodeId() });
                    return true;
                },
                .region_param => {
                    if (y.kind != .region_param or x.output != y.output) return false;
                    const paired = self.regions.get(x.regionId()) orelse return false;
                    return paired == y.regionId();
                },
                .row_param, .input => unreachable, // a parameter or a slot is never inside a cone
            },
            .hole => {
                const kx = rebuild.refKey(x);
                const ky = rebuild.refKey(y);
                if (self.holes_ab.get(kx)) |seen| return seen == ky;
                if (self.holes_ba.contains(ky)) return false;
                const join_x = x.kind == .region_param and x.output == Analysis.join_output;
                const join_y = y.kind == .region_param and y.output == Analysis.join_output;
                if (join_x != join_y) return false;
                if (!join_x) {
                    const ra = self.an.rows[self.an.row_of[self.a]];
                    const rb = self.an.rows[self.an.row_of[self.b]];
                    if (store.refTy(ra, x) != store.refTy(rb, y)) return false;
                }
                try self.holes_ab.put(self.gpa(), kx, ky);
                try self.holes_ba.put(self.gpa(), ky, kx);
                return true;
            },
        }
    }
};

const Sha256 = std.crypto.hash.sha2.Sha256;

fn putWords(h: *Sha256, ws: []const u32) void {
    h.update(std.mem.sliceAsBytes(ws));
}

fn putDigest(h: *Sha256, d: digest_mod.Digest) void {
    h.update(std.mem.asBytes(&d));
}

const testing = std.testing;
const builder_mod = @import("builder.zig");
const driver = @import("driver.zig");
const dump = @import("dump.zig");
const verify_mod = @import("verify.zig");

const Fixture = struct {
    store: ir.Store,
    types: types_mod.Types,
    b: builder_mod.Builder,

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

    fn expectGraph(self: *Fixture, root: RowId, want: []const u8) (driver.Error || std.Io.Writer.Error || error{TestExpectedEqual})!void {
        return self.expectView(root, .graph, want);
    }

    fn expectView(self: *Fixture, root: RowId, view: driver.View, want: []const u8) (driver.Error || std.Io.Writer.Error || error{TestExpectedEqual})!void {
        _ = try driver.runTo(testing.allocator, &self.b, root, &.{}, view);
        var out: std.Io.Writer.Allocating = .init(testing.allocator);
        defer out.deinit();
        try dump.dumpSite(&out.writer, testing.allocator, &self.store, &self.types, root);
        try testing.expectEqualStrings(want, out.written());
    }
};

// `|z| z * z`.
fn squareRow(f: *Fixture) Allocator.Error!RowId {
    const i64_ty = try f.types.intTy(.i64);
    const r = try f.b.beginRow(&.{i64_ty}, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) })} });
    return r;
}

test "V1: a row called from one place is inlined, and one called from two places stays a row" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const once = try squareRow(&f);
    const twice = try f.b.beginRow(&.{i64_ty}, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(0), try f.b.litInt(i64_ty, 1) })} });
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const a = try f.b.callRow(once, &.{Ref.rowParam(0)});
    const b1 = try f.b.callRow(twice, &.{Ref.rowParam(0)});
    const b2 = try f.b.callRow(twice, &.{Ref.rowParam(1)});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ a, try f.b.call(.i64, .bitwise_xor, &.{ b1, b2 }) })} });
    try f.expectGraph(root,
        \\row r0 (I64, I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p0) : I64
        \\  n1 = call r1(p0) : I64
        \\  n2 = call r1(p1) : I64
        \\  n3 = Num.I64.bitwise_xor(n0, n1, n2) : I64
        \\  value n3
        \\row r1 (I64) -> I64
        \\  n0 = 1 : I64
        \\  n1 = Num.I64.plus_wrap(p0, n0) : I64
        \\  value n1
        \\
    );
}

test "V1: the count is taken again, so a row two merged callers called becomes single-use and is inlined" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const sq = try squareRow(&f);
    // `f1` and `f2` are both `|a| sq(a + 1)`: N8g merges them, the two
    // calls merge, and V1 inlines the one row left, then `sq`.
    var callers: [2]RowId = undefined;
    for (&callers) |*c| {
        c.* = try f.b.beginRow(&.{i64_ty}, i64_ty);
        const next = try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(0), try f.b.litInt(i64_ty, 1) });
        try f.b.endRow(.{ .value = &.{try f.b.callRow(sq, &.{next})} });
    }
    const root = try f.b.beginRow(&.{i64_ty}, i64_ty);
    const x = try f.b.callRow(callers[0], &.{Ref.rowParam(0)});
    const y = try f.b.callRow(callers[1], &.{Ref.rowParam(0)});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ x, y })} });
    try f.expectGraph(root,
        \\row r0 (I64) -> I64
        \\  n0 = 1 : I64
        \\  n1 = Num.I64.plus_wrap(p0, n0) : I64
        \\  n2 = Num.I64.times_wrap(n1, n1) : I64
        \\  n3 = Num.I64.bitwise_xor(n2, n2) : I64
        \\  value n3
        \\
    );
}

test "V2: a row called from two places is inlined at both" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const sq = try squareRow(&f);
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const a = try f.b.callRow(sq, &.{Ref.rowParam(0)});
    const b1 = try f.b.callRow(sq, &.{Ref.rowParam(1)});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ a, b1 })} });
    try f.expectView(root, .inline_,
        \\row r0 (I64, I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p0) : I64
        \\  n1 = Num.I64.times_wrap(p1, p1) : I64
        \\  n2 = Num.I64.bitwise_xor(n0, n1) : I64
        \\  value n2
        \\
    );
}

test "V2: a closure of a row that is not recursive is a lambda in place, over its captures" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const fn_ty = try f.types.funcTy(&.{i64_ty}, i64_ty);
    // `|n| |x| sq(x) + n`, whose helper `sq` is inlined into the lambda.
    const sq = try squareRow(&f);
    const add = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ try f.b.callRow(sq, &.{Ref.rowParam(1)}), Ref.rowParam(0) })} });
    const root = try f.b.beginRow(&.{i64_ty}, fn_ty);
    try f.b.endRow(.{ .value = &.{try f.b.closure(add, &.{Ref.rowParam(0)}, fn_ty)} });
    try f.expectView(root, .inline_,
        \\row r0 (I64) -> (I64 -> I64)
        \\  n2 = lambda() : (I64 -> I64)
        \\    lambda (s2.0: I64)
        \\      n0 = Num.I64.times_wrap(s2.0, s2.0) : I64
        \\      n1 = Num.I64.plus_wrap(n0, p0) : I64
        \\      value n1
        \\  value n2
        \\
    );
}

test "V2: a recursive row stays a row, and the helper it calls is inlined into it" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const sq = try squareRow(&f);
    // `down = |n| if n == 0 then 0 else sq(n) + down(n - 1)`, called twice.
    const down = try f.b.beginRow(&.{i64_ty}, i64_ty);
    const zero = try f.b.litInt(i64_ty, 0);
    const done = try f.b.call(.i64, .is_eq, &.{ Ref.rowParam(0), zero });
    const arm0 = try f.b.openArm(done, 0);
    const rest = try f.b.callRow(down, &.{try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(0), try f.b.litInt(i64_ty, -1) })});
    try f.b.close(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ try f.b.callRow(sq, &.{Ref.rowParam(0)}), rest })} });
    const arm1 = try f.b.openArm(done, 1);
    try f.b.close(.{ .value = &.{zero} });
    try f.b.endRow(.{ .value = &.{try f.b.switchOn(done, &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{})} });
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const x = try f.b.callRow(down, &.{Ref.rowParam(0)});
    const y = try f.b.callRow(down, &.{Ref.rowParam(1)});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ x, y })} });
    try f.expectView(root, .inline_,
        \\row r0 (I64, I64) -> I64
        \\  n0 = call r1(p0) : I64 !spec
        \\  n1 = call r1(p1) : I64 !spec
        \\  n2 = Num.I64.bitwise_xor(n0, n1) : I64
        \\  value n2
        \\row r1 (I64) -> I64 recursive
        \\  n6 = switch p0 : I64 !spec
        \\    arm 0
        \\      n0 = 0 : I64
        \\      value n0
        \\    default
        \\      n1 = Num.I64.times_wrap(p0, p0) : I64
        \\      n2 = -1 : I64
        \\      n3 = Num.I64.plus_wrap(p0, n2) : I64
        \\      n4 = call r1(n3) : I64 !spec
        \\      n5 = Num.I64.plus_wrap(n1, n4) : I64
        \\      value n5
        \\  value n6
        \\
    );
}

test "V2: inlining a helper called twice cancels the record it builds against the field the caller reads" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const rec_ty = try f.types.recordTy(&.{ .{ .name = "x", .ty = i64_ty }, .{ .name = "y", .ty = i64_ty } });
    // `mk = |a| { x: a, y: a * a }`; the root is `mk(p0).y + mk(p1).x`.
    const mk = try f.b.beginRow(&.{i64_ty}, rec_ty);
    try f.b.endRow(.{ .value = &.{try f.b.record(rec_ty, &.{ Ref.rowParam(0), try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) }) })} });
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const y = try f.b.field(try f.b.callRow(mk, &.{Ref.rowParam(0)}), 1);
    const x = try f.b.field(try f.b.callRow(mk, &.{Ref.rowParam(1)}), 0);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ y, x })} });
    try f.expectView(root, .inline_,
        \\row r0 (I64, I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p0) : I64
        \\  n1 = Num.I64.bitwise_xor(n0, p1) : I64
        \\  value n1
        \\
    );
}

test "V2: a row whose body can end in Return stays a row, and its closure is still a lambda" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const fn_ty = try f.types.funcTy(&.{i64_ty}, i64_ty);
    // `early = |a| { if a == 0 { return 1 }; a * a + early_rest }`, where the
    // code after the `if` is a join two paths reach, so no exit rule folds it.
    const early = try f.b.beginRow(&.{i64_ty}, i64_ty);
    const zero = try f.b.litInt(i64_ty, 0);
    const c = try f.b.call(.i64, .is_lt, &.{ Ref.rowParam(0), zero });
    const join = try f.b.reserveJoin(&.{i64_ty});
    const arm0 = try f.b.openArm(c, 0);
    const d = try f.b.call(.i64, .is_eq, &.{ Ref.rowParam(0), zero });
    const inner0 = try f.b.openArm(d, 0);
    try f.b.close(.{ .jump = .{ .join = join, .args = &.{Ref.rowParam(0)} } });
    const inner1 = try f.b.openArm(d, 1);
    try f.b.close(.{ .return_ = try f.b.litInt(i64_ty, 1) });
    const inner = try f.b.exitingSwitch(d, &.{ inner0, inner1 }, &.{}, &.{});
    try f.b.close(.{ .branch = inner });
    const arm1 = try f.b.openArm(c, 1);
    try f.b.close(.{ .jump = .{ .join = join, .args = &.{try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) })} } });
    const sw = try f.b.exitingSwitch(c, &.{ arm0, arm1 }, &.{join}, &.{});
    try f.b.continueIn(sw, join);
    const v = Ref.regionParam(join, 0);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ v, v })} });
    const pair_ty = try f.types.tupleTy(&.{ i64_ty, fn_ty });
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, pair_ty);
    const twice = try f.b.call(.i64, .plus_wrap, &.{ try f.b.callRow(early, &.{Ref.rowParam(0)}), try f.b.callRow(early, &.{Ref.rowParam(1)}) });
    try f.b.endRow(.{ .value = &.{try f.b.tuple(pair_ty, &.{ twice, try f.b.closure(early, &.{}, fn_ty) })} });
    try f.expectView(root, .inline_,
        \\row r0 (I64, I64) -> (I64, (I64 -> I64))
        \\  n0 = call r1(p0) : I64 !spec
        \\  n1 = call r1(p1) : I64 !spec
        \\  n2 = Num.I64.plus_wrap(n0, n1) : I64
        \\  n3 = 0 : I64
        \\  n6 = 1 : I64
        \\  n11 = lambda() : (I64 -> I64)
        \\    lambda (s11.0: I64)
        \\      n4 = Num.I64.is_lt(s11.0, n3) : Bool
        \\      n10 = switch n4 : !spec
        \\        arm 0
        \\          n5 = Num.I64.is_eq(s11.0, n3) : Bool
        \\          n7 = switch n5 : !spec
        \\            arm 0
        \\              jump j0 s11.0
        \\            arm 1
        \\              return n6
        \\          branch n7
        \\        arm 1
        \\          n8 = Num.I64.plus_wrap(s11.0, s11.0) : I64
        \\          jump j0 n8
        \\        join j0 (s10.0: I64)
        \\          n9 = Num.I64.times_wrap(s10.0, s10.0) : I64
        \\          return n9
        \\      branch n10
        \\  n12 = tuple(n2, n11) : (I64, (I64 -> I64))
        \\  value n12
        \\row r1 (I64) -> I64
        \\  n0 = 0 : I64
        \\  n1 = Num.I64.is_lt(p0, n0) : Bool
        \\  n7 = switch n1 : !spec
        \\    arm 0
        \\      n2 = Num.I64.is_eq(p0, n0) : Bool
        \\      n4 = switch n2 : !spec
        \\        arm 0
        \\          jump j0 p0
        \\        arm 1
        \\          n3 = 1 : I64
        \\          return n3
        \\      branch n4
        \\    arm 1
        \\      n5 = Num.I64.plus_wrap(p0, p0) : I64
        \\      jump j0 n5
        \\    join j0 (s7.0: I64)
        \\      n6 = Num.I64.times_wrap(s7.0, s7.0) : I64
        \\      return n6
        \\  branch n7
        \\
    );
}

test "V2: the simplify rerun simplifies an inlined body's nodes under the facts of the arms they sink into" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const bool_ty = try f.types.boolTy();
    const pair_ty = try f.types.tupleTy(&.{ i64_ty, i64_ty });
    // `both = |c, a| (if c { a } else { a * a }, a + 1)`, called twice. The
    // root reads both parts of `both(p0, p1)` in the arms of a switch on
    // `p0`, so the call stands before the switch, and the `if` sinks into
    // the arm where `p0` is False, which decides it.
    const both = try f.b.beginRow(&.{ bool_ty, i64_ty }, pair_ty);
    const no = try f.b.openArm(Ref.rowParam(0), 0);
    try f.b.close(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(1), Ref.rowParam(1) })} });
    const yes = try f.b.openArm(Ref.rowParam(0), 1);
    try f.b.close(.{ .value = &.{Ref.rowParam(1)} });
    const first = try f.b.switchOn(Ref.rowParam(0), &.{ no, yes }, &.{}, &.{i64_ty}, &.{});
    try f.b.endRow(.{ .value = &.{try f.b.tuple(pair_ty, &.{ first, try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(1), try f.b.litInt(i64_ty, 1) }) })} });
    const root = try f.b.beginRow(&.{ bool_ty, i64_ty, bool_ty, i64_ty }, i64_ty);
    const t = try f.b.callRow(both, &.{ Ref.rowParam(0), Ref.rowParam(1) });
    const other = try f.b.index(try f.b.callRow(both, &.{ Ref.rowParam(2), Ref.rowParam(3) }), 1);
    const arm0 = try f.b.openArm(Ref.rowParam(0), 0);
    try f.b.close(.{ .value = &.{try f.b.index(t, 0)} });
    const arm1 = try f.b.openArm(Ref.rowParam(0), 1);
    try f.b.close(.{ .value = &.{try f.b.index(t, 1)} });
    const chosen = try f.b.switchOn(Ref.rowParam(0), &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ chosen, other })} });
    try f.expectView(root, .inline_,
        \\row r0 (Bool, I64, Bool, I64) -> I64
        \\  n1 = 1 : I64
        \\  n3 = switch p0 : I64
        \\    arm 0
        \\      n0 = Num.I64.times_wrap(p1, p1) : I64
        \\      value n0
        \\    arm 1
        \\      n2 = Num.I64.plus_wrap(p1, n1) : I64
        \\      value n2
        \\  n4 = Num.I64.plus_wrap(p3, n1) : I64
        \\  n5 = Num.I64.bitwise_xor(n3, n4) : I64
        \\  value n5
        \\
    );
}

test "V2: a lambda body whose exits fold ends in its value, as a row body does" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const fn_ty = try f.types.funcTy(&.{i64_ty}, i64_ty);
    const pair_ty = try f.types.tupleTy(&.{ i64_ty, fn_ty });
    // `g = |k, a| { if k < 0 { if a == 0 { return 1 } }; k * k }`, where the
    // code after the `if` is a join two paths reach. In the lambda over
    // `k = p0`, the join's `k * k` is the caller's `p0 * p0`, so the join has
    // no nodes of its own, and the exit rules fold the lambda's body to a
    // `Return`, which T6 makes its value.
    const g = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const zero = try f.b.litInt(i64_ty, 0);
    const c = try f.b.call(.i64, .is_lt, &.{ Ref.rowParam(0), zero });
    const join = try f.b.reserveJoin(&.{});
    const arm0 = try f.b.openArm(c, 0);
    try f.b.close(.{ .jump = .{ .join = join, .args = &.{} } });
    const arm1 = try f.b.openArm(c, 1);
    const d = try f.b.call(.i64, .is_eq, &.{ Ref.rowParam(1), zero });
    const inner0 = try f.b.openArm(d, 0);
    try f.b.close(.{ .jump = .{ .join = join, .args = &.{} } });
    const inner1 = try f.b.openArm(d, 1);
    try f.b.close(.{ .return_ = try f.b.litInt(i64_ty, 1) });
    const inner = try f.b.exitingSwitch(d, &.{ inner0, inner1 }, &.{}, &.{});
    try f.b.close(.{ .branch = inner });
    const sw = try f.b.exitingSwitch(c, &.{ arm0, arm1 }, &.{join}, &.{});
    try f.b.continueIn(sw, join);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) })} });
    const root = try f.b.beginRow(&.{i64_ty}, pair_ty);
    const sq = try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) });
    try f.b.endRow(.{ .value = &.{try f.b.tuple(pair_ty, &.{ sq, try f.b.closure(g, &.{Ref.rowParam(0)}, fn_ty) })} });
    try f.expectView(root, .inline_,
        \\row r0 (I64) -> (I64, (I64 -> I64))
        \\  n0 = Num.I64.times_wrap(p0, p0) : I64
        \\  n1 = 0 : I64
        \\  n2 = Num.I64.is_lt(p0, n1) : Bool
        \\  n5 = 1 : I64
        \\  n7 = lambda() : (I64 -> I64)
        \\    lambda (s7.0: I64)
        \\      n4 = and(n2) : Bool
        \\        operand
        \\          n3 = Num.I64.is_eq(s7.0, n1) : Bool
        \\          value n3
        \\      n6 = switch n4 : I64
        \\        arm 0
        \\          value n0
        \\        arm 1
        \\          value n5
        \\      value n6
        \\  n8 = tuple(n0, n7) : (I64, (I64 -> I64))
        \\  value n8
        \\
    );
}

// `|n| if n < 1 { B } else { A }`, its tags built at `tag_ty`.
fn pickRow(f: *Fixture, tag_ty: TyId) Allocator.Error!RowId {
    const i64_ty = try f.types.intTy(.i64);
    const a = try f.types.name("A");
    const b_name = try f.types.name("B");
    const row = try f.b.beginRow(&.{i64_ty}, tag_ty);
    const c = try f.b.call(.i64, .is_lt, &.{ Ref.rowParam(0), try f.b.litInt(i64_ty, 1) });
    const no = try f.b.openArm(c, 0);
    try f.b.close(.{ .value = &.{try f.b.tag(tag_ty, b_name, &.{})} });
    const yes = try f.b.openArm(c, 1);
    try f.b.close(.{ .value = &.{try f.b.tag(tag_ty, a, &.{})} });
    try f.b.endRow(.{ .value = &.{try f.b.switchOn(c, &.{ no, yes }, &.{}, &.{tag_ty}, &.{})} });
    return row;
}

// The view of `root`, its dump, and the digest of its body, which must verify.
fn inlinedForm(f: *Fixture, root: RowId, dump_out: *std.Io.Writer.Allocating) (driver.Error || std.Io.Writer.Error || Allocator.Error || error{TestUnexpectedResult})!digest_mod.Digest {
    _ = try driver.runTo(testing.allocator, &f.b, root, &.{}, .inline_);
    var report = try verify_mod.verifyAll(testing.allocator, &f.store, &f.types);
    defer report.deinit();
    try testing.expect(report.ok());
    try dump.dumpSite(&dump_out.writer, testing.allocator, &f.store, &f.types, root);
    return digest_mod.ofRegion(testing.allocator, &f.store, f.store.row(root).body);
}

test "V2: a call read at a wider union inlines to a body whose ends are built at that union" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const narrow = try f.types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{} } });
    const wide = try f.types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{} }, .{ .name = "C", .payload = &.{} } });
    // `pick` builds `[A, B]`, and the root calls it at `[A, B, C]`.
    const pick = try pickRow(&f, narrow);
    const root = try f.b.beginRow(&.{i64_ty}, wide);
    try f.b.endRow(.{ .value = &.{try f.b.callRowAt(pick, &.{Ref.rowParam(0)}, wide)} });
    // The same code written at `[A, B, C]`.
    const written = try pickRow(&f, wide);

    var got: std.Io.Writer.Allocating = .init(testing.allocator);
    defer got.deinit();
    var want: std.Io.Writer.Allocating = .init(testing.allocator);
    defer want.deinit();
    const got_digest = try inlinedForm(&f, root, &got);
    const want_digest = try inlinedForm(&f, written, &want);
    try testing.expectEqualStrings(
        \\row r0 (I64) -> [A, B, C]
        \\  n0 = 1 : I64
        \\  n1 = Num.I64.is_lt(p0, n0) : Bool
        \\  n4 = switch n1 : [A, B, C]
        \\    arm 0
        \\      n2 = tag B() : [A, B, C]
        \\      value n2
        \\    arm 1
        \\      n3 = tag A() : [A, B, C]
        \\      value n3
        \\  value n4
        \\
    , got.written());
    try testing.expectEqualStrings(want.written(), got.written());
    try testing.expectEqual(want_digest, got_digest);
}

test "V2: a call read at a wider union demands the payload types of a tag and the backing of a nominal" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const inner_narrow = try f.types.tagUnionTy(&.{.{ .name = "A", .payload = &.{} }});
    const inner_wide = try f.types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{} } });
    const some = try f.types.name("Some");
    const a = try f.types.name("A");
    // `Opt := [Some(inner, I64)]`, read at `Opt([A, B])`, built as `Opt([A])`.
    const narrow = try f.types.nominalTy("Opt", try f.types.tagUnionTy(&.{.{ .name = "Some", .payload = &.{ inner_narrow, i64_ty } }}));
    const wide = try f.types.nominalTy("Opt", try f.types.tagUnionTy(&.{.{ .name = "Some", .payload = &.{ inner_wide, i64_ty } }}));
    var rows: [2]RowId = undefined;
    for (&rows, [2]TyId{ narrow, wide }, [2]TyId{ inner_narrow, inner_wide }) |*row, ty, inner| {
        row.* = try f.b.beginRow(&.{i64_ty}, ty);
        const payload = try f.b.tag(inner, a, &.{});
        const backing = try f.types.unfold(ty);
        try f.b.endRow(.{ .value = &.{try f.b.wrap(ty, try f.b.tag(backing, some, &.{ payload, Ref.rowParam(0) }))} });
    }
    const root = try f.b.beginRow(&.{i64_ty}, wide);
    try f.b.endRow(.{ .value = &.{try f.b.callRowAt(rows[0], &.{Ref.rowParam(0)}, wide)} });

    var got: std.Io.Writer.Allocating = .init(testing.allocator);
    defer got.deinit();
    var want: std.Io.Writer.Allocating = .init(testing.allocator);
    defer want.deinit();
    const got_digest = try inlinedForm(&f, root, &got);
    const want_digest = try inlinedForm(&f, rows[1], &want);
    try testing.expectEqualStrings(
        \\row r0 (I64) -> Opt
        \\  n0 = tag A() : [A, B]
        \\  n1 = tag Some(n0, p0) : [Some([A, B], I64)]
        \\  n2 = wrap(n1) : Opt
        \\  value n2
        \\
    , got.written());
    try testing.expectEqualStrings(want.written(), got.written());
    try testing.expectEqual(want_digest, got_digest);
}

test "V2: a value another node also reads keeps its own type when the call is read at a wider union" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const inner_narrow = try f.types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{} } });
    const inner_wide = try f.types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{} }, .{ .name = "C", .payload = &.{} } });
    const narrow = try f.types.tagUnionTy(&.{.{ .name = "Some", .payload = &.{ inner_narrow, i64_ty } }});
    const wide = try f.types.tagUnionTy(&.{.{ .name = "Some", .payload = &.{ inner_wide, i64_ty } }});
    const names = [_]types_mod.NameId{ try f.types.name("A"), try f.types.name("B") };
    // `pick = |n| { s = if n < 1 { B } else { A }; Some(s, match s { A => 1, B => 2 }) }`:
    // the end demands `s` at `[A, B, C]`, and the match reads it at `[A, B]`.
    const pick = try f.b.beginRow(&.{i64_ty}, narrow);
    const c = try f.b.call(.i64, .is_lt, &.{ Ref.rowParam(0), try f.b.litInt(i64_ty, 1) });
    const no = try f.b.openArm(c, 0);
    try f.b.close(.{ .value = &.{try f.b.tag(inner_narrow, names[1], &.{})} });
    const yes = try f.b.openArm(c, 1);
    try f.b.close(.{ .value = &.{try f.b.tag(inner_narrow, names[0], &.{})} });
    const s = try f.b.switchOn(c, &.{ no, yes }, &.{}, &.{inner_narrow}, &.{});
    var arms: [2]ir.RegionId = undefined;
    for (&arms, names, 1..) |*arm, name, value| {
        arm.* = try f.b.openTagArm(s, name);
        try f.b.close(.{ .value = &.{try f.b.litInt(i64_ty, @intCast(value))} });
    }
    const read = try f.b.tagSwitchOn(s, &names, &arms, &.{}, &.{i64_ty});
    try f.b.endRow(.{ .value = &.{try f.b.tag(narrow, try f.types.name("Some"), &.{ s, read })} });
    const root = try f.b.beginRow(&.{i64_ty}, wide);
    try f.b.endRow(.{ .value = &.{try f.b.callRowAt(pick, &.{Ref.rowParam(0)}, wide)} });

    var got: std.Io.Writer.Allocating = .init(testing.allocator);
    defer got.deinit();
    _ = try inlinedForm(&f, root, &got);
    // `n4` stays at `[A, B]`, which the match needs, and conforms to the slot.
    try testing.expectEqualStrings(
        \\row r0 (I64) -> [Some([A, B, C], I64)]
        \\  n0 = 1 : I64
        \\  n1 = Num.I64.is_lt(p0, n0) : Bool
        \\  n4 = switch n1 : [A, B]
        \\    arm 0
        \\      n2 = tag B() : [A, B]
        \\      value n2
        \\    arm 1
        \\      n3 = tag A() : [A, B]
        \\      value n3
        \\  n6 = switch n4 : I64
        \\    arm 0
        \\      value n0
        \\    arm 1
        \\      n5 = 2 : I64
        \\      value n5
        \\  n7 = tag Some(n4, n6) : [Some([A, B, C], I64)]
        \\  value n7
        \\
    , got.written());
}

// V3 fixtures. Each builds a root over I64 parameters.
const eval_mod = @import("eval.zig");

// `((a * b) + 7) * a) & b`: four nodes and a literal.
fn pattern(f: *Fixture, a: Ref, b: Ref) Allocator.Error!Ref {
    const i64_ty = try f.types.intTy(.i64);
    const ab = try f.b.call(.i64, .times_wrap, &.{ a, b });
    const plus = try f.b.call(.i64, .plus_wrap, &.{ ab, try f.b.litInt(i64_ty, 7) });
    const again = try f.b.call(.i64, .times_wrap, &.{ plus, a });
    return f.b.call(.i64, .bitwise_and, &.{ again, b });
}

// `(((x * y) + z) * 7) & z`.
fn shared(f: *Fixture, x: Ref, y: Ref, z: Ref) Allocator.Error!Ref {
    const i64_ty = try f.types.intTy(.i64);
    const xy = try f.b.call(.i64, .times_wrap, &.{ x, y });
    const plus = try f.b.call(.i64, .plus_wrap, &.{ xy, z });
    const scaled = try f.b.call(.i64, .times_wrap, &.{ plus, try f.b.litInt(i64_ty, 7) });
    return f.b.call(.i64, .bitwise_and, &.{ scaled, z });
}

// `((((pattern(a, b) * c) + 9) * c) & a)`: eight nodes, `pattern` among them.
fn larger(f: *Fixture, a: Ref, b: Ref, c: Ref) Allocator.Error!Ref {
    const i64_ty = try f.types.intTy(.i64);
    const inner = try pattern(f, a, b);
    const times = try f.b.call(.i64, .times_wrap, &.{ inner, c });
    const plus = try f.b.call(.i64, .plus_wrap, &.{ times, try f.b.litInt(i64_ty, 9) });
    const again = try f.b.call(.i64, .times_wrap, &.{ plus, c });
    return f.b.call(.i64, .bitwise_and, &.{ again, a });
}

fn params(f: *Fixture, comptime n: usize) Allocator.Error![n]TyId {
    var out: [n]TyId = undefined;
    for (&out) |*t| t.* = try f.types.intTy(.i64);
    return out;
}

// `pattern` at two places, over two pairs of parameters.
fn twoPlaces(f: *Fixture, _: bool) Allocator.Error!RowId {
    const root = try f.b.beginRow(&try params(f, 4), try f.types.intTy(.i64));
    const x = try pattern(f, Ref.rowParam(0), Ref.rowParam(1));
    const y = try pattern(f, Ref.rowParam(2), Ref.rowParam(3));
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .minus, &.{ x, y })} });
    return root;
}

// `shared(p0, p0, p1)` and `shared(p2, p2, p3)` share a shape, and
// `shared(p0, p1, p2)` has another.
fn holePattern(f: *Fixture, _: bool) Allocator.Error!RowId {
    const root = try f.b.beginRow(&try params(f, 4), try f.types.intTy(.i64));
    const x = try shared(f, Ref.rowParam(0), Ref.rowParam(0), Ref.rowParam(1));
    const y = try shared(f, Ref.rowParam(2), Ref.rowParam(2), Ref.rowParam(3));
    const z = try shared(f, Ref.rowParam(0), Ref.rowParam(1), Ref.rowParam(2));
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .minus, &.{ try f.b.call(.i64, .minus, &.{ x, y }), z })} });
    return root;
}

// `larger` at two places and `pattern` alone at a third. With `reversed`,
// the three are built in the other order.
fn nested(f: *Fixture, reversed: bool) Allocator.Error!RowId {
    const root = try f.b.beginRow(&try params(f, 8), try f.types.intTy(.i64));
    var parts: [3]Ref = undefined;
    if (reversed) {
        parts[2] = try pattern(f, Ref.rowParam(6), Ref.rowParam(7));
        parts[1] = try larger(f, Ref.rowParam(3), Ref.rowParam(4), Ref.rowParam(5));
        parts[0] = try larger(f, Ref.rowParam(0), Ref.rowParam(1), Ref.rowParam(2));
    } else {
        parts[0] = try larger(f, Ref.rowParam(0), Ref.rowParam(1), Ref.rowParam(2));
        parts[1] = try larger(f, Ref.rowParam(3), Ref.rowParam(4), Ref.rowParam(5));
        parts[2] = try pattern(f, Ref.rowParam(6), Ref.rowParam(7));
    }
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .minus, &.{ try f.b.call(.i64, .minus, &.{ parts[0], parts[1] }), parts[2] })} });
    return root;
}

// `(((down(b, a) * a) + 7) * a) & b` at two places of the root, and once in
// `down = |n, m| if n == 0 { 0 } else { (((down(m, n) * n) + 7) * n) & m }`.
fn recursive(f: *Fixture, _: bool) Allocator.Error!RowId {
    const i64_ty = try f.types.intTy(.i64);
    const Occ = struct {
        fn of(ff: *Fixture, down: RowId, a: Ref, b: Ref) Allocator.Error!Ref {
            const ty = try ff.types.intTy(.i64);
            const call = try ff.b.callRow(down, &.{ b, a });
            const times = try ff.b.call(.i64, .times_wrap, &.{ call, a });
            const plus = try ff.b.call(.i64, .plus_wrap, &.{ times, try ff.b.litInt(ty, 7) });
            const again = try ff.b.call(.i64, .times_wrap, &.{ plus, a });
            return ff.b.call(.i64, .bitwise_and, &.{ again, b });
        }
    };
    const down = try f.b.beginRow(&try params(f, 2), i64_ty);
    const zero = try f.b.litInt(i64_ty, 0);
    const done = try f.b.call(.i64, .is_eq, &.{ Ref.rowParam(0), zero });
    const arm0 = try f.b.openArm(done, 0);
    try f.b.close(.{ .value = &.{try Occ.of(f, down, Ref.rowParam(0), Ref.rowParam(1))} });
    const arm1 = try f.b.openArm(done, 1);
    try f.b.close(.{ .value = &.{zero} });
    try f.b.endRow(.{ .value = &.{try f.b.switchOn(done, &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{})} });
    const root = try f.b.beginRow(&try params(f, 4), i64_ty);
    const x = try Occ.of(f, down, Ref.rowParam(0), Ref.rowParam(1));
    const y = try Occ.of(f, down, Ref.rowParam(2), Ref.rowParam(3));
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .minus, &.{ x, y })} });
    return root;
}

const Build = *const fn (*Fixture, bool) Allocator.Error!RowId;

// The `outline` view of what `build` builds, checked against what V3
// promises of it (L2): it verifies, a further pass chooses nothing, and
// every row it made is not recursive and ends in one value.
fn expectOutline(build: Build, reversed: bool, ties: ?std.Random, want: []const u8) !void {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const root = try build(&f, reversed);
    const before = f.store.rows.items.len;
    f.b.hooks.shuffle = ties;
    _ = try driver.runTo(testing.allocator, &f.b, root, &.{}, .outline);
    var report = try verify_mod.verifyAll(testing.allocator, &f.store, &f.types);
    defer report.deinit();
    try testing.expect(report.ok());
    var again = try outlineSelect(testing.allocator, &f.store, &f.types, root, outline_min_size);
    defer again.deinit();
    try testing.expectEqual(@as(usize, 0), again.shapes.len);
    for (f.store.rows.items[before..]) |row| {
        if (row.merged_into != null) continue;
        try testing.expect(!row.recursive);
        const end = f.store.region(row.body).end;
        try testing.expect(end.kind == .value and end.refs.len == 1);
    }
    var out: std.Io.Writer.Allocating = .init(testing.allocator);
    defer out.deinit();
    try dump.dumpSite(&out.writer, testing.allocator, &f.store, &f.types, root);
    try testing.expectEqualStrings(want, out.written());
}

// Views agree (L5): `graph`, `inline` and `outline` of what `build` builds
// compute one value on each of `inputs`.
fn expectViewsAgree(build: Build, inputs: []const []const i64) !void {
    var arena_impl = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_impl.deinit();
    const arena = arena_impl.allocator();
    var fixtures: [3]Fixture = undefined;
    var roots: [3]RowId = undefined;
    const views_of = [3]driver.View{ .graph, .inline_, .outline };
    for (&fixtures, &roots, views_of) |*f, *root, view| {
        f.init();
        root.* = try build(f, false);
        _ = try driver.runTo(testing.allocator, &f.b, root.*, &.{}, view);
    }
    defer for (&fixtures) |*f| f.deinit();
    for (inputs) |input| {
        const args = try arena.alloc(eval_mod.Value, input.len);
        for (args, input) |*a, v| a.* = .{ .int = v };
        var values: [3]eval_mod.Value = undefined;
        for (&fixtures, roots, &values) |*f, root, *value| {
            var e = try eval_mod.Evaluator.init(arena, &f.store, &f.types, .strict);
            value.* = try e.run(root, args);
        }
        try testing.expect(values[0].eql(values[1]));
        try testing.expect(values[0].eql(values[2]));
    }
}

const inputs4 = [_][]const i64{ &.{ 1, 2, 3, 4 }, &.{ -5, 7, 0, 11 }, &.{ 123456789, -987654321, 42, -1 } };

test "V3: a computation at two places becomes one row, and each place calls it" {
    try expectOutline(twoPlaces, false, null,
        \\row r0 (I64, I64, I64, I64) -> I64
        \\  n0 = call r1(p0, p1) : I64
        \\  n1 = call r1(p2, p3) : I64
        \\  n2 = Num.I64.minus(n0, n1) : I64 !spec
        \\  value n2
        \\row r1 (I64, I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p1) : I64
        \\  n1 = 7 : I64
        \\  n2 = Num.I64.plus_wrap(n0, n1) : I64
        \\  n3 = Num.I64.times_wrap(n2, p0) : I64
        \\  n4 = Num.I64.bitwise_and(n3, p1) : I64
        \\  value n4
        \\
    );
    try expectViewsAgree(twoPlaces, &inputs4);
}

test "V3: a cone smaller than K stays where it is" {
    const Small = struct {
        fn build(f: *Fixture, _: bool) Allocator.Error!RowId {
            const i64_ty = try f.types.intTy(.i64);
            const root = try f.b.beginRow(&try params(f, 4), i64_ty);
            var parts: [2]Ref = undefined;
            for (&parts, 0..) |*part, k| {
                const a = Ref.rowParam(@intCast(2 * k));
                const b = Ref.rowParam(@intCast(2 * k + 1));
                const ab = try f.b.call(.i64, .times_wrap, &.{ a, b });
                const plus = try f.b.call(.i64, .plus_wrap, &.{ ab, try f.b.litInt(i64_ty, 7) });
                part.* = try f.b.call(.i64, .times_wrap, &.{ plus, a });
            }
            try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .minus, &.{ parts[0], parts[1] })} });
            return root;
        }
    };
    try expectOutline(Small.build, false, null,
        \\row r0 (I64, I64, I64, I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p1) : I64
        \\  n1 = 7 : I64
        \\  n2 = Num.I64.plus_wrap(n0, n1) : I64
        \\  n3 = Num.I64.times_wrap(n2, p0) : I64
        \\  n4 = Num.I64.times_wrap(p2, p3) : I64
        \\  n5 = Num.I64.plus_wrap(n4, n1) : I64
        \\  n6 = Num.I64.times_wrap(n5, p2) : I64
        \\  n7 = Num.I64.minus(n3, n6) : I64 !spec
        \\  value n7
        \\
    );
}

test "V3: holes are numbered by first occurrence, so `a * a` and `a * b` are two shapes" {
    try expectOutline(holePattern, false, null,
        \\row r0 (I64, I64, I64, I64) -> I64
        \\  n0 = call r1(p0, p1) : I64
        \\  n1 = call r1(p2, p3) : I64
        \\  n2 = Num.I64.minus(n0, n1) : I64 !spec
        \\  n3 = Num.I64.times_wrap(p0, p1) : I64
        \\  n4 = Num.I64.plus_wrap(n3, p2) : I64
        \\  n5 = 7 : I64
        \\  n6 = Num.I64.times_wrap(n4, n5) : I64
        \\  n7 = Num.I64.bitwise_and(n6, p2) : I64
        \\  n8 = Num.I64.minus(n2, n7) : I64 !spec
        \\  value n8
        \\row r1 (I64, I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p0) : I64
        \\  n1 = Num.I64.plus_wrap(n0, p1) : I64
        \\  n2 = 7 : I64
        \\  n3 = Num.I64.times_wrap(n1, n2) : I64
        \\  n4 = Num.I64.bitwise_and(n3, p1) : I64
        \\  value n4
        \\
    );
    try expectViewsAgree(holePattern, &inputs4);
}

test "V3: the larger gain is taken first, and the next pass finds the repetition inside its row" {
    try expectOutline(nested, false, null,
        \\row r0 (I64, I64, I64, I64, I64, I64, I64, I64) -> I64
        \\  n0 = call r1(p0, p1, p2) : I64
        \\  n1 = call r1(p3, p4, p5) : I64
        \\  n2 = Num.I64.minus(n0, n1) : I64 !spec
        \\  n3 = call r2(p6, p7) : I64
        \\  n4 = Num.I64.minus(n2, n3) : I64 !spec
        \\  value n4
        \\row r1 (I64, I64, I64) -> I64
        \\  n0 = call r2(p0, p1) : I64
        \\  n1 = Num.I64.times_wrap(n0, p2) : I64
        \\  n2 = 9 : I64
        \\  n3 = Num.I64.plus_wrap(n1, n2) : I64
        \\  n4 = Num.I64.times_wrap(n3, p2) : I64
        \\  n5 = Num.I64.bitwise_and(n4, p0) : I64
        \\  value n5
        \\row r2 (I64, I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p1) : I64
        \\  n1 = 7 : I64
        \\  n2 = Num.I64.plus_wrap(n0, n1) : I64
        \\  n3 = Num.I64.times_wrap(n2, p0) : I64
        \\  n4 = Num.I64.bitwise_and(n3, p1) : I64
        \\  value n4
        \\
    );
    try expectViewsAgree(nested, &.{ &.{ 1, 2, 3, 4, 5, 6, 7, 8 }, &.{ -3, 9, 27, -81, 243, 0, 5, -5 } });
}

test "V3: a cone in a recursive row that calls its own component stays, and the others outline" {
    try expectOutline(recursive, false, null,
        \\row r0 (I64, I64, I64, I64) -> I64
        \\  n0 = call r1(p1, p0) : I64 !spec
        \\  n1 = call r1(p3, p2) : I64 !spec
        \\  n2 = Num.I64.minus(n0, n1) : I64 !spec
        \\  value n2
        \\row r1 (I64, I64) -> I64
        \\  n0 = call r2(p0, p1) : I64 !spec
        \\  n1 = Num.I64.times_wrap(n0, p1) : I64
        \\  n2 = 7 : I64
        \\  n3 = Num.I64.plus_wrap(n1, n2) : I64
        \\  n4 = Num.I64.times_wrap(n3, p1) : I64
        \\  n5 = Num.I64.bitwise_and(n4, p0) : I64
        \\  value n5
        \\row r2 (I64, I64) -> I64 recursive
        \\  n7 = switch p0 : I64 !spec
        \\    arm 0
        \\      n0 = 0 : I64
        \\      value n0
        \\    default
        \\      n1 = call r2(p1, p0) : I64 !spec
        \\      n2 = Num.I64.times_wrap(n1, p0) : I64
        \\      n3 = 7 : I64
        \\      n4 = Num.I64.plus_wrap(n2, n3) : I64
        \\      n5 = Num.I64.times_wrap(n4, p0) : I64
        \\      n6 = Num.I64.bitwise_and(n5, p1) : I64
        \\      value n6
        \\  value n7
        \\
    );
    try expectViewsAgree(recursive, &.{ &.{ 3, 0, 5, 0 }, &.{ -7, 0, 0, 2 } });
}

test "L6 V3: selection does not depend on the build order or on how placement breaks ties" {
    var want: std.Io.Writer.Allocating = .init(testing.allocator);
    defer want.deinit();
    {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        const root = try nested(&f, false);
        _ = try driver.runTo(testing.allocator, &f.b, root, &.{}, .outline);
        try dump.dumpSite(&want.writer, testing.allocator, &f.store, &f.types, root);
    }
    for (0..16) |seed| {
        var prng = std.Random.DefaultPrng.init(seed);
        try expectOutline(nested, seed % 2 == 1, prng.random(), want.written());
    }
}
