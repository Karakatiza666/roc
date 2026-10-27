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
// | places and keys | `Analysis.keyOf`: per place and depth d, the cone read down to depth d, with every other value a leaf numbered by first occurrence |
// | groups | `outlineSelect`: runs of one key at every depth up to d among the places sorted by their keys, for d from 0 to D |
// | generalization | `Gen.evaluate`: the least general generalization of a group (`Gen.round`), with the rules that keep meaning (`Gen.rules`) run until none applies, and the places whose images overlap left out |
// | selection | `outlineSelect`: gain c(s - 1) - ch descending, then s descending, then shape, first place and depth ascending; a candidate whose evaluation predates a take is evaluated again |
// | rows | `driver.zig`: each chosen generalization becomes a row (`rebuild.cone`), each place a `Call` of it, and the passes repeat until none is chosen |
//
// A cone stops at row parameters, input slots, the parameters of a region
// no node of the cone owns, and nodes something outside the cone reads. A
// literal is part of every cone that reads it, as `to_tree` substitutes it
// at every read (normal-form 5.4), and a cone's size does not count it. A
// cone is a place only when outlining it keeps its meaning: its root has
// one output, no region in it ends by leaving it (a `Return` of the row, a
// `Continue` or `Break` of a loop outside it, a `Jump` to a join outside
// it), and, in a recursive row, it calls or names no row of that row's
// component, so outlining never joins a new row to a recursive component.

/// K: the least size of a generalization `outline` makes a row of, literals
/// not counted. A constant of the language version (normal-form 5.3). It is
/// at least 3, so every take lowers the site's measure (`SiteSize.measure`).
pub const outline_min_size: u32 = 4;

/// D: the deepest key places are grouped by (normal-form 5.3, rule 2). A
/// constant of the language version.
pub const outline_key_depth: u32 = 3;

comptime {
    std.debug.assert(outline_min_size >= 3);
}

/// One pass of `outline`: the generalizations it chose, in selection order,
/// and per row that holds an occurrence, what the row's copy replaces.
pub const Selection = struct {
    arena: std.heap.ArenaAllocator,
    shapes: []const Chosen = &.{},
    edits: []const Edit = &.{},

    /// One place a generalization is taken at: its root, in its row, the
    /// values of its holes in hole order, and the values that move out of
    /// its cone, which the caller builds just before the call, in site order.
    pub const Occurrence = struct { row: RowId, root: NodeId, holes: []const Ref, moved: []const NodeId };

    /// A chosen generalization. Its row is copied from `rep`, the first of
    /// its occurrences in site order.
    pub const Chosen = struct {
        rep: Occurrence,
        /// The nodes of `rep`'s image, which the row copies, its root among them.
        nodes: std.AutoHashMapUnmanaged(NodeId, void),
        /// The nodes of `rep`'s cone the row does not build: those its
        /// caller keeps, and the literals in the image's regions that only
        /// they read.
        skip: []const NodeId,
        /// Per hole, in hole order: its type.
        params: []const TyId,
        /// Where `rep`'s image reads a hole.
        slots: rebuild.HoleSlots,
        /// The literals the image reads from its root's region or a region
        /// around it, in site order, which the row builds in its body.
        lits: []const NodeId,
        /// Per node of `rep`'s image, and per literal it copies: the nodes
        /// of the other occurrences it stands for, whose origins its copy
        /// takes too (N10).
        also: collections.DenseMapUnmanaged(NodeId, []const NodeId),
        occurrences: []const Occurrence,
        /// Per occurrence: the nodes of its image but its root, which its
        /// caller does not build.
        images: []const []const NodeId,
    };

    /// One row's occurrences: each root becomes a `Call` of shape `shape`'s
    /// row over its holes, and `skip` holds the nodes only those images read.
    pub const Edit = struct {
        row: RowId,
        calls: []const Call,
        skip: []const NodeId,

        pub const Call = struct { root: NodeId, shape: u32, holes: []const Ref, moved: []const NodeId };
    };

    pub fn deinit(self: *Selection) void {
        self.arena.deinit();
    }
};

/// The size of a site: the rows it reaches, their nodes, literals not
/// counted, and the arguments of their calls.
pub const SiteSize = struct {
    nodes: u32 = 0,
    rows: u32 = 0,
    args: u32 = 0,

    /// What every pass of `outline` lowers (normal-form 5.3): a node weighs
    /// three and an argument one. A take of c places of a generalization of
    /// s nodes and h holes, with a positive gain, so h <= s - 2, lowers it
    /// by at least s(2c - 3) - c, which is above 0 for c >= 2 and s >= 3.
    pub fn measure(self: SiteSize) u64 {
        return 3 * @as(u64, self.nodes) + self.args;
    }
};

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
    var out: SiteSize = .{ .rows = @intCast(reached.count()) };
    for (reached.values()) |numbering| for (numbering.order.items) |n| {
        const nd = store.node(n);
        if (nd.op != .lit) out.nodes += 1;
        if (nd.op == .call) out.args += nd.args.len;
    };
    return out;
}

/// The generalizations one pass of `outline` takes over the site of
/// `root`, whose rows are at `inline` or at an earlier pass, with K =
/// `min_size`.
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

    // Places, sorted by their keys at depths 0 to D, then by the key at
    // depth D with literal values, then in site order.
    const width = outline_key_depth + 2;
    var places: std.ArrayList(u32) = .empty;
    defer places.deinit(gpa);
    for (0..a.count()) |i| {
        if (a.valid[i] and a.size[i] >= min_size) try places.append(gpa, @intCast(i));
    }
    const keys = try gpa.alloc(u64, places.items.len * width);
    defer gpa.free(keys);
    for (places.items, 0..) |i, p| for (0..width) |d| {
        a.key_values = d == width - 1;
        keys[p * width + d] = try a.keyOf(i, @intCast(@min(d, outline_key_depth)));
    };
    a.key_values = false;
    const order = try gpa.alloc(u32, places.items.len);
    defer gpa.free(order);
    for (order, 0..) |*o, p| o.* = @intCast(p);
    const ByKey = struct {
        keys: []const u64,
        width: usize,
        fn less(ctx: @This(), x: u32, y: u32) bool {
            const kx = ctx.keys[x * ctx.width ..][0..ctx.width];
            const ky = ctx.keys[y * ctx.width ..][0..ctx.width];
            for (kx, ky) |p, q| if (p != q) return p < q;
            return x < y;
        }
        // Whether sorted positions `x` and `y` have one key at every depth up to `d`.
        fn same(ctx: @This(), sorted: []const u32, x: usize, y: usize, d: usize) bool {
            const kx = ctx.keys[sorted[x] * ctx.width ..][0 .. d + 1];
            const ky = ctx.keys[sorted[y] * ctx.width ..][0 .. d + 1];
            return std.mem.eql(u64, kx, ky);
        }
    };
    const by_key: ByKey = .{ .keys = keys, .width = width };
    std.mem.sort(u32, order, by_key, ByKey.less);
    const sorted = try gpa.alloc(u32, places.items.len);
    defer gpa.free(sorted);
    for (order, sorted) |p, *s| s.* = places.items[p];

    // Groups: per depth, the runs of one key, each counted once.
    const Group = struct { start: u32, len: u32, depth: u32 };
    var groups: std.ArrayList(Group) = .empty;
    defer groups.deinit(gpa);
    for (0..width) |d| {
        var start: usize = 0;
        while (start < order.len) {
            var end = start + 1;
            while (end < order.len and by_key.same(order, start, end, d)) end += 1;
            const inherited = d > 0 and
                (start == 0 or !by_key.same(order, start - 1, start, d - 1)) and
                (end == order.len or !by_key.same(order, end - 1, end, d - 1));
            if (end - start >= 2 and !inherited) try groups.append(gpa, .{ .start = @intCast(start), .len = @intCast(end - start), .depth = @intCast(d) });
            start = end;
        }
    }

    // Selection: evaluate every group, then take the best whose evaluation
    // is current, evaluating again the ones a take predates.
    a.claimed = try a.scratch.allocator().alloc(bool, a.count());
    @memset(a.claimed, false);
    a.stamp = try a.scratch.allocator().alloc(u32, a.count());
    @memset(a.stamp, 0);
    var gen: Gen = .{ .an = &a };
    defer gen.deinit();
    const Live = struct { group: u32, score: Gen.Score, version: u32 };
    var live: std.ArrayList(Live) = .empty;
    defer live.deinit(gpa);
    for (groups.items, 0..) |g, gi| {
        if (try gen.evaluate(sorted[g.start..][0..g.len], min_size)) |score| try live.append(gpa, .{ .group = @intCast(gi), .score = score, .version = 0 });
    }
    const better = struct {
        fn f(gs: []const Group, srt: []const u32, x: Live, y: Live) bool {
            if (x.score.gain != y.score.gain) return x.score.gain > y.score.gain;
            if (x.score.size != y.score.size) return x.score.size > y.score.size;
            if (x.score.shape != y.score.shape) return x.score.shape < y.score.shape;
            const gx = gs[x.group];
            const gy = gs[y.group];
            if (srt[gx.start] != srt[gy.start]) return srt[gx.start] < srt[gy.start];
            return gx.depth < gy.depth;
        }
    }.f;
    var chosen: std.ArrayList(Selection.Chosen) = .empty;
    // Per local literal: whether a call passes it or a value that moves reads it.
    const lit_used = try a.scratch.allocator().alloc(bool, a.count());
    @memset(lit_used, false);
    var takes: u32 = 0;
    while (live.items.len > 0) {
        var best: usize = 0;
        for (live.items[1..], 1..) |c, ci| {
            if (better(groups.items, sorted, c, live.items[best])) best = ci;
        }
        const c = live.items[best];
        const g = groups.items[c.group];
        const members = sorted[g.start..][0..g.len];
        if (c.version != takes) {
            if (try gen.evaluate(members, min_size)) |score| {
                live.items[best] = .{ .group = c.group, .score = score, .version = takes };
            } else _ = live.swapRemove(best);
            continue;
        }
        _ = live.swapRemove(best);
        // The evaluation is current, so running it again reads its tuples.
        const again = (try gen.evaluate(members, min_size)).?;
        std.debug.assert(std.meta.eql(again, c.score));
        try chosen.append(arena, try gen.take(arena, lit_used));
        takes += 1;
    }
    out.shapes = try chosen.toOwnedSlice(arena);

    // Per row, in site order: the calls, the nodes only the images read,
    // and the literals nothing the caller keeps reads.
    var edits: std.ArrayList(Selection.Edit) = .empty;
    for (a.rows, 0..) |r, row_pos| {
        var calls: std.ArrayList(Selection.Edit.Call) = .empty;
        var skip: std.ArrayList(NodeId) = .empty;
        for (out.shapes, 0..) |shape, s| for (shape.occurrences, 0..) |o, k| {
            if (o.row != r) continue;
            try calls.append(arena, .{ .root = o.root, .shape = @intCast(s), .holes = o.holes, .moved = o.moved });
            try skip.appendSlice(arena, shape.images[k]);
        };
        if (calls.items.len == 0) continue;
        for (a.row_start[row_pos]..a.row_start[row_pos + 1]) |l| {
            if (!a.is_lit[l] or lit_used[l]) continue;
            const read_outside = for (a.anchorsOf(@intCast(l))) |x| {
                if (x == Analysis.top or !a.claimed[x]) break true;
            } else false;
            if (!read_outside) try skip.append(arena, a.nodes.items[l]);
        }
        try edits.append(arena, .{ .row = r, .calls = try calls.toOwnedSlice(arena), .skip = try skip.toOwnedSlice(arena) });
    }
    out.edits = try edits.toOwnedSlice(arena);
    return out;
}

// The cones, keys and validity of every node of a site's rows. Nodes are
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
    /// Per node: whether an occurrence taken in this pass holds it in its image.
    claimed: []bool = &.{},
    /// Per node: the mark of the image being compared (`Gen`).
    stamp: []u32 = &.{},
    stamp_now: u32 = 0,
    // Scratch of `keyOf`, and whether it reads literal values.
    points: std.AutoHashMapUnmanaged(u64, u32) = .empty,
    key_values: bool = false,

    const none: u32 = std.math.maxInt(u32);
    const top: u32 = std.math.maxInt(u32) - 1;

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

    fn unreadOf(self: *const Analysis, r: RegionId) []const u32 {
        return if (self.unread.get(r)) |l| l.items else &.{};
    }

    fn regionDepth(self: *const Analysis, i: u32) u32 {
        return self.store.region(self.node(i).region).depth;
    }

    fn localOf(self: *const Analysis, n: NodeId) u32 {
        const l = self.local[n.index()];
        std.debug.assert(l != none);
        return l;
    }

    fn rowOf(self: *const Analysis, i: u32) RowId {
        return self.rows[self.row_of[i]];
    }

    // The type of `x`, a value of the row of node `at`.
    fn tyAt(self: *const Analysis, at: u32, x: Ref) TyId {
        return self.store.refTy(self.rowOf(at), x);
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

    // Sizes and validity, children before parents.
    fn bottomUp(self: *Analysis) Allocator.Error!void {
        const arena = self.scratch.allocator();
        const store = self.store;
        const total = self.count();
        self.size = try arena.alloc(u32, total);
        self.valid = try arena.alloc(bool, total);
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
            const row = self.rowOf(i);
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

    // Whether `i` is a node of the cone of `root`.
    fn inCone(self: *const Analysis, root: u32, i: u32) bool {
        return !self.is_lit[i] and self.tin[root] <= self.tin[i] and self.tin[i] <= self.tout[root];
    }

    // Whether `x` is a parameter of a region a node of the cone of `root` owns.
    fn boundIn(self: *const Analysis, root: u32, x: Ref) bool {
        if (x.kind != .region_param) return false;
        const owner = self.store.region(x.regionId()).owner;
        return owner != NodeId.none and self.inCone(root, self.localOf(owner));
    }

    // Whether nodes `x` and `y` have one op, payload, types, immediates and
    // region shape, and as many arguments.
    fn sameContent(self: *const Analysis, x: u32, y: u32) bool {
        const store = self.store;
        const nx = self.node(x);
        const ny = self.node(y);
        if (nx.op != ny.op or nx.payload != ny.payload or nx.args.len != ny.args.len) return false;
        if (!std.mem.eql(TyId, store.tySlice(nx.tys), store.tySlice(ny.tys))) return false;
        if (!std.mem.eql(u32, store.wordSlice(nx.aux), store.wordSlice(ny.aux))) return false;
        const rx = store.regionSlice(nx.regions);
        const ry = store.regionSlice(ny.regions);
        if (rx.len != ry.len) return false;
        for (rx, ry) |p, q| {
            const gp = store.region(p);
            const gq = store.region(q);
            if (gp.kind != gq.kind or gp.end.kind != gq.end.kind or gp.end.refs.len != gq.end.refs.len) return false;
            if (!std.mem.eql(TyId, store.tySlice(gp.params), store.tySlice(gq.params))) return false;
            if (self.unreadOf(p).len != self.unreadOf(q).len) return false;
        }
        return true;
    }

    // The digest of node `i`'s own content, a row it calls or names by its
    // name in the site (`digest.siteRowNames`), so no digest reads a row's id.
    fn contentOf(self: *Analysis, i: u32) Allocator.Error!digest_mod.Digest {
        const nd = self.node(i);
        const name: ?digest_mod.Digest = switch (nd.op) {
            .call, .closure => self.names[nd.payload],
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => null,
        };
        return digest_mod.localContent(self.store, &self.content, nd, name);
    }

    const Tag = enum(u32) { lit, ref, child, leaf };

    // The key of place `i` at depth `d` (normal-form 5.3, rule 2): the
    // content of every node of its cone at depth `d` or less, a literal by
    // its type (and its value too under `key_values`), and every other
    // value a leaf by its type and its number in the order the walk first
    // meets it.
    fn keyOf(self: *Analysis, i: u32, d: u32) Allocator.Error!u64 {
        self.points.clearRetainingCapacity();
        var h = std.hash.Wyhash.init(0);
        try self.keyNode(&h, i, i, 0, d);
        return h.final();
    }

    fn keyNode(self: *Analysis, h: *std.hash.Wyhash, root: u32, i: u32, depth: u32, d: u32) Allocator.Error!void {
        const store = self.store;
        const nd = self.node(i);
        putDigest(h, try self.contentOf(i));
        for (store.refSlice(nd.args)) |x| try self.keyRef(h, root, x, depth + 1, d);
        for (store.regionSlice(nd.regions)) |r| {
            const reg = store.region(r);
            putWords(h, &.{ @backingInt(reg.kind), reg.params.len, @backingInt(reg.end.kind), reg.end.refs.len, @intCast(self.unreadOf(r).len) });
            for (store.tySlice(reg.params)) |t| putDigest(h, try self.content.ty(t));
            for (store.refSlice(reg.end.refs)) |x| try self.keyRef(h, root, x, depth + 1, d);
        }
    }

    fn keyRef(self: *Analysis, h: *std.hash.Wyhash, root: u32, x: Ref, depth: u32, d: u32) Allocator.Error!void {
        if (x.kind == .node) {
            const m = self.localOf(x.nodeId());
            if (self.is_lit[m]) {
                putWords(h, &.{ @intFromEnum(Tag.lit), x.output });
                putDigest(h, try self.content.ty(self.tyAt(root, x)));
                if (self.key_values) putDigest(h, try digest_mod.litContent(self.store, &self.content, ir.LitId.of(self.node(m).payload)));
                return;
            }
            if (depth <= d and self.inCone(root, m)) {
                const gop = try self.points.getOrPut(self.gpa, rebuild.refKey(Ref.of(x.nodeId())));
                if (gop.found_existing) return putWords(h, &.{ @intFromEnum(Tag.ref), gop.value_ptr.*, x.output });
                gop.value_ptr.* = self.points.count() - 1;
                putWords(h, &.{ @intFromEnum(Tag.child), x.output });
                return self.keyNode(h, root, m, depth, d);
            }
        }
        const gop = try self.points.getOrPut(self.gpa, rebuild.refKey(x));
        if (gop.found_existing) return putWords(h, &.{ @intFromEnum(Tag.ref), gop.value_ptr.*, 0 });
        gop.value_ptr.* = self.points.count() - 1;
        putWords(h, &.{@intFromEnum(Tag.leaf)});
        putDigest(h, try self.content.ty(self.tyAt(root, x)));
    }
};

// The generalization of a group of places (normal-form 5.3, rules 3 and 4).
// A round walks the places' cones in step and gives each tuple of values,
// one per place, its kind; the rules then name the nodes that must be holes,
// and the rounds repeat until they name none.
const Gen = struct {
    an: *Analysis,
    /// The places, local roots in site order.
    places: std.ArrayList(u32) = .empty,
    /// Per (place position, local node): rule 4 made the node a hole at that place.
    forced: std.AutoHashMapUnmanaged(u64, void) = .empty,
    /// Per tuple: its kind, its values (`places.len` of them, at `values[t *
    /// n ..]`; a tuple of nodes holds each node's first output), and the
    /// number of a hole.
    kinds: std.ArrayList(Class) = .empty,
    values: std.ArrayList(Ref) = .empty,
    numbers: std.ArrayList(u32) = .empty,
    /// Per hash of a tuple's values: the last tuple with it; `chain` links the others.
    memo: std.AutoHashMapUnmanaged(u64, u32) = .empty,
    chain: std.ArrayList(u32) = .empty,
    /// Where each tuple is read: a slot of a tuple of nodes.
    edges: std.ArrayList(Edge) = .empty,
    /// Per (place position, region): the tuple of nodes that owns it, and
    /// the region's position among its owner's regions.
    regions: std.AutoHashMapUnmanaged(u64, u64) = .empty,
    /// The hole tuples, in hole order.
    holes: std.ArrayList(u32) = .empty,
    /// The tuples of nodes.
    size: u32 = 0,
    shape: u128 = 0,
    // Scratch of a round.
    stack: std.ArrayList(Item) = .empty,
    pending: std.ArrayList(Ref) = .empty,
    tuple: std.ArrayList(Ref) = .empty,
    slots: std.ArrayList(Item) = .empty,
    force: std.ArrayList(u64) = .empty,
    owner: std.AutoHashMapUnmanaged(u64, u32) = .empty,
    visited: std.AutoHashMapUnmanaged(u32, void) = .empty,
    work: std.ArrayList(u32) = .empty,
    moves: std.AutoHashMapUnmanaged(u32, bool) = .empty,
    bad: std.AutoHashMapUnmanaged(u32, void) = .empty,
    keep: std.ArrayList(u32) = .empty,

    const Class = enum(u8) { node, lit, param, hole };
    const Slot = enum(u8) { arg, end, branch, unread };
    /// Tuple `child` is read at slot `slot` (`region`, `index`) of tuple `parent`.
    const Edge = struct { parent: u32, slot: Slot, region: u32, index: u32, child: u32 };
    const Item = struct { parent: u32, slot: Slot, region: u32, index: u32, at: u32 };
    const none: u32 = std.math.maxInt(u32);
    const Outcome = enum { dead, again, settled };

    /// What selection orders a candidate by.
    pub const Score = struct { gain: i64, size: u32, holes: u32, shape: u128 };

    fn deinit(self: *Gen) void {
        const gpa = self.an.gpa;
        self.places.deinit(gpa);
        self.forced.deinit(gpa);
        self.kinds.deinit(gpa);
        self.values.deinit(gpa);
        self.numbers.deinit(gpa);
        self.memo.deinit(gpa);
        self.chain.deinit(gpa);
        self.edges.deinit(gpa);
        self.regions.deinit(gpa);
        self.holes.deinit(gpa);
        self.stack.deinit(gpa);
        self.pending.deinit(gpa);
        self.tuple.deinit(gpa);
        self.slots.deinit(gpa);
        self.force.deinit(gpa);
        self.owner.deinit(gpa);
        self.visited.deinit(gpa);
        self.work.deinit(gpa);
        self.moves.deinit(gpa);
        self.bad.deinit(gpa);
        self.keep.deinit(gpa);
    }

    fn n(self: *const Gen) u32 {
        return @intCast(self.places.items.len);
    }

    fn valuesOf(self: *const Gen, t: u32) []const Ref {
        const w = self.n();
        return self.values.items[t * w ..][0..w];
    }

    // The local node tuple `t` of nodes holds at place `k`.
    fn at(self: *const Gen, t: u32, k: u32) u32 {
        return self.an.localOf(self.values.items[t * self.n() + k].nodeId());
    }

    fn key(k: u32, x: u32) u64 {
        return @as(u64, k) << 32 | x;
    }

    /// The score of the generalization of `group`, or null where it is no
    /// candidate. The tuples of the last round stay for `take`.
    fn evaluate(self: *Gen, group: []const u32, min_size: u32) Allocator.Error!?Score {
        const gpa = self.an.gpa;
        const an = self.an;
        self.places.clearRetainingCapacity();
        try self.places.appendSlice(gpa, group);
        while (true) {
            if (self.n() < 2) return null;
            self.forced.clearRetainingCapacity();
            while (true) switch (try self.round()) {
                .dead => return null,
                .again => {},
                .settled => break,
            };
            // A place whose image meets a taken one or an earlier place's leaves.
            self.keep.clearRetainingCapacity();
            an.stamp_now += 1;
            for (0..self.n()) |kk| {
                const k: u32 = @intCast(kk);
                const meets = for (0..self.kinds.items.len) |t| {
                    if (self.kinds.items[t] != .node) continue;
                    const m = self.at(@intCast(t), k);
                    if (an.claimed[m] or an.stamp[m] == an.stamp_now) break true;
                } else false;
                if (meets) continue;
                for (0..self.kinds.items.len) |t| {
                    if (self.kinds.items[t] == .node) an.stamp[self.at(@intCast(t), k)] = an.stamp_now;
                }
                try self.keep.append(gpa, self.places.items[k]);
            }
            if (self.keep.items.len == self.n()) break;
            self.places.clearRetainingCapacity();
            try self.places.appendSlice(gpa, self.keep.items);
        }
        const c: i64 = self.n();
        const s: i64 = self.size;
        const h: i64 = @intCast(self.holes.items.len);
        const gain = c * (s - 1) - c * h;
        if (self.size < min_size or gain <= 0) return null;
        return .{ .gain = gain, .size = self.size, .holes = @intCast(self.holes.items.len), .shape = self.shape };
    }

    // One walk of the places' cones in step, then the rules of rule 4.
    fn round(self: *Gen) Allocator.Error!Outcome {
        const gpa = self.an.gpa;
        const an = self.an;
        const w = self.n();
        self.kinds.clearRetainingCapacity();
        self.values.clearRetainingCapacity();
        self.numbers.clearRetainingCapacity();
        self.memo.clearRetainingCapacity();
        self.chain.clearRetainingCapacity();
        self.edges.clearRetainingCapacity();
        self.regions.clearRetainingCapacity();
        self.holes.clearRetainingCapacity();
        self.stack.clearRetainingCapacity();
        self.pending.clearRetainingCapacity();
        self.force.clearRetainingCapacity();
        self.size = 0;
        var h = Sha256.init(.{});

        self.tuple.clearRetainingCapacity();
        for (self.places.items) |p| try self.tuple.append(gpa, Ref.of(an.nodes.items[p]));
        if (try self.classify(self.tuple.items) != .node) return .dead;
        const root = (try self.intern(self.tuple.items, .node)).t;
        putDigest(&h, try an.contentOf(self.places.items[0]));
        try self.expand(root);
        while (self.stack.pop()) |item| {
            self.tuple.clearRetainingCapacity();
            try self.tuple.appendSlice(gpa, self.pending.items[item.at..][0..w]);
            self.pending.shrinkRetainingCapacity(item.at);
            const refs = self.tuple.items;
            putWords(&h, &.{ @intFromEnum(item.slot), item.region, item.index });
            const kind = (try self.classify(refs)) orelse {
                try self.forceTuple(item.parent);
                continue;
            };
            if ((item.slot == .branch or item.slot == .unread) and kind != .node) {
                try self.forceTuple(item.parent);
                continue;
            }
            const output = refs[0].output;
            if (kind == .node) for (refs) |*x| {
                x.* = Ref.of(x.nodeId());
            };
            const got = try self.intern(refs, kind);
            try self.edges.append(gpa, .{ .parent = item.parent, .slot = item.slot, .region = item.region, .index = item.index, .child = got.t });
            putWords(&h, &.{ @intFromEnum(kind), output });
            switch (kind) {
                .node => if (got.new) {
                    putDigest(&h, try an.contentOf(self.at(got.t, 0)));
                    try self.expand(got.t);
                } else putWords(&h, &.{got.t}),
                .lit => putDigest(&h, try digest_mod.litContent(an.store, &an.content, ir.LitId.of(an.store.node(refs[0].nodeId()).payload))),
                .param => {
                    const owner = self.regions.get(key(0, refs[0].target)).?;
                    putWords(&h, &.{ @truncate(owner >> 32), @truncate(owner) });
                },
                .hole => {
                    putWords(&h, &.{self.numbers.items[got.t]});
                    putDigest(&h, try an.content.ty(an.tyAt(self.places.items[0], refs[0])));
                },
            }
        }
        try self.rules();
        var added: u32 = 0;
        for (self.force.items) |f| {
            const gop = try self.forced.getOrPut(gpa, f);
            if (gop.found_existing) continue;
            added += 1;
            const k: u32 = @truncate(f >> 32);
            if (@as(u32, @truncate(f)) == self.places.items[k]) return .dead;
        }
        if (added > 0) return .again;
        var out: [32]u8 = undefined;
        h.final(&out);
        self.shape = std.mem.readInt(u128, out[0..16], .little);
        return .settled;
    }

    // The kind of a tuple (rule 3), or null where it is no node and cannot
    // be a hole either.
    fn classify(self: *const Gen, refs: []const Ref) Allocator.Error!?Class {
        const an = self.an;
        const store = an.store;
        const places = self.places.items;
        const all_nodes = for (refs) |x| {
            if (x.kind != .node) break false;
        } else true;
        if (all_nodes) {
            const m0 = an.localOf(refs[0].nodeId());
            const all_lits = for (refs) |x| {
                if (!an.is_lit[an.localOf(x.nodeId())]) break false;
            } else true;
            if (all_lits) {
                const v0 = try digest_mod.litContent(store, &an.content, ir.LitId.of(store.node(refs[0].nodeId()).payload));
                const same = for (refs[1..]) |x| {
                    if (x.output != refs[0].output) break false;
                    const v = try digest_mod.litContent(store, &an.content, ir.LitId.of(store.node(x.nodeId()).payload));
                    if (v != v0) break false;
                } else true;
                if (same) return .lit;
            } else {
                const inside = for (refs, places, 0..) |x, p, k| {
                    const m = an.localOf(x.nodeId());
                    if (an.is_lit[m] or !an.inCone(p, m) or self.forced.contains(key(@intCast(k), m))) break false;
                    if (x.output != refs[0].output or !an.sameContent(m0, m)) break false;
                } else true;
                if (inside) return .node;
            }
        }
        // A parameter of a region of the generalization.
        const any_bound = for (refs, places) |x, p| {
            if (an.boundIn(p, x)) break true;
        } else false;
        if (any_bound) {
            for (refs, places, 0..) |x, p, k| {
                if (!an.boundIn(p, x) or x.output != refs[0].output) return null;
                const owner = self.regions.get(key(@intCast(k), x.target)) orelse return null;
                if (owner != self.regions.get(key(0, refs[0].target)).?) return null;
            }
            return .param;
        }
        // A hole: its values have one type.
        const ty = an.tyAt(places[0], refs[0]);
        for (refs[1..], places[1..]) |x, p| if (an.tyAt(p, x) != ty) return null;
        return .hole;
    }

    const Interned = struct { t: u32, new: bool };

    fn intern(self: *Gen, refs: []const Ref, kind: Class) Allocator.Error!Interned {
        const gpa = self.an.gpa;
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(std.mem.sliceAsBytes(refs));
        const hash = hasher.final();
        const gop = try self.memo.getOrPut(gpa, hash);
        if (gop.found_existing) {
            var t = gop.value_ptr.*;
            while (t != none) : (t = self.chain.items[t]) {
                const vs = self.valuesOf(t);
                const same = for (vs, refs) |p, q| {
                    if (rebuild.refKey(p) != rebuild.refKey(q)) break false;
                } else true;
                if (same) {
                    std.debug.assert(self.kinds.items[t] == kind);
                    return .{ .t = t, .new = false };
                }
            }
        }
        const t: u32 = @intCast(self.kinds.items.len);
        try self.kinds.append(gpa, kind);
        try self.values.appendSlice(gpa, refs);
        try self.numbers.append(gpa, if (kind == .hole) @intCast(self.holes.items.len) else 0);
        try self.chain.append(gpa, if (gop.found_existing) gop.value_ptr.* else none);
        gop.value_ptr.* = t;
        switch (kind) {
            .hole => try self.holes.append(gpa, t),
            .node => self.size += 1,
            .lit, .param => {},
        }
        return .{ .t = t, .new = true };
    }

    // The slots of tuple of nodes `t`, pushed so that they pop in order:
    // its arguments, then per region the switch it branches to, its end's
    // values and the nodes nothing reads. A `Jump` must reach one join of
    // the generalization at every place.
    fn expand(self: *Gen, t: u32) Allocator.Error!void {
        const gpa = self.an.gpa;
        const an = self.an;
        const store = an.store;
        const w = self.n();
        const nd0 = an.node(self.at(t, 0));
        const region_count = nd0.regions.len;
        for (0..w) |kk| {
            const k: u32 = @intCast(kk);
            for (store.regionSlice(an.node(self.at(t, k)).regions), 0..) |r, q| try self.regions.put(gpa, key(k, r.index()), key(t, @intCast(q)));
        }
        self.slots.clearRetainingCapacity();
        for (0..nd0.args.len) |j| try self.slots.append(gpa, .{ .parent = t, .slot = .arg, .region = 0, .index = @intCast(j), .at = 0 });
        for (0..region_count) |qq| {
            const q: u32 = @intCast(qq);
            const r0 = store.regionSlice(nd0.regions)[q];
            const end = store.region(r0).end;
            switch (end.kind) {
                .jump => if (self.regions.get(key(0, end.target))) |join| {
                    for (1..w) |kk| {
                        const rk = store.regionSlice(an.node(self.at(t, @intCast(kk))).regions)[q];
                        const other = self.regions.get(key(@intCast(kk), store.region(rk).end.target));
                        if (other == null or other.? != join) {
                            try self.forceTuple(t);
                            break;
                        }
                    }
                } else try self.forceTuple(t),
                .branch => try self.slots.append(gpa, .{ .parent = t, .slot = .branch, .region = q, .index = 0, .at = 0 }),
                .open, .value, .return_, .continue_, .break_ => {},
            }
            for (0..end.refs.len) |j| try self.slots.append(gpa, .{ .parent = t, .slot = .end, .region = q, .index = @intCast(j), .at = 0 });
            for (0..an.unreadOf(r0).len) |j| try self.slots.append(gpa, .{ .parent = t, .slot = .unread, .region = q, .index = @intCast(j), .at = 0 });
        }
        var i = self.slots.items.len;
        while (i > 0) {
            i -= 1;
            var item = self.slots.items[i];
            item.at = @intCast(self.pending.items.len);
            for (0..w) |kk| {
                const nd = an.node(self.at(t, @intCast(kk)));
                const x: Ref = switch (item.slot) {
                    .arg => store.refSlice(nd.args)[item.index],
                    .end => store.refSlice(store.region(store.regionSlice(nd.regions)[item.region]).end.refs)[item.index],
                    .branch => Ref.of(NodeId.of(store.region(store.regionSlice(nd.regions)[item.region]).end.target)),
                    .unread => Ref.of(an.nodes.items[an.unreadOf(store.regionSlice(nd.regions)[item.region])[item.index]]),
                };
                try self.pending.append(gpa, x);
            }
            try self.stack.append(gpa, item);
        }
    }

    // Make tuple of nodes `t` a hole at every place.
    fn forceTuple(self: *Gen, t: u32) Allocator.Error!void {
        for (0..self.n()) |k| try self.force.append(self.an.gpa, key(@intCast(k), self.at(t, @intCast(k))));
    }

    // Rule 4 over the tuples of a round: what it names goes to `force`.
    fn rules(self: *Gen) Allocator.Error!void {
        const gpa = self.an.gpa;
        const an = self.an;
        const store = an.store;
        const w = self.n();
        // A node of a place in two tuples of nodes.
        self.owner.clearRetainingCapacity();
        for (self.kinds.items, 0..) |kind, tt| {
            if (kind != .node) continue;
            const t: u32 = @intCast(tt);
            for (0..w) |kk| {
                const k: u32 = @intCast(kk);
                const gop = try self.owner.getOrPut(gpa, key(k, self.at(t, k)));
                if (gop.found_existing and gop.value_ptr.* != t) try self.force.append(gpa, key(k, self.at(t, k)));
                if (!gop.found_existing) gop.value_ptr.* = t;
            }
        }
        self.bad.clearRetainingCapacity();
        for (self.places.items, 0..) |p, kk| {
            const k: u32 = @intCast(kk);
            // A node a hole's value reads, and a tuple of nodes holds.
            self.visited.clearRetainingCapacity();
            self.work.clearRetainingCapacity();
            for (self.holes.items) |ht| try self.visit(p, self.values.items[ht * w + k]);
            while (self.work.pop()) |m| {
                if (self.owner.contains(key(k, m))) try self.force.append(gpa, key(k, m));
                const nd = an.node(m);
                for (store.refSlice(nd.args)) |x| try self.visit(p, x);
                for (store.regionSlice(nd.regions)) |r| {
                    const end = store.region(r).end;
                    for (store.refSlice(end.refs)) |x| try self.visit(p, x);
                    if (end.kind == .branch) try self.visit(p, Ref.of(NodeId.of(end.target)));
                    for (an.unreadOf(r)) |u| try self.visit(p, Ref.of(an.nodes.items[u]));
                }
            }
            // No speculation: a value outside the root's region must move.
            self.moves.clearRetainingCapacity();
            const home = an.node(p).region;
            for (self.holes.items) |ht| {
                const x = self.values.items[ht * w + k];
                if (x.kind != .node) continue;
                const m = an.localOf(x.nodeId());
                if (an.is_lit[m] or !an.inCone(p, m) or an.node(m).region == home) continue;
                if (!try self.movable(p, m)) try self.bad.put(gpa, ht, {});
            }
        }
        for (self.edges.items) |e| if (self.bad.contains(e.child)) try self.forceTuple(e.parent);
    }

    fn visit(self: *Gen, p: u32, x: Ref) Allocator.Error!void {
        if (x.kind != .node) return;
        const m = self.an.localOf(x.nodeId());
        if (!self.an.inCone(p, m)) return;
        if ((try self.visited.getOrPut(self.an.gpa, m)).found_existing) return;
        try self.work.append(self.an.gpa, m);
    }

    // Whether node `start` of the cone of `p`, outside the root's region,
    // can move to the root's region: it, and every node it reads outside
    // that region, is speculatable, owns no region, and reads no parameter
    // of a region inside the cone.
    fn movable(self: *Gen, p: u32, start: u32) Allocator.Error!bool {
        const gpa = self.an.gpa;
        const an = self.an;
        const store = an.store;
        const home = an.node(p).region;
        if (self.moves.get(start)) |v| return v;
        var stack: std.ArrayList(u32) = .empty;
        defer stack.deinit(gpa);
        try stack.append(gpa, start);
        while (stack.items.len > 0) {
            const m = stack.items[stack.items.len - 1];
            if (self.moves.contains(m)) {
                _ = stack.pop();
                continue;
            }
            const nd = an.node(m);
            var ok = nd.flags.speculatable and nd.regions.len == 0;
            var waiting = false;
            if (ok) for (store.refSlice(nd.args)) |x| {
                if (an.boundIn(p, x)) {
                    ok = false;
                    break;
                }
                if (x.kind != .node) continue;
                const u = an.localOf(x.nodeId());
                if (an.is_lit[u] or !an.inCone(p, u) or an.node(u).region == home) continue;
                if (self.moves.get(u)) |v| {
                    if (!v) {
                        ok = false;
                        break;
                    }
                } else {
                    try stack.append(gpa, u);
                    waiting = true;
                }
            };
            if (waiting and ok) continue;
            try self.moves.put(gpa, m, ok);
            _ = stack.pop();
        }
        return self.moves.get(start).?;
    }

    // The chosen generalization of the last evaluation (normal-form 5.3,
    // rule 7), with its images claimed and the literals its calls and the
    // values that move read marked in `lit_used`.
    fn take(self: *Gen, arena: Allocator, lit_used: []bool) Allocator.Error!Selection.Chosen {
        const gpa = self.an.gpa;
        const an = self.an;
        const store = an.store;
        const w = self.n();
        const places = self.places.items;
        const rep = places[0];

        // The images, and per tuple of nodes the nodes it stands for.
        const images = try arena.alloc([]const NodeId, w);
        for (images, 0..) |*image, kk| {
            const k: u32 = @intCast(kk);
            var list: std.ArrayList(NodeId) = .empty;
            for (self.kinds.items, 0..) |kind, t| {
                if (kind != .node) continue;
                const m = self.at(@intCast(t), k);
                an.claimed[m] = true;
                if (m != places[k]) try list.append(arena, an.nodes.items[m]);
            }
            image.* = try list.toOwnedSlice(arena);
        }
        var nodes: std.AutoHashMapUnmanaged(NodeId, void) = .empty;
        var also: collections.DenseMapUnmanaged(NodeId, []const NodeId) = .empty;
        var needed: std.AutoHashMapUnmanaged(u32, void) = .empty;
        defer needed.deinit(gpa);
        for (self.kinds.items, 0..) |kind, tt| {
            const t: u32 = @intCast(tt);
            const vs = self.valuesOf(t);
            switch (kind) {
                .node, .lit => {},
                .param, .hole => continue,
            }
            const first = vs[0].nodeId();
            if (kind == .node) try nodes.put(arena, first, {}) else try needed.put(gpa, an.localOf(first), {});
            const others = try arena.alloc(NodeId, w - 1);
            for (vs[1..], others) |x, *o| o.* = x.nodeId();
            const gop = try also.getOrPut(arena, first);
            gop.value_ptr.* = if (gop.found_existing) try std.mem.concat(arena, NodeId, &.{ gop.value_ptr.*, others }) else others;
        }

        // Where the representative's image reads each hole.
        var slots: rebuild.HoleSlots = .{};
        for (self.edges.items) |e| {
            if (self.kinds.items[e.child] != .hole) continue;
            const owner = self.at(e.parent, 0);
            const hole = self.numbers.items[e.child];
            switch (e.slot) {
                .arg => try slots.args.put(arena, rebuild.slotKey(an.nodes.items[owner].index(), e.index), hole),
                .end => try slots.ends.put(arena, rebuild.slotKey(store.regionSlice(an.node(owner).regions)[e.region].index(), e.index), hole),
                .branch, .unread => unreachable, // these slots hold only tuples of nodes
            }
        }
        const param_tys = try arena.alloc(TyId, self.holes.items.len);
        for (self.holes.items, param_tys) |ht, *ty| ty.* = an.tyAt(rep, self.valuesOf(ht)[0]);

        // What the row does not build: the cone's nodes outside the image,
        // and the literals in the image's regions it copies no value of.
        an.stamp_now += 1;
        for (self.kinds.items, 0..) |kind, t| {
            if (kind == .node) an.stamp[self.at(@intCast(t), 0)] = an.stamp_now;
        }
        var skip: std.ArrayList(NodeId) = .empty;
        for (an.euler_order[an.tin[rep] .. an.tout[rep] + 1]) |m| {
            if (an.stamp[m] != an.stamp_now) try skip.append(arena, an.nodes.items[m]);
        }
        const home_depth = an.regionDepth(rep);
        var lits: std.ArrayList(NodeId) = .empty;
        const row_pos = an.row_of[rep];
        for (an.row_start[row_pos]..an.row_start[row_pos + 1]) |l| {
            if (!an.is_lit[l]) continue;
            if (needed.contains(@intCast(l))) {
                if (an.regionDepth(@intCast(l)) <= home_depth) try lits.append(arena, an.nodes.items[l]);
                continue;
            }
            const owner = store.region(an.node(@intCast(l)).region).owner;
            if (owner != NodeId.none and an.stamp[an.localOf(owner)] == an.stamp_now) try skip.append(arena, an.nodes.items[l]);
        }

        // Per place: the values of its holes, and the values that move.
        const occurrences = try arena.alloc(Selection.Occurrence, w);
        for (occurrences, places, 0..) |*o, p, kk| {
            const k: u32 = @intCast(kk);
            const holes = try arena.alloc(Ref, self.holes.items.len);
            for (self.holes.items, holes) |ht, *x| x.* = self.values.items[ht * w + k];
            an.stamp_now += 1;
            for (self.kinds.items, 0..) |kind, t| {
                if (kind == .node) an.stamp[self.at(@intCast(t), k)] = an.stamp_now;
            }
            o.* = .{ .row = an.rowOf(p), .root = an.nodes.items[p], .holes = holes, .moved = try self.moved(arena, p, holes, lit_used) };
        }
        return .{
            .rep = occurrences[0],
            .nodes = nodes,
            .skip = try skip.toOwnedSlice(arena),
            .params = param_tys,
            .slots = slots,
            .lits = try lits.toOwnedSlice(arena),
            .also = also,
            .occurrences = occurrences,
            .images = images,
        };
    }

    // The values the caller of place `p` builds just before the call, in
    // site order: the nodes and literals the values of its holes read that
    // stand in a region an image node owns (`stamp`). Every literal a hole
    // passes or such a node reads is marked in `lit_used`.
    fn moved(self: *Gen, arena: Allocator, p: u32, holes: []const Ref, lit_used: []bool) Allocator.Error![]const NodeId {
        const gpa = self.an.gpa;
        const an = self.an;
        const store = an.store;
        const home = an.node(p).region;
        var found: std.ArrayList(u32) = .empty;
        defer found.deinit(gpa);
        self.visited.clearRetainingCapacity();
        self.work.clearRetainingCapacity();
        for (holes) |x| {
            if (x.kind != .node) continue;
            const m = an.localOf(x.nodeId());
            if (an.is_lit[m]) lit_used[m] = true;
            try self.reach(p, m, home);
        }
        while (self.work.pop()) |m| {
            try found.append(gpa, m);
            if (an.is_lit[m]) continue;
            for (store.refSlice(an.node(m).args)) |x| {
                if (x.kind != .node) continue;
                const u = an.localOf(x.nodeId());
                if (an.is_lit[u]) lit_used[u] = true;
                try self.reach(p, u, home);
            }
        }
        std.mem.sort(u32, found.items, {}, std.sort.asc(u32));
        const out = try arena.alloc(NodeId, found.items.len);
        for (found.items, out) |m, *o| o.* = an.nodes.items[m];
        return out;
    }

    // Note node or literal `m` for `moved` when it stands in a region an
    // image node owns.
    fn reach(self: *Gen, p: u32, m: u32, home: RegionId) Allocator.Error!void {
        const an = self.an;
        const region = an.node(m).region;
        if (region == home) return;
        if (!an.is_lit[m] and !an.inCone(p, m)) return;
        const owner = an.store.region(region).owner;
        if (owner == NodeId.none or an.stamp[an.localOf(owner)] != an.stamp_now) return;
        if ((try self.visited.getOrPut(an.gpa, m)).found_existing) return;
        try self.work.append(an.gpa, m);
    }
};

const Sha256 = std.crypto.hash.sha2.Sha256;

fn putWords(h: anytype, ws: []const u32) void {
    h.update(std.mem.sliceAsBytes(ws));
}

fn putDigest(h: anytype, d: digest_mod.Digest) void {
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

const prims = @import("prims.zig");

// V3b: anti-unification. Places that differ in a value are one row when the
// value can be a hole (normal-form 5.3, rules 3 and 4).

// `(((x * x) + 7) * x) & x`, wrapping: four nodes over one value.
fn square(f: *Fixture, x: Ref) Allocator.Error!Ref {
    return pattern(f, x, x);
}

fn pairTy(f: *Fixture) Allocator.Error!TyId {
    const i64_ty = try f.types.intTy(.i64);
    return f.types.recordTy(&.{ .{ .name = "a", .ty = i64_ty }, .{ .name = "b", .ty = i64_ty } });
}

// `square(p0.a) - square(p0.b)`: the places read two fields, and the field
// is a hole. With `reversed`, the places are built in the other order.
fn twoFields(f: *Fixture, reversed: bool) Allocator.Error!RowId {
    const root = try f.b.beginRow(&.{try pairTy(f)}, try f.types.intTy(.i64));
    var parts: [2]Ref = undefined;
    for (0..2) |k| {
        const at = if (reversed) 1 - k else k;
        parts[at] = try square(f, try f.b.field(Ref.rowParam(0), @intCast(at)));
    }
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .minus, &.{ parts[0], parts[1] })} });
    return root;
}

// `square(p0.a) - square(p0.b) - square(p1 - p2)`: three places, and the
// third holes a difference where the others hold a field. (A product would
// not do: N15 flattens `(p1 * p2) * (p1 * p2)` into one chain.)
fn threeFields(f: *Fixture, _: bool) Allocator.Error!RowId {
    const i64_ty = try f.types.intTy(.i64);
    const root = try f.b.beginRow(&.{ try pairTy(f), i64_ty, i64_ty }, i64_ty);
    const x = try square(f, try f.b.field(Ref.rowParam(0), 0));
    const y = try square(f, try f.b.field(Ref.rowParam(0), 1));
    const z = try square(f, try f.b.call(.i64, .minus, &.{ Ref.rowParam(1), Ref.rowParam(2) }));
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .minus, &.{ try f.b.call(.i64, .minus, &.{ x, y }), z })} });
    return root;
}

// `pattern(p0.a, p1) - pattern(p0.b, p1)`: `p1` is one value at both places.
fn oneSharedHole(f: *Fixture, _: bool) Allocator.Error!RowId {
    const i64_ty = try f.types.intTy(.i64);
    const root = try f.b.beginRow(&.{ try pairTy(f), i64_ty }, i64_ty);
    const x = try pattern(f, try f.b.field(Ref.rowParam(0), 0), Ref.rowParam(1));
    const y = try pattern(f, try f.b.field(Ref.rowParam(0), 1), Ref.rowParam(1));
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .minus, &.{ x, y })} });
    return root;
}

// `pattern(p0, p0) - pattern(p1, p2)`: one place reads one value twice
// where the other reads two.
fn sharingDiffers(f: *Fixture, _: bool) Allocator.Error!RowId {
    const root = try f.b.beginRow(&try params(f, 3), try f.types.intTy(.i64));
    const x = try pattern(f, Ref.rowParam(0), Ref.rowParam(0));
    const y = try pattern(f, Ref.rowParam(1), Ref.rowParam(2));
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .minus, &.{ x, y })} });
    return root;
}

// `((((a * b) + lit) * a) & b) ^ a`, wrapping: five nodes and a literal.
fn withLit(f: *Fixture, a: Ref, b: Ref, lit: i64) Allocator.Error!Ref {
    const i64_ty = try f.types.intTy(.i64);
    const ab = try f.b.call(.i64, .times_wrap, &.{ a, b });
    const plus = try f.b.call(.i64, .plus_wrap, &.{ ab, try f.b.litInt(i64_ty, lit) });
    const again = try f.b.call(.i64, .times_wrap, &.{ plus, a });
    const both = try f.b.call(.i64, .bitwise_and, &.{ again, b });
    return f.b.call(.i64, .bitwise_xor, &.{ both, a });
}

// `withLit(p0, p1, 7) - withLit(p2, p3, 9)`: the literals differ.
fn twoLiterals(f: *Fixture, _: bool) Allocator.Error!RowId {
    const root = try f.b.beginRow(&try params(f, 4), try f.types.intTy(.i64));
    const x = try withLit(f, Ref.rowParam(0), Ref.rowParam(1), 7);
    const y = try withLit(f, Ref.rowParam(2), Ref.rowParam(3), 9);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .minus, &.{ x, y })} });
    return root;
}

// `pattern(s, a)` over `s = if a == 0 { 0 } else { d(a, b) + 1 }`, where
// `d` is `*` at the first place and `|` at the second when `speculatable`,
// and the checked `*` and `-` otherwise. The places differ only in `d`,
// which stands in an arm.
fn armed(f: *Fixture, speculatable: bool) Allocator.Error!RowId {
    const i64_ty = try f.types.intTy(.i64);
    const root = try f.b.beginRow(&try params(f, 4), i64_ty);
    var parts: [2]Ref = undefined;
    for (&parts, 0..) |*part, k| {
        const a = Ref.rowParam(@intCast(2 * k));
        const b = Ref.rowParam(@intCast(2 * k + 1));
        const zero = try f.b.litInt(i64_ty, 0);
        const done = try f.b.call(.i64, .is_eq, &.{ a, zero });
        const arm0 = try f.b.openArm(done, 0);
        const method: prims.Method = if (speculatable) (if (k == 0) .times_wrap else .bitwise_or) else (if (k == 0) .times else .minus);
        const d = try f.b.call(.i64, method, &.{ a, b });
        try f.b.close(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ d, try f.b.litInt(i64_ty, 1) })} });
        const arm1 = try f.b.openArm(done, 1);
        try f.b.close(.{ .value = &.{zero} });
        const s = try f.b.switchOn(done, &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{});
        part.* = try pattern(f, s, a);
    }
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .minus, &.{ parts[0], parts[1] })} });
    return root;
}

fn armedSpeculatable(f: *Fixture, _: bool) Allocator.Error!RowId {
    return armed(f, true);
}

fn armedChecked(f: *Fixture, _: bool) Allocator.Error!RowId {
    return armed(f, false);
}

test "V3b: two places that read different fields are one row, and each passes its field" {
    try expectOutline(twoFields, false, null,
        \\row r0 ({ a : I64, b : I64 }) -> I64
        \\  n0 = field 0(p0) : I64
        \\  n1 = call r1(n0) : I64
        \\  n2 = field 1(p0) : I64
        \\  n3 = call r1(n2) : I64
        \\  n4 = Num.I64.minus(n1, n3) : I64 !spec
        \\  value n4
        \\row r1 (I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p0) : I64
        \\  n1 = 7 : I64
        \\  n2 = Num.I64.plus_wrap(n0, n1) : I64
        \\  n3 = Num.I64.times_wrap(n2, p0) : I64
        \\  n4 = Num.I64.bitwise_and(n3, p0) : I64
        \\  value n4
        \\
    );
}

test "V3b: three places generalize together, a field at two and a difference at the third" {
    try expectOutline(threeFields, false, null,
        \\row r0 ({ a : I64, b : I64 }, I64, I64) -> I64
        \\  n0 = field 0(p0) : I64
        \\  n1 = call r1(n0) : I64
        \\  n2 = field 1(p0) : I64
        \\  n3 = call r1(n2) : I64
        \\  n4 = Num.I64.minus(n1, n3) : I64 !spec
        \\  n5 = Num.I64.minus(p1, p2) : I64 !spec
        \\  n6 = call r1(n5) : I64
        \\  n7 = Num.I64.minus(n4, n6) : I64 !spec
        \\  value n7
        \\row r1 (I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p0) : I64
        \\  n1 = 7 : I64
        \\  n2 = Num.I64.plus_wrap(n0, n1) : I64
        \\  n3 = Num.I64.times_wrap(n2, p0) : I64
        \\  n4 = Num.I64.bitwise_and(n3, p0) : I64
        \\  value n4
        \\
    );
}

test "V3b: a hole that is one value at every place is one parameter" {
    try expectOutline(oneSharedHole, false, null,
        \\row r0 ({ a : I64, b : I64 }, I64) -> I64
        \\  n0 = field 0(p0) : I64
        \\  n1 = call r1(n0, p1) : I64
        \\  n2 = field 1(p0) : I64
        \\  n3 = call r1(n2, p1) : I64
        \\  n4 = Num.I64.minus(n1, n3) : I64 !spec
        \\  value n4
        \\row r1 (I64, I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p1) : I64
        \\  n1 = 7 : I64
        \\  n2 = Num.I64.plus_wrap(n0, n1) : I64
        \\  n3 = Num.I64.times_wrap(n2, p0) : I64
        \\  n4 = Num.I64.bitwise_and(n3, p1) : I64
        \\  value n4
        \\
    );
}

test "V3b: a place that reads one value twice passes it twice where the other passes two" {
    try expectOutline(sharingDiffers, false, null,
        \\row r0 (I64, I64, I64) -> I64
        \\  n0 = call r1(p0, p0) : I64
        \\  n1 = call r1(p1, p2) : I64
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
    try expectViewsAgree(sharingDiffers, &.{ &.{ 1, 2, 3 }, &.{ -5, 7, 0 }, &.{ 123456789, -987654321, 42 } });
}

test "V3b: literals that differ are a hole, and the node that reads them stays in the row" {
    try expectOutline(twoLiterals, false, null,
        \\row r0 (I64, I64, I64, I64) -> I64
        \\  n0 = 7 : I64
        \\  n1 = call r1(p0, p1, n0) : I64
        \\  n2 = 9 : I64
        \\  n3 = call r1(p2, p3, n2) : I64
        \\  n4 = Num.I64.minus(n1, n3) : I64 !spec
        \\  value n4
        \\row r1 (I64, I64, I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p1) : I64
        \\  n1 = Num.I64.plus_wrap(n0, p2) : I64
        \\  n2 = Num.I64.times_wrap(n1, p0) : I64
        \\  n3 = Num.I64.bitwise_and(n2, p1) : I64
        \\  n4 = Num.I64.bitwise_xor(n3, p0) : I64
        \\  value n4
        \\
    );
    try expectViewsAgree(twoLiterals, &inputs4);
}

test "V3b: a speculatable value in an arm moves before the call, and the switch stays in the row" {
    // `a == 0` is a switch on `a` (N7), so the row switches on its first parameter.
    try expectOutline(armedSpeculatable, false, null,
        \\row r0 (I64, I64, I64, I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p1) : I64
        \\  n1 = call r1(p0, n0) : I64
        \\  n2 = Num.I64.bitwise_or(p2, p3) : I64
        \\  n3 = call r1(p2, n2) : I64
        \\  n4 = Num.I64.minus(n1, n3) : I64 !spec
        \\  value n4
        \\row r1 (I64, I64) -> I64
        \\  n3 = switch p0 : I64
        \\    arm 0
        \\      n0 = 0 : I64
        \\      value n0
        \\    default
        \\      n1 = 1 : I64
        \\      n2 = Num.I64.plus_wrap(p1, n1) : I64
        \\      value n2
        \\  n4 = Num.I64.times_wrap(n3, p0) : I64
        \\  n5 = 7 : I64
        \\  n6 = Num.I64.plus_wrap(n4, n5) : I64
        \\  n7 = Num.I64.times_wrap(n6, n3) : I64
        \\  n8 = Num.I64.bitwise_and(n7, p0) : I64
        \\  value n8
        \\
    );
    try expectViewsAgree(armedSpeculatable, &.{ &.{ 0, 2, 3, 4 }, &.{ -5, 7, 0, 11 }, &.{ 123456789, -987654321, 42, -1 } });
}

test "V3b: a value in an arm that can crash does not move, so the switch is a hole" {
    try expectOutline(armedChecked, false, null,
        \\row r0 (I64, I64, I64, I64) -> I64
        \\  n0 = 0 : I64
        \\  n4 = switch p0 : I64 !spec
        \\    arm 0
        \\      value n0
        \\    default
        \\      n1 = Num.I64.times(p0, p1) : I64 !spec
        \\      n2 = 1 : I64
        \\      n3 = Num.I64.plus_wrap(n1, n2) : I64
        \\      value n3
        \\  n5 = call r1(n4, p0) : I64
        \\  n9 = switch p2 : I64 !spec
        \\    arm 0
        \\      value n0
        \\    default
        \\      n6 = Num.I64.minus(p2, p3) : I64 !spec
        \\      n7 = 1 : I64
        \\      n8 = Num.I64.plus_wrap(n6, n7) : I64
        \\      value n8
        \\  n10 = call r1(n9, p2) : I64
        \\  n11 = Num.I64.minus(n5, n10) : I64 !spec
        \\  value n11
        \\row r1 (I64, I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p1) : I64
        \\  n1 = 7 : I64
        \\  n2 = Num.I64.plus_wrap(n0, n1) : I64
        \\  n3 = Num.I64.times_wrap(n2, p0) : I64
        \\  n4 = Num.I64.bitwise_and(n3, p1) : I64
        \\  value n4
        \\
    );
    try expectViewsAgree(armedChecked, &.{ &.{ 0, 2, 3, 4 }, &.{ -5, 7, 0, 11 }, &.{ 1234, -9876, 42, -1 } });
}

test "L6 V3b: the generalization does not depend on the build order or on how placement breaks ties" {
    var want: std.Io.Writer.Allocating = .init(testing.allocator);
    defer want.deinit();
    {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        const root = try twoFields(&f, false);
        _ = try driver.runTo(testing.allocator, &f.b, root, &.{}, .outline);
        try dump.dumpSite(&want.writer, testing.allocator, &f.store, &f.types, root);
    }
    for (0..16) |seed| {
        var prng = std.Random.DefaultPrng.init(seed);
        try expectOutline(twoFields, seed % 2 == 1, prng.random(), want.written());
    }
}

test "V3b: every pass lowers the site's measure, and the passes end" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const root = try nested(&f, false);
    const stats = try driver.runTo(testing.allocator, &f.b, root, &.{}, .outline);
    try testing.expectEqual(@as(u32, 2), stats.outline_passes);
    try testing.expect(stats.outline_size.measure() < stats.inline_size.measure());
    try testing.expect(stats.outline_size.nodes < stats.inline_size.nodes);
    // A further pass takes nothing.
    var again = try outlineSelect(testing.allocator, &f.store, &f.types, root, outline_min_size);
    defer again.deinit();
    try testing.expectEqual(@as(usize, 0), again.shapes.len);
}
