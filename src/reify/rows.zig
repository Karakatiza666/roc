//! Rows at finalize (N8e, N8f, N8g; normal-form 3.8, plan 3.5).
//!
//! | Step | Does |
//! |---|---|
//! | N8e | the call graph and its components, over what the rows' bodies reach; a component that no longer is one splits into its parts |
//! | N9 at finalize | switch outputs and joins in the order the walk reads them, so the steps below read a canonical row |
//! | N8f | every row whose parameters are not fixed takes them in the order the walk first reads each, and drops the ones it does not read; every `Call` of it is permuted to match, and a `Closure` of it goes through a row that keeps the closure's calling convention |
//! | N8g | the row's digest, a component's by partition refinement; bisimilar members merge, and a row whose digest a finalized row has, confirmed structurally, merges into it |
//!
//! A component is finalized before any caller is simplified (normal-form
//! 3.0), so every `Call` and `Closure` a caller holds is rewritten here, in
//! place, before the caller's first round. A merged row stays in the store
//! with nothing naming it.

const std = @import("std");
const collections = @import("collections");
const ir = @import("ir.zig");
const live_mod = @import("live.zig");
const place = @import("place.zig");
const rebuild = @import("rebuild.zig");
const number = @import("number.zig");
const digest_mod = @import("digest.zig");
const equal = @import("equal.zig");
const types_mod = @import("types.zig");
const builder_mod = @import("builder.zig");
const provenance = @import("provenance.zig");

const Allocator = std.mem.Allocator;
const Ref = ir.Ref;
const NodeId = ir.NodeId;
const RowId = ir.RowId;
const TyId = ir.TyId;
const Digest = digest_mod.Digest;
const Builder = builder_mod.Builder;

/// Why finalize stopped: a compiler bug.
pub const Error = error{InvariantBroken} || Allocator.Error;

/// Which references are edges of the graph.
pub const Edges = enum {
    /// `Call` only: the graph whose cycles make a row recursive.
    calls,
    /// `Call` and `Closure`: the order rows are finalized in, because a
    /// row's digest names every row it refers to by that row's digest.
    references,
};

/// Per row: the rows its live `Call` nodes, and with `references` its live
/// `Closure` nodes, name. A merged row has none. The caller frees it with
/// `freeGraph`.
pub fn graph(gpa: Allocator, store: *const ir.Store, edges: Edges) Allocator.Error![]std.ArrayList(RowId) {
    const out = try gpa.alloc(std.ArrayList(RowId), store.rows.items.len);
    for (out) |*c| c.* = .empty;
    errdefer freeGraph(gpa, out);
    var live = try live_mod.ofStore(gpa, store);
    defer live.deinit(gpa);
    const regions = store.nodes.items(.region);
    for (store.nodes.items(.op), store.nodes.items(.payload), regions, live.nodes) |op, payload, r, l| {
        if (!l) continue;
        switch (op) {
            .call => {},
            .closure => if (edges == .calls) continue,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => continue,
        }
        const from = store.region(r).row;
        if (store.row(from).merged_into != null) continue;
        const list = &out[from.index()];
        if (std.mem.findScalar(RowId, list.items, RowId.of(payload)) == null) try list.append(gpa, RowId.of(payload));
    }
    return out;
}

/// Free a graph that `graph` built.
pub fn freeGraph(gpa: Allocator, g: []std.ArrayList(RowId)) void {
    for (g) |*c| c.deinit(gpa);
    gpa.free(g);
}

/// The strongly connected components of `g` among `members`, callee first
/// (Tarjan's algorithm, whose output order is already reverse topological),
/// each sorted by row id. The caller frees each and the slice.
pub fn components(gpa: Allocator, g: []const std.ArrayList(RowId), members: []const RowId) Allocator.Error![][]RowId {
    const n = g.len;
    var t: Tarjan = .{ .gpa = gpa, .callees = g };
    t.in = try gpa.alloc(bool, n);
    defer gpa.free(t.in);
    @memset(t.in, false);
    for (members) |m| t.in[m.index()] = true;
    t.index = try gpa.alloc(?u32, n);
    defer gpa.free(t.index);
    @memset(t.index, null);
    t.low = try gpa.alloc(u32, n);
    defer gpa.free(t.low);
    t.on_stack = try gpa.alloc(bool, n);
    defer gpa.free(t.on_stack);
    @memset(t.on_stack, false);
    defer t.stack.deinit(gpa);
    errdefer {
        for (t.out.items) |c| gpa.free(c);
        t.out.deinit(gpa);
    }
    for (members) |m| if (t.index[m.index()] == null) try t.visit(m.index());
    return t.out.toOwnedSlice(gpa);
}

/// Free the components that `components` returned.
pub fn freeComponents(gpa: Allocator, comps: [][]RowId) void {
    for (comps) |c| gpa.free(c);
    gpa.free(comps);
}

const Tarjan = struct {
    gpa: Allocator,
    callees: []const std.ArrayList(RowId),
    in: []bool = &.{},
    index: []?u32 = &.{},
    low: []u32 = &.{},
    on_stack: []bool = &.{},
    stack: std.ArrayList(u32) = .empty,
    next: u32 = 0,
    out: std.ArrayList([]RowId) = .empty,

    fn visit(self: *Tarjan, v: u32) Allocator.Error!void {
        self.index[v] = self.next;
        self.low[v] = self.next;
        self.next += 1;
        try self.stack.append(self.gpa, v);
        self.on_stack[v] = true;
        for (self.callees[v].items) |w_row| {
            const w = w_row.index();
            if (!self.in[w]) continue;
            if (self.index[w] == null) {
                try self.visit(w);
                self.low[v] = @min(self.low[v], self.low[w]);
            } else if (self.on_stack[w]) {
                self.low[v] = @min(self.low[v], self.index[w].?);
            }
        }
        if (self.low[v] != self.index[v].?) return;
        var comp: std.ArrayList(RowId) = .empty;
        errdefer comp.deinit(self.gpa);
        while (true) {
            const w = self.stack.pop().?;
            self.on_stack[w] = false;
            try comp.append(self.gpa, RowId.of(w));
            if (w == v) break;
        }
        std.mem.sort(RowId, comp.items, {}, rowLess);
        try self.out.append(self.gpa, try comp.toOwnedSlice(self.gpa));
    }
};

fn rowLess(_: void, a: RowId, b: RowId) bool {
    return a.index() < b.index();
}

/// The parts of `comp` once its fixpoint ended (N8e): one part when it is
/// still one component, and otherwise its components, callee first.
pub fn parts(gpa: Allocator, store: *const ir.Store, comp: []const RowId) Allocator.Error![][]RowId {
    const g = try graph(gpa, store, .references);
    defer freeGraph(gpa, g);
    return components(gpa, g, comp);
}

/// What finalize keeps across components: per digest, the finalized row
/// that holds it.
pub const Finalizer = struct {
    gpa: Allocator,
    registry: std.AutoHashMapUnmanaged(Digest, RowId) = .empty,
    /// The site's root, which keeps its parameters and is never merged away.
    root: RowId,
    /// How placement breaks ties (`place.Ties`).
    ties: place.Ties = .lowest,
    /// The cap on the turns that put a row's outputs and joins in order.
    max_turns: u32,
    /// Per row N8f renumbered: its parameters by old index, in their new
    /// order. A call built after the row was finalized, over the old order,
    /// reads it (a specialization, N8i).
    orders: collections.DenseMapUnmanaged(RowId, []u32) = .empty,

    pub fn deinit(self: *Finalizer) void {
        self.registry.deinit(self.gpa);
        var it = self.orders.valueIterator();
        while (it.next()) |o| self.gpa.free(o.*);
        self.orders.deinit(self.gpa);
    }

    /// The new order of `r`'s parameters, by old index, where N8f
    /// renumbered them, and null where it kept them.
    pub fn orderOf(self: *const Finalizer, r: RowId) ?[]const u32 {
        return self.orders.get(r);
    }

    /// Finalize `comp`, one component that did not split, whose fixpoint ended.
    pub fn finalize(self: *Finalizer, b: *Builder, comp: []const RowId) Error!void {
        for (comp) |r| try self.orderRow(b, r);
        const wrappers = try self.renumber(b, comp);
        defer self.gpa.free(wrappers);
        const all = try std.mem.concat(self.gpa, RowId, &.{ comp, wrappers });
        defer self.gpa.free(all);
        const g = try graph(self.gpa, b.store, .references);
        defer freeGraph(self.gpa, g);
        const comps = try components(self.gpa, g, all);
        defer freeComponents(self.gpa, comps);
        for (comps) |part| try self.identify(b.store, part);
    }

    // N9 over one row: its switch outputs and joins in the order the walk
    // reads them, until the numbering is a fixpoint. Placement is the
    // simplify stage's, so the row stays settled.
    fn orderRow(self: *Finalizer, b: *Builder, r: RowId) Error!void {
        const store = b.store;
        var turns: u32 = 0;
        while (true) : (turns += 1) {
            var returns = try live_mod.Returns.init(self.gpa, store);
            defer returns.deinit(self.gpa);
            var numbering = try number.ofRow(self.gpa, store, &returns, r);
            defer numbering.deinit(self.gpa);
            if (number.inOrder(store, &numbering)) return;
            if (turns == self.max_turns) return error.InvariantBroken;
            var p = try place.planWith(self.gpa, store, &returns, r, .simplify, self.ties);
            defer p.deinit();
            try rebuild.run(self.gpa, b, &p, .{ .raw = true, .outputs = &numbering.outputs, .joins = &numbering.joins });
        }
    }

    // N8f over a component: the rows whose parameters are not fixed take
    // them in first-read order. Returns the rows it built to give closures
    // of those rows their calling convention, which the caller finalizes
    // with the component.
    fn renumber(self: *Finalizer, b: *Builder, comp: []const RowId) Error![]RowId {
        const gpa = self.gpa;
        const store = b.store;
        // Per row of the component: its parameters by old index, in their new order.
        var orders: ir.RowTable([]u32) = .empty;
        defer {
            for (orders.values()) |o| gpa.free(o);
            orders.deinit(gpa);
        }
        for (comp) |r| {
            if (store.row(r).fixed_params) continue;
            var returns = try live_mod.Returns.init(gpa, store);
            defer returns.deinit(gpa);
            var numbering = try number.ofRow(gpa, store, &returns, r);
            defer numbering.deinit(gpa);
            const read = numbering.params.items;
            const identity = read.len == store.row(r).params.len and for (read, 0..) |k, i| {
                if (k != i) break false;
            } else true;
            if (identity) continue;
            try orders.put(gpa, r, try gpa.dupe(u32, read));
        }
        if (orders.count() == 0) return &.{};
        for (orders.keys(), orders.values()) |r, o| try self.orders.put(gpa, r, try gpa.dupe(u32, o));

        // The closures that name a renumbered row, read before anything changes.
        var closures: std.ArrayList(NodeId) = .empty;
        defer closures.deinit(gpa);
        {
            var live = try live_mod.ofStore(gpa, store);
            defer live.deinit(gpa);
            for (store.nodes.items(.op), store.nodes.items(.payload), live.nodes, 0..) |op, payload, l, i| {
                if (l and op == .closure and orders.contains(RowId.of(payload))) try closures.append(gpa, NodeId.of(@intCast(i)));
            }
        }
        // Old parameter types, which a closure's convention keeps.
        var old_params: collections.DenseMapUnmanaged(RowId, []TyId) = .empty;
        defer {
            var it = old_params.valueIterator();
            while (it.next()) |v| gpa.free(v.*);
            old_params.deinit(gpa);
        }
        for (orders.keys()) |r| try old_params.put(gpa, r, try gpa.dupe(TyId, store.tySlice(store.row(r).params)));

        // Every call of a renumbered row, anywhere, passes its arguments in the new order.
        for (store.nodes.items(.op), 0..) |op, i| {
            if (op != .call) continue;
            const order = orders.get(RowId.of(store.nodes.items(.payload)[i])) orelse continue;
            const old = try gpa.dupe(Ref, store.refSlice(store.nodes.items(.args)[i]));
            defer gpa.free(old);
            const new = try gpa.alloc(Ref, order.len);
            defer gpa.free(new);
            for (order, new) |k, *o| o.* = old[k];
            store.nodes.items(.args)[i] = try store.addRefs(new);
        }
        for (orders.keys(), orders.values()) |r, order| {
            const old = old_params.get(r).?;
            const tys = try gpa.alloc(TyId, order.len);
            defer gpa.free(tys);
            for (order, tys) |k, *t| t.* = old[k];
            store.rows.items[r.index()].params = try store.addTys(tys);
        }

        // A closure of a renumbered row: its captures in the row's new order,
        // and where the row's parameters do not stay the captures followed by
        // the function's own parameters in their order, a row that keeps the
        // closure's convention and calls the renumbered one.
        var wrappers: std.ArrayList(RowId) = .empty;
        errdefer wrappers.deinit(gpa);
        var made: std.AutoHashMapUnmanaged([2]u32, RowId) = .empty;
        defer made.deinit(gpa);
        for (closures.items) |c| {
            const nd = store.node(c);
            const r = RowId.of(nd.payload);
            const order = orders.get(r).?;
            const old = old_params.get(r).?;
            const captures: u32 = nd.args.len;
            const caps = try gpa.dupe(Ref, store.refSlice(nd.args));
            defer gpa.free(caps);
            // The captures the row still reads, in its new order.
            var kept: std.ArrayList(u32) = .empty;
            defer kept.deinit(gpa);
            for (order) |k| if (k < captures) try kept.append(gpa, k);
            const direct = order.len == old.len and for (order[kept.items.len..], captures..) |k, want| {
                if (k != want) break false;
            } else true;
            const target = if (direct) r else blk: {
                const gop = try made.getOrPut(gpa, .{ r.index(), captures });
                if (!gop.found_existing) {
                    gop.value_ptr.* = try self.conventionRow(b, r, order, old, captures, kept.items);
                    try wrappers.append(gpa, gop.value_ptr.*);
                }
                break :blk gop.value_ptr.*;
            };
            const args = try gpa.alloc(Ref, kept.items.len);
            defer gpa.free(args);
            for (kept.items, args) |k, *a| a.* = caps[k];
            store.nodes.items(.payload)[c.index()] = target.index();
            store.nodes.items(.args)[c.index()] = try store.addRefs(args);
        }

        // The bodies read their parameters by their new indices.
        for (orders.keys(), orders.values()) |r, order| {
            const map = try gpa.alloc(?u32, old_params.get(r).?.len);
            defer gpa.free(map);
            @memset(map, null);
            for (order, 0..) |k, i| map[k] = @intCast(i);
            var returns = try live_mod.Returns.init(gpa, store);
            defer returns.deinit(gpa);
            var p = try place.planWith(gpa, store, &returns, r, .simplify, self.ties);
            defer p.deinit();
            try rebuild.run(gpa, b, &p, .{ .raw = true, .row_params = map });
        }
        return wrappers.toOwnedSlice(gpa);
    }

    // The row a closure of `r` calls through: the captures `r` reads, in
    // `r`'s order, then the function's own parameters in their order, and a
    // body that calls `r` over them.
    fn conventionRow(self: *Finalizer, b: *Builder, r: RowId, order: []const u32, old: []const TyId, captures: u32, kept: []const u32) Error!RowId {
        const gpa = self.gpa;
        const own = old.len - captures;
        const tys = try gpa.alloc(TyId, kept.len + own);
        defer gpa.free(tys);
        for (kept, tys[0..kept.len]) |k, *t| t.* = old[k];
        @memcpy(tys[kept.len..], old[captures..]);
        const w = try b.beginRow(tys, b.store.row(r).result);
        b.store.rows.items[w.index()].fixed_params = true;
        const args = try gpa.alloc(Ref, order.len);
        defer gpa.free(args);
        for (order, args) |k, *a| {
            a.* = if (k < captures)
                Ref.rowParam(@intCast(std.mem.findScalar(u32, kept, k).?))
            else
                Ref.rowParam(@intCast(kept.len + (k - captures)));
        }
        const call = try b.callRow(r, args);
        try b.endRow(.{ .value = &.{call} });
        return w;
    }

    // N8g over one part: its digests, the merge of bisimilar members, and
    // the merge into a finalized part with the same digests.
    fn identify(self: *Finalizer, store: *ir.Store, part: []const RowId) Error!void {
        const gpa = self.gpa;
        const digests = try gpa.alloc(Digest, part.len);
        defer gpa.free(digests);
        try refine(gpa, store, part, digests);
        // Bisimilar members merge into one: the root where it is one of
        // them, and otherwise the lowest.
        var reps: std.ArrayList(RowId) = .empty;
        defer reps.deinit(gpa);
        const classes: ClassPairing = .{ .part = part, .digests = digests };
        for (part, digests, 0..) |r, d, i| {
            if (std.mem.findScalar(Digest, digests[0..i], d) != null) continue;
            var rep = r;
            for (part[i..], digests[i..]) |q, e| {
                if (e == d and q == self.root) rep = q;
            }
            for (part[i..], digests[i..]) |q, e| {
                if (e != d or q == rep) continue;
                if (!try sameRow(gpa, store, rep, q, classes.pairing())) return error.InvariantBroken;
                try mergeInto(gpa, store, q, rep);
            }
            try reps.append(gpa, rep);
        }
        std.mem.sort(RowId, reps.items, {}, rowLess);
        const quotient = try gpa.alloc(Digest, reps.items.len);
        defer gpa.free(quotient);
        try refine(gpa, store, reps.items, quotient);

        // A part that a finalized part already computes merges into it,
        // member by member; the root keeps its own row.
        const hits = try gpa.alloc(?RowId, reps.items.len);
        defer gpa.free(hits);
        for (quotient, hits) |d, *h| h.* = self.registry.get(d);
        const all_hit = for (hits) |h| {
            if (h == null) break false;
        } else true;
        if (all_hit) {
            const pairing: MapPairing = .{ .from = reps.items, .to = hits };
            for (reps.items, hits) |r, h| {
                if (!try sameRow(gpa, store, r, h.?, pairing.pairing())) return error.InvariantBroken;
            }
            for (reps.items, hits) |r, h| if (r != self.root) try mergeInto(gpa, store, r, h.?);
            if (std.mem.findScalar(RowId, reps.items, self.root) == null) return;
            // The root now calls the finalized part, so its digest is its own.
            var d: [1]Digest = undefined;
            try refine(gpa, store, &.{self.root}, &d);
            store.rows.items[self.root.index()].digest = d[0];
            return setRecursive(gpa, store, &.{self.root});
        }
        for (reps.items, quotient) |r, d| {
            store.rows.items[r.index()].digest = d;
            if (r != self.root) {
                const gop = try self.registry.getOrPut(gpa, d);
                if (!gop.found_existing) gop.value_ptr.* = r;
            }
        }
        try setRecursive(gpa, store, reps.items);
    }
};

// Partition refinement over `part` (normal-form 3.8): each round digests
// every member with a reference to a member named by that member's digest
// of the round before, starting from one name for all, until the number of
// classes stops growing. Members still tied are bisimilar. A reference
// outside the part names the finalized row's digest.
fn refine(gpa: Allocator, store: *const ir.Store, part: []const RowId, out: []Digest) Error!void {
    const names = try gpa.alloc(Digest, part.len);
    defer gpa.free(names);
    @memset(names, 0);
    var classes: usize = 1;
    var rounds: usize = 0;
    while (true) : (rounds += 1) {
        var namer: PartNamer = .{ .store = store, .part = part, .names = names };
        for (part, out) |r, *d| d.* = try digest_mod.ofRow(gpa, store, r, namer.namer());
        if (namer.missing) return error.InvariantBroken;
        const now = distinct(out);
        if (now == classes and rounds > 0) return;
        if (rounds > part.len) return error.InvariantBroken;
        classes = now;
        @memcpy(names, out);
    }
}

fn distinct(ds: []const Digest) usize {
    var n: usize = 0;
    for (ds, 0..) |d, i| {
        if (std.mem.findScalar(Digest, ds[0..i], d) == null) n += 1;
    }
    return n;
}

const PartNamer = struct {
    store: *const ir.Store,
    part: []const RowId,
    names: []const Digest,
    missing: bool = false,

    fn namer(self: *const PartNamer) digest_mod.RowNamer {
        return .{ .ctx = self, .name = name };
    }

    fn name(ctx: *const anyopaque, row: RowId) Digest {
        const self: *const PartNamer = @ptrCast(@alignCast(ctx));
        if (std.mem.findScalar(RowId, self.part, row)) |i| {
            // A member, told apart from any finalized row's digest.
            var h = std.crypto.hash.sha2.Sha256.init(.{});
            h.update("member");
            h.update(std.mem.asBytes(&self.names[i]));
            var out: [32]u8 = undefined;
            h.final(&out);
            return std.mem.readInt(u128, out[0..16], .little);
        }
        // Every row outside the part is finalized before it: a caller is
        // finalized after its callees.
        return self.store.row(row).digest orelse {
            @constCast(self).missing = true;
            return 0;
        };
    }
};

// Two members pair when refinement left them in one class.
const ClassPairing = struct {
    part: []const RowId,
    digests: []const Digest,

    fn pairing(self: *const ClassPairing) equal.RowPairing {
        return .{ .ctx = self, .same = same };
    }

    fn same(ctx: *const anyopaque, a: RowId, b: RowId) bool {
        const self: *const ClassPairing = @ptrCast(@alignCast(ctx));
        const i = std.mem.findScalar(RowId, self.part, a) orelse return false;
        const j = std.mem.findScalar(RowId, self.part, b) orelse return false;
        return self.digests[i] == self.digests[j];
    }
};

// A member pairs with the finalized row it merges into.
const MapPairing = struct {
    from: []const RowId,
    to: []const ?RowId,

    fn pairing(self: *const MapPairing) equal.RowPairing {
        return .{ .ctx = self, .same = same };
    }

    fn same(ctx: *const anyopaque, a: RowId, b: RowId) bool {
        const self: *const MapPairing = @ptrCast(@alignCast(ctx));
        const i = std.mem.findScalar(RowId, self.from, a) orelse return false;
        return self.to[i].? == b;
    }
};

// Whether rows `a` and `b` compute one thing: equal parameter and result
// types, and bodies that end alike over equal values, with a row that
// `pairing` pairs taken as one. A digest collision never merges two rows.
fn sameRow(gpa: Allocator, store: *const ir.Store, a: RowId, b: RowId, pairing: equal.RowPairing) Allocator.Error!bool {
    const x = store.row(a);
    const y = store.row(b);
    if (x.result != y.result) return false;
    if (!std.mem.eql(TyId, store.tySlice(x.params), store.tySlice(y.params))) return false;
    var cmp: equal.Comparison = .{ .gpa = gpa, .store = store, .rows = pairing };
    defer cmp.deinit();
    return cmp.regions(x.body, y.body);
}

// Row `from` merges into `into`: every `Call` and `Closure` that names it
// names `into`.
// Row `from` merges into `into`, which `sameRow` found equal to it: every
// call and closure of `from` names `into`, and each node of `into` takes the
// origins of the node of `from` its numbering pairs it with (N10).
fn mergeInto(gpa: Allocator, store: *ir.Store, from: RowId, into: RowId) Error!void {
    {
        var returns = try live_mod.Returns.init(gpa, store);
        defer returns.deinit(gpa);
        var a = try number.ofRow(gpa, store, &returns, from);
        defer a.deinit(gpa);
        var b = try number.ofRow(gpa, store, &returns, into);
        defer b.deinit(gpa);
        if (a.order.items.len != b.order.items.len) return error.InvariantBroken;
        for (a.order.items, b.order.items) |x, y| {
            const origins = try gpa.dupe(provenance.OriginId, store.provenance.of(x));
            defer gpa.free(origins);
            try store.provenance.add(gpa, y, origins);
        }
    }
    for (store.nodes.items(.op), store.nodes.items(.payload)) |op, *payload| {
        switch (op) {
            .call, .closure => if (payload.* == from.index()) {
                payload.* = into.index();
            },
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => {},
        }
    }
    store.rows.items[from.index()].merged_into = into;
}

// A row of the part is recursive when a cycle of calls reaches it.
fn setRecursive(gpa: Allocator, store: *ir.Store, part: []const RowId) Allocator.Error!void {
    const g = try graph(gpa, store, .calls);
    defer freeGraph(gpa, g);
    const comps = try components(gpa, g, part);
    defer freeComponents(gpa, comps);
    for (comps) |c| {
        const self_call = c.len == 1 and std.mem.findScalar(RowId, g[c[0].index()].items, c[0]) != null;
        for (c) |r| store.rows.items[r.index()].recursive = c.len > 1 or self_call;
    }
}

/// The digest of the rows a walk built for the site of `root`, before any
/// is simplified (P1): the root's index, and every row's digest with each
/// row it names named by its index, and every type, literal, primitive and
/// name by its content. Each site has a store and a type table of its own,
/// so no id is read; two sites with this digest built equal rows, and have
/// one normal form.
pub fn walkedDigest(gpa: Allocator, store: *const ir.Store, types: *const types_mod.Types, root: RowId) Allocator.Error!Digest {
    const ByIndex = struct {
        fn name(_: *const anyopaque, row: RowId) Digest {
            return @as(Digest, row.index()) | (@as(Digest, 1) << 64);
        }
    };
    const namer: digest_mod.RowNamer = .{ .ctx = store, .name = ByIndex.name };
    var content: digest_mod.Content = .{ .gpa = gpa, .types = types };
    defer content.deinit();
    var h = std.crypto.hash.sha2.Sha256.init(.{});
    h.update(std.mem.asBytes(&root.index()));
    for (0..store.rows.items.len) |i| {
        const d = try digest_mod.ofRowContent(gpa, store, RowId.of(@intCast(i)), namer, &content);
        h.update(std.mem.asBytes(&d));
    }
    var out: [32]u8 = undefined;
    h.final(&out);
    return std.mem.readInt(u128, out[0..16], .little);
}

/// The content digest of every node of the rows the site of `root` reaches
/// (V5a): one slice per row, root first, in the order the emitter writes the
/// rows, with one digest per node in the order it numbers them. Free it with
/// `digest_mod.freeSite`.
pub fn siteDigests(gpa: Allocator, store: *const ir.Store, types: *const types_mod.Types, root: RowId) Allocator.Error![]const []const Digest {
    var returns = try live_mod.Returns.init(gpa, store);
    defer returns.deinit(gpa);
    var reached: ir.RowTable(number.Numbering) = .empty;
    defer {
        for (reached.values()) |*n| n.deinit(gpa);
        reached.deinit(gpa);
    }
    try number.siteRows(gpa, store, &returns, root, &reached);
    const orders = try gpa.alloc([]const ir.NodeId, reached.count());
    defer gpa.free(orders);
    for (reached.values(), orders) |*numbering, *o| o.* = numbering.order.items;
    return digest_mod.ofSite(gpa, store, types, reached.keys(), orders);
}

/// Whether a row the site of `root` reaches holds an `Apply` (N8j): a call
/// through a function value that no rule resolved, which refuses the site.
pub fn reachesApply(gpa: Allocator, store: *const ir.Store, root: RowId) Allocator.Error!bool {
    var returns = try live_mod.Returns.init(gpa, store);
    defer returns.deinit(gpa);
    var reached: ir.RowTable(number.Numbering) = .empty;
    defer {
        for (reached.values()) |*n| n.deinit(gpa);
        reached.deinit(gpa);
    }
    try number.siteRows(gpa, store, &returns, root, &reached);
    for (reached.values()) |numbering| for (numbering.order.items) |n| {
        if (store.nodes.items(.op)[n.index()] == .apply) return true;
    };
    return false;
}

/// The M3 invariants of plan 5.2 over the rows `root` reaches: every
/// `Call` and `Closure` names a finalized row, no two of those rows have
/// one digest, every recursive flag agrees with the call graph, and every
/// digest recomputes to itself. Returns what failed, or null.
pub fn check(gpa: Allocator, store: *const ir.Store, root: RowId) Allocator.Error!?[]const u8 {
    var returns = try live_mod.Returns.init(gpa, store);
    defer returns.deinit(gpa);
    var reached: ir.RowTable(number.Numbering) = .empty;
    defer {
        for (reached.values()) |*n| n.deinit(gpa);
        reached.deinit(gpa);
    }
    try number.siteRows(gpa, store, &returns, root, &reached);
    const rows = reached.keys();
    for (rows) |r| {
        const info = store.row(r);
        if (info.merged_into != null) return "a row that merged is still named";
        if (info.digest == null) return "a row is not finalized";
    }
    for (rows, 0..) |r, i| for (rows[0..i]) |q| {
        if (r == root or q == root) continue;
        if (store.row(r).digest.? == store.row(q).digest.?) return "two finalized rows have one digest";
    };
    const g = try graph(gpa, store, .calls);
    defer freeGraph(gpa, g);
    const comps = try components(gpa, g, rows);
    defer freeComponents(gpa, comps);
    for (comps) |c| {
        const self_call = c.len == 1 and std.mem.findScalar(RowId, g[c[0].index()].items, c[0]) != null;
        for (c) |r| if (store.row(r).recursive != (c.len > 1 or self_call)) return "a recursive flag disagrees with the call graph";
    }
    const refs = try graph(gpa, store, .references);
    defer freeGraph(gpa, refs);
    const parts_ = try components(gpa, refs, rows);
    defer freeComponents(gpa, parts_);
    for (parts_) |part| {
        const ds = try gpa.alloc(Digest, part.len);
        defer gpa.free(ds);
        refine(gpa, store, part, ds) catch |err| switch (err) {
            error.OutOfMemory => |e| return e,
            error.InvariantBroken => return "a row names a row that is not finalized",
        };
        for (part, ds) |r, d| if (store.row(r).digest.? != d) return "a digest does not recompute to itself";
    }
    return null;
}

const testing = std.testing;
const driver = @import("driver.zig");
const dump = @import("dump.zig");

const Fixture = struct {
    store: ir.Store,
    types: types_mod.Types,
    b: Builder,

    fn init(self: *Fixture) void {
        self.store = ir.Store.init(testing.allocator);
        self.types = types_mod.Types.init(testing.allocator);
        self.b = Builder.init(testing.allocator, &self.store, &self.types);
    }

    fn deinit(self: *Fixture) void {
        self.b.deinit();
        self.types.deinit();
        self.store.deinit();
    }

    fn i64Ty(self: *Fixture) Allocator.Error!TyId {
        return self.types.intTy(.i64);
    }

    // Run the driver over the site of `root` and dump it.
    fn site(self: *Fixture, root: RowId) (driver.Error || std.Io.Writer.Error)![]u8 {
        _ = try driver.runTo(testing.allocator, &self.b, root, &.{}, .finalized);
        var out: std.Io.Writer.Allocating = .init(testing.allocator);
        errdefer out.deinit();
        try dump.dumpSite(&out.writer, testing.allocator, &self.store, &self.types, root);
        return out.toOwnedSlice();
    }
};

fn expectSite(f: *Fixture, root: RowId, want: []const u8) (driver.Error || std.Io.Writer.Error || error{TestExpectedEqual})!void {
    const got = try f.site(root);
    defer testing.allocator.free(got);
    try testing.expectEqualStrings(want, got);
}

// `|a, b| a - b` built with its parameters in the order `order` gives.
fn minusRow(f: *Fixture, swapped: bool) Allocator.Error!RowId {
    const i64_ty = try f.i64Ty();
    const r = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const a = Ref.rowParam(if (swapped) 1 else 0);
    const b = Ref.rowParam(if (swapped) 0 else 1);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .minus, &.{ a, b })} });
    return r;
}

test "N8g: two helpers written alike are one row, and the calls of them one call" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.i64Ty();
    const h1 = try minusRow(&f, false);
    const h2 = try minusRow(&f, false);
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const c1 = try f.b.callRow(h1, &.{ Ref.rowParam(0), Ref.rowParam(1) });
    const c2 = try f.b.callRow(h2, &.{ Ref.rowParam(0), Ref.rowParam(1) });
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ c1, c2 })} });
    try expectSite(&f, root,
        \\row r0 (I64, I64) -> I64
        \\  n0 = call r1(p0, p1) : I64 !spec
        \\  n1 = Num.I64.times_wrap(n0, n0) : I64
        \\  value n1
        \\row r1 (I64, I64) -> I64
        \\  n0 = Num.I64.minus(p0, p1) : I64 !spec
        \\  value n0
        \\
    );
}

test "N8f: a helper's parameter order is its first-read order, so swapping it and its arguments changes nothing" {
    var dumps: [2][]u8 = .{ &.{}, &.{} };
    defer for (dumps) |d| testing.allocator.free(d);
    for (&dumps, [_]bool{ false, true }) |*d, swapped| {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        const i64_ty = try f.i64Ty();
        const h = try minusRow(&f, swapped);
        const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
        const x = try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(0), Ref.rowParam(1) });
        const args: [2]Ref = if (swapped) .{ Ref.rowParam(1), x } else .{ x, Ref.rowParam(1) };
        try f.b.endRow(.{ .value = &.{try f.b.callRow(h, &args)} });
        d.* = try f.site(root);
    }
    try testing.expectEqualStrings(dumps[0], dumps[1]);
    try testing.expectEqualStrings(
        \\row r0 (I64, I64) -> I64
        \\  n0 = Num.I64.plus_wrap(p0, p1) : I64
        \\  n1 = call r1(n0, p1) : I64 !spec
        \\  value n1
        \\row r1 (I64, I64) -> I64
        \\  n0 = Num.I64.minus(p0, p1) : I64 !spec
        \\  value n0
        \\
    , dumps[0]);
}

test "N8f: a parameter the helper does not read is dropped, with its argument" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.i64Ty();
    const h = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(1), Ref.rowParam(1) })} });
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const unread = try f.b.call(.i64, .plus, &.{ Ref.rowParam(0), Ref.rowParam(1) });
    try f.b.endRow(.{ .value = &.{try f.b.callRow(h, &.{ unread, Ref.rowParam(0) })} });
    try expectSite(&f, root,
        \\row r0 (I64, I64) -> I64
        \\  n0 = call r1(p0) : I64
        \\  value n0
        \\row r1 (I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p0) : I64
        \\  value n0
        \\
    );
}

// `f(n) = if n < 1 then 0 else g(n - 1)`, where `g` is `f` itself, a row
// given, or with `partner` a row built on the spot the same way over `f`.
const Callee = union(enum) { itself, row: RowId, partner };

fn countdown(f: *Fixture, callee: Callee) Allocator.Error!RowId {
    const i64_ty = try f.i64Ty();
    const r = try f.b.beginRow(&.{i64_ty}, i64_ty);
    const one = try f.b.litInt(i64_ty, 1);
    const c = try f.b.call(.i64, .is_lt, &.{ Ref.rowParam(0), one });
    const arm0 = try f.b.openArm(c, 0);
    const next = try f.b.call(.i64, .minus, &.{ Ref.rowParam(0), one });
    const target = switch (callee) {
        .itself => r,
        .row => |g| g,
        .partner => blk: {
            const held = f.b.suspendRow();
            const g = try countdown(f, .{ .row = r });
            f.b.resumeRow(held);
            break :blk g;
        },
    };
    try f.b.close(.{ .value = &.{try f.b.callRow(target, &.{next})} });
    const arm1 = try f.b.openArm(c, 1);
    try f.b.close(.{ .value = &.{Ref.rowParam(0)} });
    try f.b.endRow(.{ .value = &.{try f.b.switchOn(c, &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{})} });
    return r;
}

test "N8g: two recursive rows that call each other alike are bisimilar and meet one row that calls itself" {
    var dumps: [2][]u8 = .{ &.{}, &.{} };
    defer for (dumps) |d| testing.allocator.free(d);
    for (&dumps, [_]bool{ false, true }) |*d, mutual| {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        const i64_ty = try f.i64Ty();
        const entry = try countdown(&f, if (mutual) .partner else .itself);
        const root = try f.b.beginRow(&.{i64_ty}, i64_ty);
        try f.b.endRow(.{ .value = &.{try f.b.callRow(entry, &.{Ref.rowParam(0)})} });
        d.* = try f.site(root);
    }
    try testing.expectEqualStrings(dumps[1], dumps[0]);
    try testing.expectEqualStrings(
        \\row r0 (I64) -> I64
        \\  n0 = call r1(p0) : I64 !spec
        \\  value n0
        \\row r1 (I64) -> I64
        \\  n0 = 1 : I64
        \\  n4 = loop(p0) : I64 !spec
        \\    body (s4.0: I64)
        \\      n1 = Num.I64.is_lt(s4.0, n0) : Bool
        \\      n3 = switch n1 : !spec
        \\        arm 0
        \\          n2 = Num.I64.minus(s4.0, n0) : I64 !spec
        \\          continue n2
        \\        arm 1
        \\          break s4.0
        \\      branch n3
        \\  value n4
        \\
    , dumps[0]);
}

test "N8e: a component whose cycle simplifying removed splits, and its parts are simplified again, callee first" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.i64Ty();
    // `f(n) = if True then h(n) else g(n)` and `g(n) = f(n) + 1`, built
    // with the rules off, so only simplifying decides the `if`. Then `f`
    // only calls `h`, and `g`, simplified again once `f` is final, calls `h`.
    f.b.hooks.rules_off = true;
    const h = try f.b.beginRow(&.{i64_ty}, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) })} });
    const r_f = try f.b.beginRow(&.{i64_ty}, i64_ty);
    const t = try f.b.litBool(true);
    const arm0 = try f.b.openArm(t, 0);
    const held = f.b.suspendRow();
    const r_g = try f.b.beginRow(&.{i64_ty}, i64_ty);
    const back = try f.b.callRow(r_f, &.{Ref.rowParam(0)});
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ back, try f.b.litInt(i64_ty, 1) })} });
    f.b.resumeRow(held);
    try f.b.close(.{ .value = &.{try f.b.callRow(r_g, &.{Ref.rowParam(0)})} });
    const arm1 = try f.b.openArm(t, 1);
    try f.b.close(.{ .value = &.{try f.b.callRow(h, &.{Ref.rowParam(0)})} });
    try f.b.endRow(.{ .value = &.{try f.b.switchOn(t, &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{})} });
    const root = try f.b.beginRow(&.{i64_ty}, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.callRow(r_g, &.{Ref.rowParam(0)})} });
    f.b.hooks.rules_off = false;
    try expectSite(&f, root,
        \\row r0 (I64) -> I64
        \\  n0 = call r1(p0) : I64
        \\  value n0
        \\row r1 (I64) -> I64
        \\  n0 = call r2(p0) : I64
        \\  n1 = 1 : I64
        \\  n2 = Num.I64.plus_wrap(n0, n1) : I64
        \\  value n2
        \\row r2 (I64) -> I64
        \\  n0 = Num.I64.times_wrap(p0, p0) : I64
        \\  value n0
        \\
    );
}

test "N8f: a closure of a renumbered row calls it through a row that keeps the closure's convention" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.i64Ty();
    // `|x| x - c`, lifted with the capture `c` first.
    const lifted = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .minus, &.{ Ref.rowParam(1), Ref.rowParam(0) })} });
    const fn_ty = try f.types.funcTy(&.{i64_ty}, i64_ty);
    const root = try f.b.beginRow(&.{i64_ty}, fn_ty);
    try f.b.endRow(.{ .value = &.{try f.b.closure(lifted, &.{Ref.rowParam(0)}, fn_ty)} });
    try expectSite(&f, root,
        \\row r0 (I64) -> (I64 -> I64)
        \\  n0 = closure r1(p0) : (I64 -> I64)
        \\  value n0
        \\row r1 (I64, I64) -> I64
        \\  n0 = call r2(p1, p0) : I64 !spec
        \\  value n0
        \\row r2 (I64, I64) -> I64
        \\  n0 = Num.I64.minus(p0, p1) : I64 !spec
        \\  value n0
        \\
    );
}

test "N8c over calls: a call of a row that only calls another row over its parameters is that call" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.i64Ty();
    const t = try minusRow(&f, false);
    const h = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.callRow(t, &.{ Ref.rowParam(1), Ref.rowParam(0) })} });
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.callRow(h, &.{ Ref.rowParam(0), Ref.rowParam(1) })} });
    try expectSite(&f, root,
        \\row r0 (I64, I64) -> I64
        \\  n0 = call r1(p1, p0) : I64 !spec
        \\  value n0
        \\row r1 (I64, I64) -> I64
        \\  n0 = Num.I64.minus(p0, p1) : I64 !spec
        \\  value n0
        \\
    );
}

// `|x| x + k` lifted with the capture `k` first, or `|x| x * 2` with none.
fn adderRow(f: *Fixture) Allocator.Error!RowId {
    const i64_ty = try f.i64Ty();
    const r = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(0), Ref.rowParam(1) })} });
    return r;
}

fn doublerRow(f: *Fixture) Allocator.Error!RowId {
    const i64_ty = try f.i64Ty();
    const r = try f.b.beginRow(&.{i64_ty}, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), try f.b.litInt(i64_ty, 2) })} });
    return r;
}

test "N8i: an Apply of a known closure is a call of its row over the captures and the arguments" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.i64Ty();
    const fn_ty = try f.types.funcTy(&.{i64_ty}, i64_ty);
    const add = try adderRow(&f);
    f.b.hooks.rules_off = true;
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const clo = try f.b.closure(add, &.{Ref.rowParam(0)}, fn_ty);
    try f.b.endRow(.{ .value = &.{try f.b.apply(clo, &.{Ref.rowParam(1)}, i64_ty)} });
    f.b.hooks.rules_off = false;
    try expectSite(&f, root,
        \\row r0 (I64, I64) -> I64
        \\  n0 = call r1(p0, p1) : I64
        \\  value n0
        \\row r1 (I64, I64) -> I64
        \\  n0 = Num.I64.plus_wrap(p0, p1) : I64
        \\  value n0
        \\
    );
}

test "N8i: an Apply of a function a switch chooses applies each arm's closure in that arm" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.i64Ty();
    const bool_ty = try f.types.boolTy();
    const fn_ty = try f.types.funcTy(&.{i64_ty}, i64_ty);
    const add = try adderRow(&f);
    const dbl = try doublerRow(&f);
    // `(if c then |x| x * 2 else |x| x + k)(y)`.
    const root = try f.b.beginRow(&.{ bool_ty, i64_ty, i64_ty }, i64_ty);
    const arm0 = try f.b.openArm(Ref.rowParam(0), 0);
    try f.b.close(.{ .value = &.{try f.b.closure(add, &.{Ref.rowParam(1)}, fn_ty)} });
    const arm1 = try f.b.openArm(Ref.rowParam(0), 1);
    try f.b.close(.{ .value = &.{try f.b.closure(dbl, &.{}, fn_ty)} });
    const chosen = try f.b.switchOn(Ref.rowParam(0), &.{ arm0, arm1 }, &.{}, &.{fn_ty}, &.{});
    try f.b.endRow(.{ .value = &.{try f.b.apply(chosen, &.{Ref.rowParam(2)}, i64_ty)} });
    try expectSite(&f, root,
        \\row r0 (Bool, I64, I64) -> I64
        \\  n2 = switch p0 : I64
        \\    arm 0
        \\      n0 = call r1(p1, p2) : I64
        \\      value n0
        \\    arm 1
        \\      n1 = call r2(p2) : I64
        \\      value n1
        \\  value n2
        \\row r1 (I64, I64) -> I64
        \\  n0 = Num.I64.plus_wrap(p0, p1) : I64
        \\  value n0
        \\row r2 (I64) -> I64
        \\  n0 = 2 : I64
        \\  n1 = Num.I64.times_wrap(p0, n0) : I64
        \\  value n1
        \\
    );
}

// `twice(h, x) = h(h(x))`, whose `h` no call fixed when it was built.
fn twiceRow(f: *Fixture) Allocator.Error!RowId {
    const i64_ty = try f.i64Ty();
    const fn_ty = try f.types.funcTy(&.{i64_ty}, i64_ty);
    const r = try f.b.beginRow(&.{ fn_ty, i64_ty }, i64_ty);
    const inner = try f.b.apply(Ref.rowParam(0), &.{Ref.rowParam(1)}, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.apply(Ref.rowParam(0), &.{inner}, i64_ty)} });
    return r;
}

test "N8i: a call that passes a known closure calls a row specialized to it, one row for two such calls" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.i64Ty();
    const fn_ty = try f.types.funcTy(&.{i64_ty}, i64_ty);
    const add = try adderRow(&f);
    const twice = try twiceRow(&f);
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const c1 = try f.b.callRow(twice, &.{ try f.b.closure(add, &.{Ref.rowParam(0)}, fn_ty), Ref.rowParam(1) });
    const c2 = try f.b.callRow(twice, &.{ try f.b.closure(add, &.{Ref.rowParam(1)}, fn_ty), Ref.rowParam(0) });
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ c1, c2 })} });
    try expectSite(&f, root,
        \\row r0 (I64, I64) -> I64
        \\  n0 = call r1(p0, p1) : I64
        \\  n1 = call r1(p1, p0) : I64
        \\  n2 = Num.I64.bitwise_xor(n0, n1) : I64
        \\  value n2
        \\row r1 (I64, I64) -> I64
        \\  n0 = call r2(p0, p1) : I64
        \\  n1 = call r2(p0, n0) : I64
        \\  value n1
        \\row r2 (I64, I64) -> I64
        \\  n0 = Num.I64.plus_wrap(p0, p1) : I64
        \\  value n0
        \\
    );
}

test "N8j: an Apply that no rule resolves refuses the site" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.i64Ty();
    const fn_ty = try f.types.funcTy(&.{i64_ty}, i64_ty);
    const root = try f.b.beginRow(&.{ fn_ty, i64_ty }, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.apply(Ref.rowParam(0), &.{Ref.rowParam(1)}, i64_ty)} });
    try testing.expectError(error.UnresolvedApply, f.site(root));
}

// `apply(f, x) = f(x)` called with `|y| y - k`: the row the call
// specializes to is renumbered at its finalize, and the call built after it
// passes its arguments in the new order.
test "N8i: a call of a specialization its finalize renumbered passes the arguments in the new order" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.i64Ty();
    const fn_ty = try f.types.funcTy(&.{i64_ty}, i64_ty);
    const lam = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .minus, &.{ Ref.rowParam(1), Ref.rowParam(0) })} });
    const ap = try f.b.beginRow(&.{ fn_ty, i64_ty }, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.apply(Ref.rowParam(0), &.{Ref.rowParam(1)}, i64_ty)} });
    const root = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.callRow(ap, &.{ try f.b.closure(lam, &.{Ref.rowParam(0)}, fn_ty), Ref.rowParam(1) })} });
    try expectSite(&f, root,
        \\row r0 (I64, I64) -> I64
        \\  n0 = call r1(p1, p0) : I64 !spec
        \\  value n0
        \\row r1 (I64, I64) -> I64
        \\  n0 = Num.I64.minus(p0, p1) : I64 !spec
        \\  value n0
        \\
    );
}

// `|x| x + value` in `f`, after `f` interns `padding` other types first.
fn walkedAdder(f: *Fixture, padding: bool, value: i128) Allocator.Error!Digest {
    if (padding) {
        _ = try f.types.strTy();
        _ = try f.types.floatTy(.f64);
    }
    const i64_ty = try f.i64Ty();
    const r = try f.b.beginRow(&.{i64_ty}, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(0), try f.b.litInt(i64_ty, value) })} });
    return walkedDigest(testing.allocator, &f.store, &f.types, r);
}

test "P1: the walked digest reads types and literals by their content, not by their ids" {
    var plain: Fixture = undefined;
    plain.init();
    defer plain.deinit();
    var padded: Fixture = undefined;
    padded.init();
    defer padded.deinit();
    var other: Fixture = undefined;
    other.init();
    defer other.deinit();
    const a = try walkedAdder(&plain, false, 3);
    try testing.expectEqual(a, try walkedAdder(&padded, true, 3));
    try testing.expect(a != try walkedAdder(&other, false, 4));
}

// `|u, x| (B(x), payload B.0(u))` over `[A, B(I64)]`, after `f` interns the
// names in `order` first.
fn walkedTags(f: *Fixture, order: []const []const u8) Allocator.Error!Digest {
    for (order) |text| _ = try f.types.name(text);
    const i64_ty = try f.i64Ty();
    const union_ty = try f.types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{i64_ty} } });
    const pair_ty = try f.types.tupleTy(&.{ union_ty, i64_ty });
    const name_b = try f.types.name("B");
    const r = try f.b.beginRow(&.{ union_ty, i64_ty }, pair_ty);
    const made = try f.b.tag(union_ty, name_b, &.{Ref.rowParam(1)});
    const read = try f.b.payload(Ref.rowParam(0), name_b, 0);
    try f.b.endRow(.{ .value = &.{try f.b.tuple(pair_ty, &.{ made, read })} });
    return walkedDigest(testing.allocator, &f.store, &f.types, r);
}

test "P1: the walked digest reads a tag by its name, not by the order a store interned it in" {
    var a_first: Fixture = undefined;
    a_first.init();
    defer a_first.deinit();
    var b_first: Fixture = undefined;
    b_first.init();
    defer b_first.deinit();
    const forward = try walkedTags(&a_first, &.{ "A", "B" });
    try testing.expectEqual(forward, try walkedTags(&b_first, &.{ "B", "A" }));
}

test "N8g: a forced digest collision merges nothing, and finalize reports it" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.i64Ty();
    const doubled = try f.b.beginRow(&.{i64_ty}, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), try f.b.litInt(i64_ty, 2) })} });
    const bumped = try f.b.beginRow(&.{i64_ty}, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(0), try f.b.litInt(i64_ty, 1) })} });
    const root = try f.b.beginRow(&.{i64_ty}, i64_ty);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ try f.b.callRow(doubled, &.{Ref.rowParam(0)}), try f.b.callRow(bumped, &.{Ref.rowParam(0)}) })} });
    var fin: Finalizer = .{ .gpa = testing.allocator, .root = root, .max_turns = 8 };
    defer fin.deinit();
    try fin.finalize(&f.b, &.{doubled});
    // The registry says `bumped`'s digest is `doubled`'s, as a collision would.
    var d: [1]Digest = undefined;
    try refine(testing.allocator, &f.store, &.{bumped}, &d);
    try fin.registry.put(testing.allocator, d[0], doubled);
    try testing.expectError(error.InvariantBroken, fin.finalize(&f.b, &.{bumped}));
    try testing.expectEqual(@as(?RowId, null), f.store.row(bumped).merged_into);
}
