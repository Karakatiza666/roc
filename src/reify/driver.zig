//! The pipeline driver (I12): the stages of plan 1.3 over one module's rows.
//!
//! | Stage | Runs | Does |
//! |---|---|---|
//! | simplify | per component of the call graph, callee first, to a fixpoint | each round rebuilds every row of the component (`rebuild.zig`) at its latest regions (`place.zig`), then runs the passes |
//! | finalize | per component, once its fixpoint ends | splits a component that is no longer one (N8e), then orders outputs and joins, renumbers parameters (N8f), and digests and merges rows (N8g), in `rows.zig` |
//! | number | per row, once every component is final | hoists speculatable nodes out of loops (N5b), then puts switch outputs and joins in the walk's order (N9) |
//!
//! A round changed its component when a row's fingerprint (`number.zig`),
//! which does not read where nodes are placed, or a row's speculatable flag
//! changed. A round that changed a fingerprint must have lowered the measure
//! of normal-form 3.0. A round that changed neither ends the component. A
//! rewrite can take away the use that placed a node in an outer region, but
//! it changes a fingerprint, so another round places the node. A rebuild
//! that rewrites nothing builds no node its row does not read (matching a
//! rule builds nothing), so it leaves every row settled. The rounds per
//! component are capped by `max_rounds`, a constant of the language version
//! (plan 2.3). The passes are hooks, so each milestone adds its passes
//! without changing the driver.
//!
//! The verifier, and the checks that no plan speculates, that the simplify
//! stage left every row settled, and that the number stage left the
//! numbering a fixpoint and the content digest as it was, run in builds with
//! runtime safety.

const std = @import("std");
const collections = @import("collections");
const ir = @import("ir.zig");
const types_mod = @import("types.zig");
const measure = @import("measure.zig");
const verify = @import("verify.zig");
const live = @import("live.zig");
const place = @import("place.zig");
const rebuild = @import("rebuild.zig");
const number = @import("number.zig");
const digest = @import("digest.zig");
const builder_mod = @import("builder.zig");
const rows = @import("rows.zig");
const views = @import("views.zig");
const match = @import("match.zig");
const loops = @import("loops.zig");
const scalar = @import("scalar.zig");
const laws = @import("laws.zig");

const Allocator = std.mem.Allocator;
const RowId = ir.RowId;
const Builder = builder_mod.Builder;

/// The cap on simplify rounds per component.
pub const max_rounds: u32 = 64;

/// Whether the driver runs the verifier and its own checks.
const checks = std.debug.runtime_safety;

/// A simplify pass: rewrites the rows of a component and says whether it changed any.
pub const Pass = struct {
    name: []const u8,
    run: *const fn (ctx: *anyopaque, store: *ir.Store, types: *types_mod.Types, rows: []const RowId) Allocator.Error!bool,
    ctx: *anyopaque,
};

/// Why the driver stopped.
pub const Error = error{
    /// A round changed a row without lowering its measure: a compiler bug.
    MeasureDidNotFall,
    /// A component took more than `max_rounds` rounds.
    RoundBoundExceeded,
    /// A pass broke an invariant of the verifier: a compiler bug.
    InvariantBroken,
    /// A call through a function value that no rule resolved is left in a
    /// row the site reaches (N8j).
    UnresolvedApply,
} || Allocator.Error;

/// What one run of the driver did.
pub const Stats = struct {
    components: u32 = 0,
    rounds: u32 = 0,
    max_component_rounds: u32 = 0,
    /// For the `outline` view: the size of `inline` and of the result
    /// (`views.siteSize`), the rows the passes made, and the passes that
    /// chose a shape.
    inline_size: views.SiteSize = .{},
    outline_size: views.SiteSize = .{},
    outline_rows: u32 = 0,
    outline_passes: u32 = 0,
};

/// The components of the graph of `Call` and `Closure` references, callee
/// first (`rows.zig`).
pub fn components(gpa: Allocator, store: *const ir.Store) Allocator.Error![][]RowId {
    const g = try rows.graph(gpa, store, .references);
    defer rows.freeGraph(gpa, g);
    const all = try gpa.alloc(RowId, store.rows.items.len);
    defer gpa.free(all);
    for (all, 0..) |*r, i| r.* = RowId.of(@intCast(i));
    return rows.components(gpa, g, all);
}

/// Which rows the run leaves: the finalized rows, the `graph` view of them
/// (V1), which a `Code(f)` site holds, the `inline` view (V2), which a
/// `Code.Inlined(f)` site holds, or the `outline` view (V3), which a
/// `Code.Outlined(f)` site holds.
pub const View = enum { finalized, graph, inline_, outline };

/// How a run builds its view.
pub const Options = struct {
    /// K of the `outline` view. Only the measurement of K reads another
    /// value (`ROC_REIFY_OUTLINE_STATS`); the language version fixes it.
    outline_min_size: u32 = views.outline_min_size,
    /// Whether the site opts into layer L (`laws.zig`): a `Code.Lawful(f)` site.
    laws: bool = false,
};

/// Run the simplify, finalize, view and number stages over every row of
/// `b`'s store, whose site has the root `root`. `b` builds no row now.
pub fn run(gpa: Allocator, b: *Builder, root: RowId, passes: []const Pass) Error!Stats {
    return runTo(gpa, b, root, passes, .graph);
}

/// `run`, leaving the rows at `view`.
pub fn runTo(gpa: Allocator, b: *Builder, root: RowId, passes: []const Pass, view: View) Error!Stats {
    return runToWith(gpa, b, root, passes, view, .{});
}

/// `runTo`, with `options`.
pub fn runToWith(gpa: Allocator, b: *Builder, root: RowId, passes: []const Pass, view: View, options: Options) Error!Stats {
    std.debug.assert(options.outline_min_size >= 3);
    const store = b.store;
    store.rows.items[root.index()].fixed_params = true;
    var stats: Stats = .{};
    const comps = try components(gpa, store);
    defer rows.freeComponents(gpa, comps);
    var fin: rows.Finalizer = .{ .gpa = gpa, .root = root, .ties = ties(b), .max_turns = max_rounds };
    defer fin.deinit();
    var special: Specialize = .{ .gpa = gpa, .passes = passes, .fin = &fin, .stats = &stats, .arena = std.heap.ArenaAllocator.init(gpa) };
    defer special.deinit();
    b.specializer = .{ .ctx = &special, .run = Specialize.run };
    defer b.specializer = null;
    b.scalarizer = .{ .ctx = &special, .run = Specialize.scalarize };
    defer b.scalarizer = null;
    if (options.laws) b.laws = .{ .ctx = &special, .close = Specialize.lawClose, .inline_row = Specialize.lawInline };
    defer b.laws = null;
    for (comps) |comp| {
        try component(gpa, b, passes, &fin, comp, &stats);
        if (special.failed) |err| return err;
    }
    if (try rows.reachesApply(gpa, store, root)) return error.UnresolvedApply;
    switch (view) {
        .finalized => {},
        .graph => try viewTurns(gpa, b, passes, &fin, root, &stats, views.singleUse),
        .inline_ => {
            try viewTurns(gpa, b, passes, &fin, root, &stats, views.singleUse);
            try viewTurns(gpa, b, passes, &fin, root, &stats, views.everyHelper);
        },
        .outline => {
            try viewTurns(gpa, b, passes, &fin, root, &stats, views.singleUse);
            try viewTurns(gpa, b, passes, &fin, root, &stats, views.everyHelper);
        },
    }
    if (special.failed) |err| return err;
    // V3 runs over the `inline` view and makes rows that no simplify round
    // built, so the rule checks below do not read the calls of its rows.
    var outlined: std.ArrayList(RowId) = .empty;
    defer outlined.deinit(gpa);
    if (view == .outline) try outlineTurns(gpa, b, &fin, root, &stats, options.outline_min_size, &outlined);
    try numberStage(gpa, b);
    if (checks) {
        try checkInvariants(gpa, b, root, outlined.items, options.laws);
        try checkFlatTrees(gpa, store, b.types);
        if (try rows.check(gpa, store, root)) |_| return error.InvariantBroken;
    }
    return stats;
}

// A view's turns (`views.zig`): V1 inlines every row called from one place
// into its caller, and V2 every call of a row that is not recursive, with
// each closure of such a row a lambda. Each turn rebuilds the callers,
// simplifies them, and finalizes the site's rows again, callee first, from
// a registry of their own, because a caller's digest names its callees'.
// Every turn takes the calls and closures of the rows it picked out of the
// rows the site reaches, so the turns end.
fn viewTurns(
    gpa: Allocator,
    b: *Builder,
    passes: []const Pass,
    fin: *rows.Finalizer,
    root: RowId,
    stats: *Stats,
    comptime turnOf: fn (Allocator, *const ir.Store, RowId) Allocator.Error!views.Turn,
) Error!void {
    const store = b.store;
    while (true) {
        var turn = try turnOf(gpa, store, root);
        defer turn.deinit(gpa);
        if (turn.callers.len == 0) return;
        var returns = try live.Returns.init(gpa, store);
        defer returns.deinit(gpa);
        const plans = try gpa.alloc(place.Plan, turn.inlined.len + turn.lambdas.len);
        var planned: usize = 0;
        defer {
            for (plans[0..planned]) |*p| p.deinit();
            gpa.free(plans);
        }
        var inline_rows: collections.DenseMapUnmanaged(RowId, *const place.Plan) = .empty;
        defer inline_rows.deinit(gpa);
        var lambda_rows: collections.DenseMapUnmanaged(RowId, *const place.Plan) = .empty;
        defer lambda_rows.deinit(gpa);
        for (turn.inlined) |r| {
            plans[planned] = try place.planWith(gpa, store, &returns, r, .simplify, ties(b));
            try inline_rows.put(gpa, r, &plans[planned]);
            planned += 1;
        }
        for (turn.lambdas) |r| {
            plans[planned] = try place.planWith(gpa, store, &returns, r, .simplify, ties(b));
            try lambda_rows.put(gpa, r, &plans[planned]);
            planned += 1;
        }
        for (turn.callers) |c| {
            var p = try place.planWith(gpa, store, &returns, c, .simplify, ties(b));
            defer p.deinit();
            try rebuild.run(gpa, b, &p, .{ .inline_rows = &inline_rows, .lambda_rows = &lambda_rows });
        }
        try refinalize(gpa, b, passes, fin, root, stats, turn.callers);
    }
}

// The rows the site of `root` reaches, finalized again callee first, from a
// registry of their own, because a caller's digest names its callees'. A
// component that holds one of `changed` is simplified first.
fn refinalize(gpa: Allocator, b: *Builder, passes: []const Pass, fin: *rows.Finalizer, root: RowId, stats: *Stats, changed: []const RowId) Error!void {
    const store = b.store;
    var reached: std.ArrayList(RowId) = .empty;
    defer reached.deinit(gpa);
    {
        var numberings: ir.RowTable(number.Numbering) = .empty;
        defer {
            for (numberings.values()) |*n| n.deinit(gpa);
            numberings.deinit(gpa);
        }
        var after = try live.Returns.init(gpa, store);
        defer after.deinit(gpa);
        try number.siteRows(gpa, store, &after, root, &numberings);
        try reached.appendSlice(gpa, numberings.keys());
    }
    fin.registry.clearRetainingCapacity();
    for (reached.items) |r| store.rows.items[r.index()].digest = null;
    const g = try rows.graph(gpa, store, .references);
    defer rows.freeGraph(gpa, g);
    const comps = try rows.components(gpa, g, reached.items);
    defer rows.freeComponents(gpa, comps);
    for (comps) |comp| {
        const simplified = for (comp) |r| {
            if (std.mem.findScalar(RowId, changed, r) != null) break true;
        } else false;
        if (simplified) try component(gpa, b, passes, fin, comp, stats) else try fin.finalize(b, comp);
    }
}

// V3 (`views.zig`): each pass makes a row of every shape it chose, copied
// from the shape's first occurrence, rewrites each occurrence as a call of
// it, and finalizes the site's rows again without simplifying them, until a
// pass chooses nothing. Every pass lowers the site's size, so the passes end.
fn outlineTurns(gpa: Allocator, b: *Builder, fin: *rows.Finalizer, root: RowId, stats: *Stats, min_size: u32, made: *std.ArrayList(RowId)) Error!void {
    const store = b.store;
    stats.inline_size = try views.siteSize(gpa, store, root);
    var size = stats.inline_size;
    while (true) {
        var sel = try views.outlineSelect(gpa, store, b.types, root, min_size);
        defer sel.deinit();
        if (sel.shapes.len == 0) break;
        const shape_rows = try gpa.alloc(RowId, sel.shapes.len);
        defer gpa.free(shape_rows);
        for (sel.shapes, shape_rows) |*shape, *row| {
            var returns = try live.Returns.init(gpa, store);
            defer returns.deinit(gpa);
            var p = try place.planWith(gpa, store, &returns, shape.rep.row, .simplify, ties(b));
            defer p.deinit();
            row.* = try rebuild.cone(gpa, b, &p, shape.rep.root, &shape.nodes, shape.rep.holes, shape.lits, &shape.also);
            try made.append(gpa, row.*);
        }
        for (sel.edits) |edit| {
            var o: rebuild.Outlined = .{};
            defer o.deinit(gpa);
            for (edit.calls) |c| try o.calls.put(gpa, c.root, .{ .row = shape_rows[c.shape], .args = c.holes });
            for (edit.skip) |n| try o.skip.put(gpa, n, {});
            var returns = try live.Returns.init(gpa, store);
            defer returns.deinit(gpa);
            var p = try place.planWith(gpa, store, &returns, edit.row, .simplify, ties(b));
            defer p.deinit();
            try rebuild.run(gpa, b, &p, .{ .raw = true, .outlined = &o });
        }
        try refinalize(gpa, b, &.{}, fin, root, stats, &.{});
        stats.outline_passes += 1;
        stats.outline_rows += @intCast(sel.shapes.len);
        const now = try views.siteSize(gpa, store, root);
        if (checks and now.nodes >= size.nodes) return error.InvariantBroken;
        size = now;
    }
    stats.outline_size = size;
}

// The rows calls specialize to (N8i, N8d), each built from a finalized
// row with one function parameter bound to a closure of a finalized row,
// then simplified and finalized on the spot, before the call that asked
// for it is built. Keyed by the two rows' digests, the parameter and the
// captures' types, so two calls that pass one function share a row.
const Specialize = struct {
    gpa: Allocator,
    passes: []const Pass,
    fin: *rows.Finalizer,
    stats: *Stats,
    made: std.AutoHashMapUnmanaged(u128, RowId) = .empty,
    /// Per finalized row's digest: how N14a splits its parameters, or null
    /// where it splits none. The arena owns the shapes.
    shapes: std.AutoHashMapUnmanaged(u128, ?[]const scalar.Shape) = .empty,
    arena: std.heap.ArenaAllocator,
    /// The first error a specialization stopped with, which ends the run
    /// once the caller's round is over.
    failed: ?Error = null,

    fn deinit(self: *Specialize) void {
        self.made.deinit(self.gpa);
        self.shapes.deinit(self.gpa);
        self.arena.deinit();
    }

    // N14a: the row a call of `row` is made to, when a parameter of `row`
    // splits. It is built from the finalized row with each such parameter
    // replaced by one parameter per component, which the body reads as the
    // aggregate they make, so a read by field or index is the component
    // (N13). It is simplified and finalized on the spot, before the call is
    // built, and keyed by the row's digest and the shapes, so two calls that
    // split one row alike share a row, and so do rows that differ only in
    // whether they take `f(a, b)`, `f({ a, b })` or `f((a, b))` (N8g).
    fn scalarize(ctx: *anyopaque, b: *Builder, row: RowId) builder_mod.SpecializeError!?builder_mod.Scalarized {
        const self: *Specialize = @ptrCast(@alignCast(ctx));
        const store = b.store;
        if (!scalar.rowEligible(store, row)) return null;
        const digest_of = store.row(row).digest.?;
        const known = try self.shapes.getOrPut(self.gpa, digest_of);
        if (!known.found_existing) known.value_ptr.* = try scalar.analyzeRow(self.arena.allocator(), self.gpa, store, b.types, row);
        const shapes = known.value_ptr.* orelse return null;

        var h = std.crypto.hash.sha2.Sha256.init(.{});
        h.update("scalar");
        h.update(std.mem.asBytes(&digest_of));
        for (shapes) |shape| hashShape(&h, shape);
        var out: [32]u8 = undefined;
        h.final(&out);
        const key = std.mem.readInt(u128, out[0..16], .little);
        if (self.made.get(key)) |made| return self.scalarized(store, made, shapes);

        const held = b.suspendRow();
        defer b.resumeRow(held);
        var scratch = std.heap.ArenaAllocator.init(self.gpa);
        defer scratch.deinit();
        const leaves = try scalar.leavesOf(scratch.allocator(), shapes);
        const old = try self.gpa.dupe(ir.TyId, store.tySlice(store.row(row).params));
        defer self.gpa.free(old);
        const params = try self.gpa.alloc(ir.TyId, leaves.len);
        defer self.gpa.free(params);
        for (leaves, params) |leaf, *t| t.* = scalar.tyAt(b.types, old[leaf.index], leaf.path);
        var returns = try live.Returns.init(self.gpa, store);
        defer returns.deinit(self.gpa);
        var p = try place.planWith(self.gpa, store, &returns, row, .simplify, ties(b));
        defer p.deinit();
        const Values = struct {
            gpa: Allocator,
            old: []const ir.TyId,
            shapes: []const scalar.Shape,
            first: []const u32,

            // Each old parameter as the aggregate its new parameters make.
            fn of(v: @This(), bb: *Builder) Allocator.Error![]const ir.Ref {
                const refs = try v.gpa.alloc(ir.Ref, v.old.len);
                errdefer v.gpa.free(refs);
                for (refs, v.old, v.shapes, v.first) |*r, ty, shape, first| {
                    var next = first;
                    r.* = try aggregate(bb, ty, shape, &next);
                }
                return refs;
            }

            fn aggregate(bb: *Builder, ty: ir.TyId, shape: scalar.Shape, next: *u32) Allocator.Error!ir.Ref {
                switch (shape) {
                    .whole => {
                        defer next.* += 1;
                        return ir.Ref.rowParam(@intCast(next.*));
                    },
                    .split => |children| {
                        const parts = try bb.gpa.alloc(ir.Ref, children.len);
                        defer bb.gpa.free(parts);
                        for (children, parts, 0..) |child, *part, i| {
                            part.* = try aggregate(bb, bb.types.componentTy(ty, @intCast(i)), child, next);
                        }
                        return switch (bb.types.get(ty)) {
                            .record => try bb.record(ty, parts),
                            .tuple => try bb.tuple(ty, parts),
                            .bool_, .str, .int, .float, .dec, .tag_union, .list, .nominal, .func, .opaque_, .recursive => unreachable, // a shape splits records and tuples only
                        };
                    },
                }
            }
        };
        const first = try self.gpa.alloc(u32, old.len);
        defer self.gpa.free(first);
        var at: u32 = 0;
        for (first, shapes) |*f, shape| {
            f.* = at;
            at += shape.leafCount();
        }
        const values: Values = .{ .gpa = self.gpa, .old = old, .shapes = shapes, .first = first };
        const made = try rebuild.into(self.gpa, b, &p, params, values, Values.of);
        try self.made.put(self.gpa, key, made);
        const comp = [_]RowId{made};
        component(self.gpa, b, self.passes, self.fin, &comp, self.stats) catch |err| {
            if (self.failed == null) self.failed = err;
            return switch (err) {
                error.OutOfMemory => |e| e,
                error.MeasureDidNotFall => error.MeasureDidNotFall,
                error.RoundBoundExceeded => error.RoundBoundExceeded,
                error.InvariantBroken, error.UnresolvedApply => error.InvariantBroken,
            };
        };
        return self.scalarized(store, made, shapes);
    }

    fn scalarized(self: *const Specialize, store: *const ir.Store, made: RowId, shapes: []const scalar.Shape) builder_mod.Scalarized {
        const at = self.specialized(store, made);
        return .{ .row = at.row, .order = at.order, .shapes = shapes };
    }

    fn hashShape(h: *std.crypto.hash.sha2.Sha256, shape: scalar.Shape) void {
        switch (shape) {
            .whole => h.update("w"),
            .split => |children| {
                h.update("(");
                for (children) |c| hashShape(h, c);
                h.update(")");
            },
        }
    }

    fn run(ctx: *anyopaque, b: *Builder, row: RowId, param: u32, closure: RowId, captures: []const ir.TyId) builder_mod.SpecializeError!?builder_mod.Specialized {
        const self: *Specialize = @ptrCast(@alignCast(ctx));
        const store = b.store;
        const closure_digest = store.row(closure).digest orelse return null;
        var h = std.crypto.hash.sha2.Sha256.init(.{});
        h.update(std.mem.asBytes(&store.row(row).digest.?));
        h.update(std.mem.asBytes(&param));
        h.update(std.mem.asBytes(&closure_digest));
        h.update(std.mem.sliceAsBytes(captures));
        var out: [32]u8 = undefined;
        h.final(&out);
        const key = std.mem.readInt(u128, out[0..16], .little);
        if (self.made.get(key)) |made| return self.specialized(store, made);

        const held = b.suspendRow();
        defer b.resumeRow(held);
        const old = try self.gpa.dupe(ir.TyId, store.tySlice(store.row(row).params));
        defer self.gpa.free(old);
        const params = try std.mem.concat(self.gpa, ir.TyId, &.{ old[0..param], captures, old[param + 1 ..] });
        defer self.gpa.free(params);
        var returns = try live.Returns.init(self.gpa, store);
        defer returns.deinit(self.gpa);
        var p = try place.planWith(self.gpa, store, &returns, row, .simplify, ties(b));
        defer p.deinit();
        const Values = struct {
            gpa: Allocator,
            old: usize,
            param: u32,
            closure: RowId,
            captures: usize,
            fn_ty: ir.TyId,

            fn of(v: @This(), bb: *Builder) Allocator.Error![]const ir.Ref {
                const refs = try v.gpa.alloc(ir.Ref, v.old);
                errdefer v.gpa.free(refs);
                const caps = try v.gpa.alloc(ir.Ref, v.captures);
                defer v.gpa.free(caps);
                for (caps, 0..) |*c, k| c.* = ir.Ref.rowParam(@intCast(v.param + k));
                for (refs, 0..) |*r, j| r.* = if (j < v.param)
                    ir.Ref.rowParam(@intCast(j))
                else if (j == v.param)
                    try bb.closure(v.closure, caps, v.fn_ty)
                else
                    ir.Ref.rowParam(@intCast(j - 1 + v.captures));
                return refs;
            }
        };
        const values: Values = .{ .gpa = self.gpa, .old = old.len, .param = param, .closure = closure, .captures = captures.len, .fn_ty = old[param] };
        const made = try rebuild.into(self.gpa, b, &p, params, values, Values.of);
        try self.made.put(self.gpa, key, made);
        const comp = [_]RowId{made};
        component(self.gpa, b, self.passes, self.fin, &comp, self.stats) catch |err| {
            if (self.failed == null) self.failed = err;
            return switch (err) {
                error.OutOfMemory => |e| e,
                error.MeasureDidNotFall => error.MeasureDidNotFall,
                error.RoundBoundExceeded => error.RoundBoundExceeded,
                error.InvariantBroken, error.UnresolvedApply => error.InvariantBroken,
            };
        };
        return self.specialized(store, made);
    }

    // Layer L (`laws.zig`): the row a law built, simplified and finalized on
    // the spot, and the row a closure of it names, with the captures that
    // row reads. A closure's row takes the captures first and the
    // function's own parameters after them, in their order; where finalize
    // ordered `row`'s parameters otherwise, a row that keeps that convention
    // calls it, as finalize makes one for a closure the walk built (N8f).
    fn lawClose(ctx: *anyopaque, b: *Builder, row: RowId, captures: u32) builder_mod.SpecializeError!?builder_mod.LawClosure {
        const self: *Specialize = @ptrCast(@alignCast(ctx));
        const store = b.store;
        const old = try self.arena.allocator().dupe(ir.TyId, store.tySlice(store.row(row).params));
        const comp = [_]RowId{row};
        component(self.gpa, b, self.passes, self.fin, &comp, self.stats) catch |err| return self.keep(err);
        const at = self.specialized(store, row);
        const order = at.order orelse {
            const kept = try self.arena.allocator().alloc(u32, captures);
            for (kept, 0..) |*k, i| k.* = @intCast(i);
            return .{ .row = at.row, .kept = kept };
        };
        var kept: std.ArrayList(u32) = .empty;
        for (order) |k| if (k < captures) try kept.append(self.arena.allocator(), k);
        const direct = order.len == old.len and for (order[kept.items.len..], captures..) |k, want| {
            if (k != want) break false;
        } else true;
        if (direct) return .{ .row = at.row, .kept = kept.items };
        const w = self.fin.conventionRow(b, at.row, order, old, captures, kept.items) catch |err| return self.keep(err);
        const wrapper = [_]RowId{w};
        component(self.gpa, b, self.passes, self.fin, &wrapper, self.stats) catch |err| return self.keep(err);
        return .{ .row = canonical(store, w), .kept = kept.items };
    }

    // `Builder.Laws.inline_row`: a row that only forwards to another, as a
    // closure's convention row does, is inlined as that row over the
    // arguments it passes.
    fn lawInline(ctx: *anyopaque, b: *Builder, row: RowId, args: []const ir.Ref, ty: ir.TyId) Allocator.Error!?ir.Ref {
        const self: *Specialize = @ptrCast(@alignCast(ctx));
        const store = b.store;
        var at = canonical(store, row);
        var with = try self.gpa.dupe(ir.Ref, args);
        defer self.gpa.free(with);
        while (store.forwardingCall(at)) |n| {
            const nd = store.node(n);
            const passed = try self.gpa.alloc(ir.Ref, nd.args.len);
            for (store.refSlice(nd.args), passed) |a, *p| p.* = with[a.output];
            self.gpa.free(with);
            with = passed;
            at = canonical(store, RowId.of(nd.payload));
        }
        const info = store.row(at);
        if (info.recursive) return null;
        var returns = try live.Returns.init(self.gpa, store);
        defer returns.deinit(self.gpa);
        const end = store.region(info.body).end;
        if (end.kind != .value or end.refs.len != 1 or returns.regionHolds(store, info.body)) return null;
        return try rebuild.inlineRow(self.gpa, b, &returns, at, with, ty, ties(b));
    }

    // The error a driver step a specialization runs stopped with, kept for
    // the end of the caller's round.
    fn keep(self: *Specialize, err: Error) builder_mod.SpecializeError {
        if (self.failed == null) self.failed = err;
        return switch (err) {
            error.OutOfMemory => |e| e,
            error.MeasureDidNotFall => error.MeasureDidNotFall,
            error.RoundBoundExceeded => error.RoundBoundExceeded,
            error.InvariantBroken, error.UnresolvedApply => error.InvariantBroken,
        };
    }

    // The row `made` is now, with the order finalize gave its parameters.
    // A row that merged took the parameters of the row it merged into, in
    // the order `made` had them, and the merge follows the renumbering.
    fn specialized(self: *const Specialize, store: *const ir.Store, made: RowId) builder_mod.Specialized {
        return .{ .row = canonical(store, made), .order = self.fin.orderOf(made) };
    }
};

// The row `r` merged into, or `r`.
fn canonical(store: *const ir.Store, r: RowId) RowId {
    var at = r;
    while (store.row(at).merged_into) |next| at = next;
    return at;
}

// One component: its fixpoint, then its parts if it split (N8e), each
// simplified and finalized callee first, or its finalize.
fn component(gpa: Allocator, b: *Builder, passes: []const Pass, fin: *rows.Finalizer, comp: []const RowId, stats: *Stats) Error!void {
    stats.components += 1;
    const rounds = try simplify(gpa, b, passes, comp);
    stats.rounds += rounds;
    stats.max_component_rounds = @max(stats.max_component_rounds, rounds);
    if (checks and !try allSettled(gpa, b.store, comp)) return error.InvariantBroken;
    const split = try rows.parts(gpa, b.store, comp);
    defer rows.freeComponents(gpa, split);
    if (split.len > 1) {
        for (split) |part| try component(gpa, b, passes, fin, part, stats);
        return;
    }
    try fin.finalize(b, comp);
    if (checks and !try allSettled(gpa, b.store, comp)) return error.InvariantBroken;
    // Finalizing merged rows that call each other alike into one row that
    // calls itself. When that call is a tail call the row is a loop (N12),
    // so the row it became is simplified again, then finalized again.
    var again: std.ArrayList(RowId) = .empty;
    defer again.deinit(gpa);
    {
        var reached = try live.ofStore(gpa, b.store);
        defer reached.deinit(gpa);
        var scratch = std.heap.ArenaAllocator.init(gpa);
        defer scratch.deinit();
        for (comp) |r| {
            const at = canonical(b.store, r);
            if (at != r or std.mem.indexOfScalar(RowId, again.items, at) != null) continue;
            if (try loops.tailSites(scratch.allocator(), b.store, reached, at) != null) try again.append(gpa, at);
        }
    }
    if (again.items.len == 0) return;
    const more = try simplify(gpa, b, passes, again.items);
    stats.rounds += more;
    stats.max_component_rounds = @max(stats.max_component_rounds, more);
    try fin.finalize(b, again.items);
    if (checks and !try allSettled(gpa, b.store, again.items)) return error.InvariantBroken;
}

/// What a round compares: per row, its fingerprint and its flag, and the
/// component's measure.
const State = struct {
    prints: []u128,
    flags: []bool,
    measure: measure.Measure,

    fn deinit(self: *State, gpa: Allocator) void {
        gpa.free(self.prints);
        gpa.free(self.flags);
    }
};

fn stateOf(gpa: Allocator, store: *const ir.Store, types: *const types_mod.Types, comp: []const RowId, with_laws: bool) Allocator.Error!State {
    var returns = try live.Returns.init(gpa, store);
    defer returns.deinit(gpa);
    var reached = try live.ofStore(gpa, store);
    defer reached.deinit(gpa);
    const prints = try gpa.alloc(u128, comp.len);
    errdefer gpa.free(prints);
    const flags = try gpa.alloc(bool, comp.len);
    errdefer gpa.free(flags);
    var total: measure.Measure = .{};
    var calls = scalar.Cache.init(gpa, store, types, reached);
    defer calls.deinit();
    for (comp, prints, flags) |r, *p, *f| {
        var numbering = try number.ofRow(gpa, store, &returns, r);
        defer numbering.deinit(gpa);
        p.* = number.fingerprint(store, &returns, &numbering, r);
        f.* = store.row(r).speculatable;
        const m = try measure.ofRow(gpa, store, types, reached, &calls, r, with_laws);
        for (&total.counts, m.counts) |*t, c| t.* +|= c;
    }
    return .{ .prints = prints, .flags = flags, .measure = total };
}

fn simplify(gpa: Allocator, b: *Builder, passes: []const Pass, comp: []const RowId) Error!u32 {
    const store = b.store;
    var rounds: u32 = 0;
    var before = try stateOf(gpa, store, b.types, comp, b.laws != null);
    defer before.deinit(gpa);
    while (true) {
        {
            var returns = try live.Returns.init(gpa, store);
            defer returns.deinit(gpa);
            var reached = try live.ofStore(gpa, store);
            defer reached.deinit(gpa);
            var tails = std.heap.ArenaAllocator.init(gpa);
            defer tails.deinit();
            for (comp) |r| {
                var p = try place.planWith(gpa, store, &returns, r, .simplify, ties(b));
                defer p.deinit();
                if (checks and !place.noSpeculation(&p)) return error.InvariantBroken;
                // N12: a row whose every call to itself is a tail call is a loop.
                if (try loops.tailSites(tails.allocator(), store, reached, r)) |tail| {
                    try rebuild.runTail(gpa, b, &p, &tail);
                } else try rebuild.run(gpa, b, &p, .{});
            }
        }
        var passed = false;
        for (passes) |p| {
            if (try p.run(p.ctx, store, b.types, comp)) passed = true;
        }
        var after = try stateOf(gpa, store, b.types, comp, b.laws != null);
        const content = passed or !std.mem.eql(u128, before.prints, after.prints);
        const flags = !std.mem.eql(bool, before.flags, after.flags);
        if (!content and !flags) {
            after.deinit(gpa);
            return rounds;
        }
        rounds += 1;
        if (content and after.measure.order(before.measure) != .lt) {
            after.deinit(gpa);
            return error.MeasureDidNotFall;
        }
        before.deinit(gpa);
        before = after;
        if (rounds >= max_rounds) return error.RoundBoundExceeded;
    }
}

// Whether every row of a component, once simplified, is where placement puts it.
fn allSettled(gpa: Allocator, store: *const ir.Store, comp: []const RowId) Allocator.Error!bool {
    var returns = try live.Returns.init(gpa, store);
    defer returns.deinit(gpa);
    for (comp) |r| {
        var p = try place.plan(gpa, store, &returns, r, .simplify);
        defer p.deinit();
        if (!place.settled(&p)) return false;
    }
    return true;
}

// The number stage of every row: hoisting (N5b), which must leave the row's
// content digest as it was, then outputs and joins in the walk's order (N9),
// until the numbering is a fixpoint.
fn numberStage(gpa: Allocator, b: *Builder) Error!void {
    const store = b.store;
    for (0..store.rows.items.len) |i| {
        const r = RowId.of(@intCast(i));
        if (store.row(r).merged_into != null) continue;
        const before = if (checks) try digest.ofRegion(gpa, store, store.row(r).body) else 0;
        {
            var returns = try live.Returns.init(gpa, store);
            defer returns.deinit(gpa);
            var p = try place.planWith(gpa, store, &returns, r, .number, ties(b));
            defer p.deinit();
            if (checks and !place.noSpeculation(&p)) return error.InvariantBroken;
            try rebuild.run(gpa, b, &p, .{ .raw = true });
        }
        if (checks and try digest.ofRegion(gpa, store, store.row(r).body) != before) return error.InvariantBroken;
        var turns: u32 = 0;
        while (true) : (turns += 1) {
            var returns = try live.Returns.init(gpa, store);
            defer returns.deinit(gpa);
            var numbering = try number.ofRow(gpa, store, &returns, r);
            defer numbering.deinit(gpa);
            if (number.inOrder(store, &numbering)) break;
            if (turns == max_rounds) return error.InvariantBroken;
            var p = try place.planWith(gpa, store, &returns, r, .number, ties(b));
            defer p.deinit();
            try rebuild.run(gpa, b, &p, .{ .raw = true, .outputs = &numbering.outputs, .joins = &numbering.joins });
        }
    }
}

// How placement breaks ties: at random only under the L6 test hook.
fn ties(b: *const Builder) place.Ties {
    if (builder_mod.hooks_enabled) if (b.hooks.shuffle) |random| return .{ .shuffled = random };
    return .lowest;
}

// N7a: every flat decision tree is canonical, and none is larger than the
// multiplier bound (`match.zig`).
fn checkFlatTrees(gpa: Allocator, store: *const ir.Store, types: *types_mod.Types) Error!void {
    var report = try match.check(gpa, store, types);
    defer report.deinit();
    if (!report.ok()) return error.InvariantBroken;
}

fn checkInvariants(gpa: Allocator, b: *const Builder, root: RowId, outlined: []const RowId, with_laws: bool) Error!void {
    const store = b.store;
    const types = b.types;
    var report = try verify.verifyAll(gpa, store, types);
    defer report.deinit();
    if (!report.ok()) return error.InvariantBroken;
    // L2: no call of a row the site reaches is one N14a splits.
    {
        var returns = try live.Returns.init(gpa, store);
        defer returns.deinit(gpa);
        var reached: ir.RowTable(number.Numbering) = .empty;
        defer {
            for (reached.values()) |*n| n.deinit(gpa);
            reached.deinit(gpa);
        }
        try number.siteRows(gpa, store, &returns, root, &reached);
        var nodes: std.ArrayList(ir.NodeId) = .empty;
        defer nodes.deinit(gpa);
        for (reached.values()) |numbering| for (numbering.order.items) |n| {
            // A row `outline` made is not simplified, so N14a's check does not read its calls.
            const nd = store.node(n);
            if (nd.op == .call) {
                const callee = ir.RowId.of(nd.payload);
                const made = for (outlined) |o| {
                    if (canonical(store, o) == callee) break true;
                } else false;
                if (made) continue;
            }
            try nodes.append(gpa, n);
        };
        if (!try scalar.noneRewritable(gpa, store, types, nodes.items)) return error.InvariantBroken;
    }
    // L2: no loop of a finished row matches a loop rule.
    var returns = try live.Returns.init(gpa, store);
    defer returns.deinit(gpa);
    for (0..store.rows.items.len) |i| {
        const r = RowId.of(@intCast(i));
        if (store.row(r).merged_into != null) continue;
        var p = try place.plan(gpa, store, &returns, r, .simplify);
        defer p.deinit();
        if (!try loops.noneRewritable(gpa, store, types, &p)) return error.InvariantBroken;
        // L2: at a site that opts into layer L, no law applies to a finished row.
        if (with_laws and !try lawsNoneRewritable(gpa, b, &p)) return error.InvariantBroken;
    }
}

fn lawsNoneRewritable(gpa: Allocator, b: *const Builder, p: *const place.Plan) Allocator.Error!bool {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    return laws.noneRewritable(arena.allocator(), p, b);
}

const testing = std.testing;

test "components run callee first and recursion is recorded" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    // r0 calls r1; r1 calls itself.
    const leaf = try b.beginRow(&.{i64_ty}, i64_ty);
    try b.endRow(.{ .value = &.{ir.Ref.rowParam(0)} });
    const root = try b.beginRow(&.{i64_ty}, i64_ty);
    const c = try b.callRow(leaf, &.{ir.Ref.rowParam(0)});
    try b.endRow(.{ .value = &.{c} });
    const rec = try b.beginRow(&.{i64_ty}, i64_ty);
    const again = try b.callRow(rec, &.{ir.Ref.rowParam(0)});
    // Not a tail call, so the row stays recursive (a tail call becomes a loop, N12).
    try b.endRow(.{ .value = &.{try b.call(.i64, .plus_wrap, &.{ again, ir.Ref.rowParam(0) })} });

    const comps = try components(testing.allocator, &store);
    defer {
        for (comps) |comp| testing.allocator.free(comp);
        testing.allocator.free(comps);
    }
    try testing.expectEqual(@as(usize, 3), comps.len);
    const pos = struct {
        fn of(cs: []const []RowId, r: RowId) usize {
            for (cs, 0..) |comp, i| if (comp[0] == r) return i;
            unreachable; // the component list covers every row
        }
    };
    try testing.expect(pos.of(comps, leaf) < pos.of(comps, root));

    const stats = try runTo(testing.allocator, &b, root, &.{}, .finalized);
    try testing.expectEqual(@as(u32, 3), stats.components);
    try testing.expectEqual(@as(u32, 0), stats.rounds);
    try testing.expect(store.row(rec).recursive);
    try testing.expect(!store.row(root).recursive);
}

test "a round that changes nothing measurable is a compiler bug" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    const only = try b.beginRow(&.{i64_ty}, i64_ty);
    try b.endRow(.{ .value = &.{ir.Ref.rowParam(0)} });

    const Liar = struct {
        fn run(_: *anyopaque, _: *ir.Store, _: *types_mod.Types, _: []const RowId) Allocator.Error!bool {
            return true;
        }
    };
    var dummy: u8 = 0;
    const pass: Pass = .{ .name = "liar", .run = Liar.run, .ctx = &dummy };
    try testing.expectError(error.MeasureDidNotFall, run(testing.allocator, &b, only, &.{pass}));
}
