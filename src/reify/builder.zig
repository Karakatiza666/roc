//! The builder: smart constructors over the rule table (I4).
//!
//! Every node is built here. A constructor first tries the rules of the table
//! whose root is the node's op; a rule that matches builds its result through
//! the same constructors, so a result that is itself a redex is rewritten at
//! once. A node no rule rewrites is hash-consed: an identical node in a region
//! that encloses the current one is returned instead of a new node.
//!
//! Test builds and `zig build reify-rules` also get the knockout switch, which
//! disables one rule, and the rules-off mode, which disables all of them, so
//! the derivation tool can build a redex without it being rewritten.

const std = @import("std");
const collections = @import("collections");
const builtin = @import("builtin");
const ir = @import("ir.zig");
const types_mod = @import("types.zig");
const prims = @import("prims.zig");
const table = @import("rules/table.zig");
const equal = @import("equal.zig");
const polarity = @import("polarity.zig");
const match = @import("match.zig");
const provenance = @import("provenance.zig");
const scalar = @import("scalar.zig");
const laws_mod = @import("laws.zig");
const ranges = @import("ranges.zig");

const Allocator = std.mem.Allocator;
const Ref = ir.Ref;
const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const RowId = ir.RowId;
const TyId = ir.TyId;
const NameId = types_mod.NameId;
const LitId = ir.LitId;
const Op = ir.Op;

/// Whether the knockout switch and the rules-off mode are compiled in.
pub const hooks_enabled = builtin.is_test or @hasDecl(@import("root"), "reify_rule_hooks");

/// What a node's constructor receives, before any rule runs.
pub const NodeSpec = struct {
    op: Op,
    payload: u32 = 0,
    args: []const Ref = &.{},
    tys: []const TyId,
    regions: []const RegionId = &.{},
    aux: []const u32 = &.{},
};

/// A fact a dominating test established: the node `ref` has arm `key`. The
/// key of a `Bool` arm is 0 or 1. The key of a tag arm is the index of the
/// tag's name (`types.NameId`), so it holds whatever union the tag is read at.
/// An arm of a literal switch also states the literal: `lit` for a keyed arm,
/// and for the default arm the keys it excludes, in `excluded`.
pub const Fact = struct {
    ref: Ref,
    key: u32,
    /// The region the fact holds in: the arm, operand or loop body whose
    /// test or index established it. N13u reads it as the region an interval
    /// computed from the fact holds in.
    region: RegionId,
    lit: ?LitId = null,
    excluded: ir.Span = .empty,
    /// Set when `ref` is the index parameter of the body of a `ForList` over
    /// a list: the fact then names no arm, and only N13m reads it.
    loop: ?ListLoop = null,
    /// Set when `ref` is the index parameter of the body of a `ForRange`: its
    /// interval (N13u). The fact names no arm, and only N13u reads it.
    index: ?ir.Interval = null,

    /// Whether the fact is a test's arm, which names an arm key.
    fn isTest(f: Fact) bool {
        return f.loop == null and f.index == null;
    }
};

/// The list a `ForList` body runs over, and the body's element parameter.
pub const ListLoop = struct { list: Ref, element: Ref };

const OpenRegion = struct {
    /// The region nodes are built in: the region the caller opened, or the
    /// join the last exiting switch in it continues in.
    region: RegionId,
    fact_mark: u32,
    /// Where this region's exiting switches start in `Builder.links`.
    link_mark: u32,
};

/// An exiting switch of a region still open: the region it ends, and the
/// join the code after it continues in, or `none` where every path exits.
const Link = struct {
    owner: RegionId,
    sw: NodeId,
    join: RegionId,
};

/// The context rules that are algorithms, not rows (plan 3.3): N7b over
/// positions, N13r over a switch's arms, N13w over the arms that reach a
/// rejected literal, N13m over the facts of a bound, N13d over `Bool.not`,
/// N14a over a call, N13u over the intervals of the fact stack, and N15c's
/// parameter half over the root's parameter positions, which the rule
/// table's terms do not name. A test turns one off to see its rule stop.
pub const Algorithm = enum {
    interchange,
    /// N15c's parameter half: two root parameters in parameter order.
    param_order,
    /// N13u: a comparison with a literal that an interval decides.
    range_compare,
    /// N13u: a checked `plus`, `minus` or `times` that an interval proves
    /// fits is speculatable in the regions of its facts.
    range_fit,
    /// N13u with N15a: a checked `plus` chain whose operands' intervals
    /// prove no grouping overflows is one `Prim`.
    range_chain,
    case_of_case,
    rejected_arm,
    bounded_get,
    decided_not,
    scalar_call,
    /// The laws of layer L (`laws.zig`), N16a to N16f.
    law_map,
    law_keep_if,
    law_fold,
    law_fusion,
    law_iter_map,
    law_is_empty,
    /// N11n: a general loop's leading test that every edge decides.
    decided_test,
    /// N11o: a derived counter of a bounded loop.
    derived_counter,
};

/// The rules on exits and joins (normal-form 3.11), which run when an
/// exiting switch's region closes. T1 is how the walk builds them.
pub const ExitRule = enum { t2, t3, t4, t5, t6 };

/// The structural key of a node for hash-consing: a slice of `key_words`.
const NodeKey = struct { start: u32, len: u32 };

const NodeKeyContext = struct {
    words: *const std.ArrayList(u32),

    pub fn hash(ctx: NodeKeyContext, key: NodeKey) u64 {
        return std.hash.Wyhash.hash(0, std.mem.sliceAsBytes(ctx.words.items[key.start..][0..key.len]));
    }

    pub fn eql(ctx: NodeKeyContext, a: NodeKey, b: NodeKey) bool {
        return std.mem.eql(u32, ctx.words.items[a.start..][0..a.len], ctx.words.items[b.start..][0..b.len]);
    }
};

const LitKey = struct {
    ty: TyId,
    tag: u8,
    bits: u128,
    str: ir.Span,
};

const LitKeyContext = struct {
    store: *const ir.Store,

    pub fn hash(ctx: LitKeyContext, key: LitKey) u64 {
        var h = std.hash.Wyhash.init(0);
        h.update(std.mem.asBytes(&key.ty));
        h.update(&.{key.tag});
        h.update(std.mem.asBytes(&key.bits));
        if (key.tag == 3 or key.tag == 5) h.update(ctx.store.byteSlice(key.str));
        return h.final();
    }

    pub fn eql(ctx: LitKeyContext, a: LitKey, b: LitKey) bool {
        if (a.ty != b.ty or a.tag != b.tag or a.bits != b.bits) return false;
        if (a.tag != 3 and a.tag != 5) return true;
        return std.mem.eql(u8, ctx.store.byteSlice(a.str), ctx.store.byteSlice(b.str));
    }
};

/// What decides whether a node of an op is speculatable (normal-form 1.1).
/// The list is covered by the normal-form version (`mod.zig`).
pub const OpSpeculatable = enum {
    always,
    never,
    /// The builtin's entry in `prims.zig`.
    by_prim,
    /// The called row's flag.
    by_row,
    /// Every region: speculatable, and ending in a value or a `Continue`.
    by_regions,
};

/// The rule for nodes of `op`.
pub fn opSpeculatable(op: Op) OpSpeculatable {
    return switch (op) {
        .lit, .record, .tuple, .list, .tag, .wrap, .unwrap, .closure, .field, .index, .opt_field, .lambda => .always,
        // `Payload` and `Elem` are defined only under the test that dominates them.
        .payload, .elem, .crash, .derived, .loop, .apply => .never,
        .prim => .by_prim,
        .call => .by_row,
        .and_, .or_, .switch_, .for_range, .for_list => .by_regions,
    };
}

/// What makes the row a call specializes to (N8i): `row` with parameter
/// `param` bound to a closure of `closure`, whose captures become that
/// many parameters in its place. Returns the finalized row, or null where
/// the closure's row is not finalized yet, as in the component being
/// simplified.
pub const Specializer = struct {
    ctx: *anyopaque,
    run: *const fn (ctx: *anyopaque, b: *Builder, row: RowId, param: u32, closure: RowId, captures: []const TyId) SpecializeError!?Specialized,
};

/// A row a call specializes to, and, where finalizing it renumbered its
/// parameters (N8f), their new order by the index they were built with.
pub const Specialized = struct {
    row: RowId,
    order: ?[]const u32,
};

/// What a call of a row N14a splits calls instead: the row with the split
/// parameters, in its order when finalizing it renumbered them, and the
/// shape of each parameter of the row the call named.
pub const Scalarized = struct {
    row: RowId,
    order: ?[]const u32,
    shapes: []const scalar.Shape,
};

/// The row a call of a finalized row (N14a) is made to: `row` with each
/// parameter its shape splits replaced by the components. Returns null where
/// no parameter of the row splits.
pub const Scalarizer = struct {
    ctx: *anyopaque,
    run: *const fn (ctx: *anyopaque, b: *Builder, row: RowId) SpecializeError!?Scalarized,
};

/// The row a closure of a row that a law of layer L built names (`laws.zig`):
/// the row itself, or a row that keeps the closure's convention, and the
/// captures that row still reads, by their index among the built row's.
pub const LawClosure = struct { row: RowId, kept: []const u32 };

/// Simplifies and finalizes `row`, a row a law just built whose first
/// `captures` parameters are the values a closure of it captures, and gives
/// the row a closure of it names. Returns null where it stopped with an
/// error, which the driver keeps.
///
/// `inline_row` builds the body of `row` in the current region over `args`
/// for its parameters: the known function a law calls, inlined (N16c, N16d).
/// It returns null for a row that cannot be inlined, a recursive one or one
/// whose body can end in `Return` in a nested region (V1).
pub const Laws = struct {
    ctx: *anyopaque,
    close: *const fn (ctx: *anyopaque, b: *Builder, row: RowId, captures: u32) SpecializeError!?LawClosure,
    inline_row: *const fn (ctx: *anyopaque, b: *Builder, row: RowId, args: []const Ref, ty: TyId) Allocator.Error!?Ref,
};

/// Why a specialization stopped: the driver's errors, which the builder
/// hands back through the call it was building.
pub const SpecializeError = error{ MeasureDidNotFall, RoundBoundExceeded, InvariantBroken } || Allocator.Error;

/// The smart-constructor builder over one store.
pub const Builder = struct {
    gpa: Allocator,
    store: *ir.Store,
    types: *types_mod.Types,
    row: RowId = RowId.of(0),
    open: std.ArrayList(OpenRegion) = .empty,
    facts: std.ArrayList(Fact) = .empty,
    cons: std.HashMapUnmanaged(NodeKey, NodeId, NodeKeyContext, std.hash_map.default_max_load_percentage) = .empty,
    key_words: std.ArrayList(u32) = .empty,
    /// Per node: the previous node with the same key, for keys built in several regions.
    same_key: std.ArrayList(NodeId) = .empty,
    lits: std.HashMapUnmanaged(LitKey, LitId, LitKeyContext, std.hash_map.default_max_load_percentage) = .empty,
    /// The exiting switches of the open regions, innermost last.
    links: std.ArrayList(Link) = .empty,
    /// Per region: how many nodes sit in it, nested regions not counted.
    region_nodes: std.ArrayList(u32) = .empty,
    /// Per region: the values its parameters stand for while a join is
    /// inlined at a jump.
    param_subst: collections.DenseMapUnmanaged(RegionId, []const Ref) = .empty,
    /// Per node: its latest copy, reused while the copy is visible.
    copy_of: std.ArrayList(?Ref) = .empty,
    /// Per region: its latest copy.
    region_copy: std.ArrayList(RegionId) = .empty,
    /// The named primitives this store holds, by `owner ++ "\x00" ++ method`.
    named_prims: std.StringHashMapUnmanaged(ir.PrimId) = .empty,
    hooks: if (hooks_enabled) Hooks else void = if (hooks_enabled) .{} else {},
    /// Where set, a call that passes a known closure for a function
    /// parameter of a finalized row calls a row specialized to it (N8i,
    /// N8d). The driver sets it; the row is simplified and finalized before
    /// the call is built.
    specializer: ?Specializer = null,
    /// Where set, a call of a finalized row with an aggregate parameter that
    /// the row only reads by field or index calls the row with the parameter
    /// split (N14a). The driver sets it.
    scalarizer: ?Scalarizer = null,
    /// Where set, the site opts into layer L (`laws.zig`, normal-form 3.16),
    /// and a row a law builds is simplified and finalized through it. The
    /// driver sets it for a `Code.Lawful(f)` site only.
    laws: ?Laws = null,
    /// The value switch output that the switch being built is the only reader
    /// of, which the rebuild knows from the placement's uses: N13r moves the
    /// switch into the arms of the value switch only then, so the value switch
    /// dies and nothing is computed twice.
    sole_reader: ?Ref = null,
    /// While case-of-case copies an outer arm (N13r): the switch output that
    /// the arm reads, and the known value it stands for in the arm.
    case_subst: ?struct { from: Ref, to: Ref } = null,
    /// The origins of what is being built (N10): every node built, or found
    /// again by hash-consing, takes them. The walk sets one per expression,
    /// and a rebuild the copied node's.
    origins: []const provenance.OriginId = &.{},

    /// The test hooks: which rules are disabled, and how often each rule fired.
    pub const Hooks = struct {
        rules_off: bool = false,
        knocked_out: [table.count]bool = @splat(false),
        fired: [table.count]u32 = @splat(0),
        /// The rewrites an algorithm made rather than a row: N7 over a
        /// literal switch, N13d over switches and operands, and the exit rules.
        algorithm_steps: u32 = 0,
        exits_off: std.EnumSet(ExitRule) = .empty,
        exits_fired: std.EnumArray(ExitRule, u32) = .initFill(0),
        algorithms_off: std.EnumSet(Algorithm) = .empty,
        algorithms_fired: std.EnumArray(Algorithm, u32) = .initFill(0),
        /// Where set, the driver's placements break ties at random from it
        /// (L6, `place.Ties`).
        shuffle: ?std.Random = null,
    };

    fn exitRuleOn(self: *Builder, rule: ExitRule) bool {
        if (!hooks_enabled) return true;
        if (self.hooks.rules_off or self.hooks.exits_off.contains(rule)) return false;
        return true;
    }

    fn exitRuleFired(self: *Builder, rule: ExitRule) void {
        if (!hooks_enabled) return;
        self.hooks.exits_fired.getPtr(rule).* += 1;
        self.hooks.algorithm_steps += 1;
    }

    pub fn algorithmOn(self: *const Builder, a: Algorithm) bool {
        if (!hooks_enabled) return true;
        return !self.hooks.rules_off and !self.hooks.algorithms_off.contains(a);
    }

    pub fn algorithmFired(self: *Builder, a: Algorithm) void {
        if (!hooks_enabled) return;
        self.hooks.algorithms_fired.getPtr(a).* += 1;
        self.hooks.algorithm_steps += 1;
    }

    fn algorithmStep(self: *Builder) void {
        if (hooks_enabled) self.hooks.algorithm_steps += 1;
    }

    pub fn init(gpa: Allocator, store: *ir.Store, types: *types_mod.Types) Builder {
        return .{ .gpa = gpa, .store = store, .types = types };
    }

    pub fn deinit(self: *Builder) void {
        self.open.deinit(self.gpa);
        self.facts.deinit(self.gpa);
        self.cons.deinit(self.gpa);
        self.key_words.deinit(self.gpa);
        self.same_key.deinit(self.gpa);
        self.lits.deinit(self.gpa);
        self.links.deinit(self.gpa);
        self.region_nodes.deinit(self.gpa);
        self.param_subst.deinit(self.gpa);
        self.copy_of.deinit(self.gpa);
        self.region_copy.deinit(self.gpa);
        var keys = self.named_prims.keyIterator();
        while (keys.next()) |k| self.gpa.free(k.*);
        self.named_prims.deinit(self.gpa);
    }

    fn trackRegion(self: *Builder, r: RegionId) Allocator.Error!void {
        std.debug.assert(r.index() == self.region_nodes.items.len);
        try self.region_nodes.append(self.gpa, 0);
        try self.region_copy.append(self.gpa, RegionId.none);
    }

    fn pushOpen(self: *Builder, r: RegionId, fact_mark: usize) Allocator.Error!void {
        try self.open.append(self.gpa, .{ .region = r, .fact_mark = @intCast(fact_mark), .link_mark = @intCast(self.links.items.len) });
    }

    /// The region nodes are built in.
    pub fn current(self: *const Builder) RegionId {
        return self.open.items[self.open.items.len - 1].region;
    }

    /// Whether a row is being built: `beginRow` ran and `endRow` has not.
    pub fn building(self: *const Builder) bool {
        return self.open.items.len > 0;
    }

    /// Whether the region nodes are built in is the row body, or a join the
    /// row body continued in, so a terminator ends the row (`endRow`).
    pub fn atRowBody(self: *const Builder) bool {
        return self.open.items.len == 1;
    }

    /// Start a row with these parameter types; its body becomes the current region.
    pub fn beginRow(self: *Builder, params: []const TyId, result: TyId) Allocator.Error!RowId {
        std.debug.assert(self.open.items.len == 0);
        const row = RowId.of(@intCast(self.store.rows.items.len));
        self.row = row;
        self.cons.clearRetainingCapacity();
        self.key_words.clearRetainingCapacity();
        const param_span = try self.store.addTys(params);
        const body = try self.store.appendRegion(.{
            .kind = .row_body,
            .row = row,
            .parent = .none,
            .owner = .none,
            .params = .empty,
            .end = .{ .kind = .open, .target = 0, .refs = .empty },
            .depth = 0,
            .speculatable = true,
        });
        try self.store.rows.append(self.gpa, .{ .params = param_span, .result = result, .body = body, .recursive = false, .speculatable = false });
        try self.trackRegion(body);
        try self.pushOpen(body, self.facts.items.len);
        return row;
    }

    /// Start a new body for the existing row `row`, which becomes the
    /// current region, as `beginRow` starts one for a new row. The rebuild
    /// (`rebuild.zig`) copies the old body into it; the old body's regions
    /// and nodes stay in the store, and nothing reaches them once the row
    /// ends. The row keeps its `speculatable` flag until `endRow`.
    pub fn rebuildRow(self: *Builder, row: RowId) Allocator.Error!void {
        std.debug.assert(self.open.items.len == 0);
        self.row = row;
        self.cons.clearRetainingCapacity();
        self.key_words.clearRetainingCapacity();
        const body = try self.store.appendRegion(.{
            .kind = .row_body,
            .row = row,
            .parent = .none,
            .owner = .none,
            .params = .empty,
            .end = .{ .kind = .open, .target = 0, .refs = .empty },
            .depth = 0,
            .speculatable = true,
        });
        self.store.rows.items[row.index()].body = body;
        try self.trackRegion(body);
        try self.pushOpen(body, self.facts.items.len);
    }

    /// Close the row body with `end`. A `Return` the body ends in is its
    /// value (T6).
    pub fn endRow(self: *Builder, end: EndSpec) Allocator.Error!void {
        std.debug.assert(self.open.items.len == 1);
        const body = self.store.row(self.row).body;
        // The row's value, where the body continued in the join of an
        // exiting switch, leaves the row from that join: it is a `Return`,
        // which the exit rules read as the terminator it is, and T6 makes
        // the body's own end a value again.
        const continued = self.links.items.len > self.open.items[0].link_mark;
        if (continued and end == .value) {
            std.debug.assert(end.value.len == 1);
            try self.close(.{ .return_ = end.value[0] });
        } else try self.close(end);
        const e = self.store.region(body).end;
        if (e.kind == .return_ and self.exitRuleOn(.t6)) {
            self.store.setEnd(body, .{ .kind = .value, .target = 0, .refs = e.refs });
            self.exitRuleFired(.t6);
        }
        const r = self.store.region(body);
        self.store.rows.items[self.row.index()].speculatable = r.speculatable and r.end.kind == .value;
    }

    /// Close the lambda body `body`, the current region or the region a
    /// join of it continues, with `end`, as `endRow` closes a row body: a
    /// value after a join leaves the lambda in `Return`, and a `Return` the
    /// body ends in is its value (T6).
    pub fn endLambda(self: *Builder, body: RegionId, end: EndSpec) Allocator.Error!void {
        std.debug.assert(self.store.region(body).kind == .lambda_body);
        const top = self.open.items[self.open.items.len - 1];
        const continued = self.links.items.len > top.link_mark;
        if (continued and end == .value) {
            std.debug.assert(end.value.len == 1);
            try self.close(.{ .return_ = end.value[0] });
        } else try self.close(end);
        const e = self.store.region(body).end;
        if (e.kind == .return_ and self.exitRuleOn(.t6)) {
            self.store.setEnd(body, .{ .kind = .value, .target = 0, .refs = e.refs });
            self.exitRuleFired(.t6);
        }
    }

    /// What one row's construction holds while another row is built inside
    /// it: a call names a callee that the walk describes on the spot.
    pub const Suspended = struct {
        row: RowId,
        open: std.ArrayList(OpenRegion),
        facts: std.ArrayList(Fact),
        links: std.ArrayList(Link),
        cons: std.HashMapUnmanaged(NodeKey, NodeId, NodeKeyContext, std.hash_map.default_max_load_percentage),
        key_words: std.ArrayList(u32),
    };

    /// Set the row being built aside, so another can begin; `resumeRow`
    /// takes it back once that one ends.
    pub fn suspendRow(self: *Builder) Suspended {
        const s: Suspended = .{ .row = self.row, .open = self.open, .facts = self.facts, .links = self.links, .cons = self.cons, .key_words = self.key_words };
        self.open = .empty;
        self.facts = .empty;
        self.links = .empty;
        self.cons = .empty;
        self.key_words = .empty;
        return s;
    }

    /// Free a row `suspendRow` set aside that is never taken back: the walk
    /// abandoned the site it belongs to.
    pub fn dropSuspended(self: *Builder, s: Suspended) void {
        var dropped = s;
        dropped.open.deinit(self.gpa);
        dropped.facts.deinit(self.gpa);
        dropped.links.deinit(self.gpa);
        dropped.cons.deinit(self.gpa);
        dropped.key_words.deinit(self.gpa);
    }

    /// Take back a row `suspendRow` set aside. The row built since has ended.
    pub fn resumeRow(self: *Builder, s: Suspended) void {
        std.debug.assert(self.open.items.len == 0 and self.links.items.len == 0);
        self.open.deinit(self.gpa);
        self.facts.deinit(self.gpa);
        self.links.deinit(self.gpa);
        self.cons.deinit(self.gpa);
        self.key_words.deinit(self.gpa);
        self.row = s.row;
        self.open = s.open;
        self.facts = s.facts;
        self.links = s.links;
        self.cons = s.cons;
        self.key_words = s.key_words;
    }

    /// Open a nested region; it becomes the current region.
    pub fn openRegion(self: *Builder, kind: ir.RegionKind, params: []const TyId) Allocator.Error!RegionId {
        std.debug.assert(kind != .row_body);
        const parent = self.current();
        const param_span = try self.store.addTys(params);
        const r = try self.store.appendRegion(.{
            .kind = kind,
            .row = self.row,
            .parent = parent,
            .owner = .none,
            .params = param_span,
            .end = .{ .kind = .open, .target = 0, .refs = .empty },
            .depth = self.store.region(parent).depth + 1,
            .speculatable = true,
        });
        try self.trackRegion(r);
        try self.pushOpen(r, self.facts.items.len);
        return r;
    }

    /// Open the arm of a `Bool` switch on `scrutinee` that `key` selects, under that fact.
    pub fn openArm(self: *Builder, scrutinee: Ref, key: u32) Allocator.Error!RegionId {
        if (std.debug.runtime_safety and self.types.get(self.store.refTy(self.row, scrutinee)) == .tag_union)
            @import("base").invariant("reify builder: a tag switch opens its arms by tag name", .{});
        const r = try self.openRegion(.arm, &.{});
        try self.facts.append(self.gpa, .{ .ref = scrutinee, .key = key, .region = r });
        return r;
    }

    /// Open the arm of a tag switch on `scrutinee` for the tag `name`, under
    /// the fact that the scrutinee is that tag.
    pub fn openTagArm(self: *Builder, scrutinee: Ref, name: NameId) Allocator.Error!RegionId {
        const r = try self.openRegion(.arm, &.{});
        try self.facts.append(self.gpa, .{ .ref = scrutinee, .key = name.index(), .region = r });
        return r;
    }

    /// Open arm `i` of a switch on `scrutinee` that keeps the arms of an
    /// existing switch over the same scrutinee type: a literal arm when `keys`
    /// is not empty, the tag of member `i` for a tag union, and else `Bool`
    /// arm `i`.
    pub fn openArmAt(self: *Builder, scrutinee: Ref, keys: []const u32, i: u32) Allocator.Error!RegionId {
        if (keys.len > 0) return self.openLitArm(scrutinee, keys, i);
        const ty = self.store.refTy(self.row, scrutinee);
        return switch (self.types.get(ty)) {
            .tag_union => |span| self.openTagArm(scrutinee, self.types.memberSlice(span)[i].name),
            .bool_, .str, .int, .float, .dec, .record, .tuple, .list, .nominal, .func, .opaque_, .recursive => self.openArm(scrutinee, i),
        };
    }

    /// Open arm `arm` of a literal switch on `scrutinee` whose keyed arms
    /// test `keys`, one `LitId` each in source order: under the fact that
    /// the scrutinee is `keys[arm]`, or, for the default arm at
    /// `keys.len`, that it is none of them.
    pub fn openLitArm(self: *Builder, scrutinee: Ref, keys: []const u32, arm: u32) Allocator.Error!RegionId {
        const r = try self.openRegion(.arm, &.{});
        try self.facts.append(self.gpa, if (arm < keys.len)
            .{ .ref = scrutinee, .key = arm, .region = r, .lit = LitId.of(keys[arm]) }
        else
            .{ .ref = scrutinee, .key = arm, .region = r, .excluded = try self.store.addWords(keys) });
        return r;
    }

    /// Open an `And` or `Or` operand after the first, under the fact that the
    /// operands before it decided nothing: `True` for `And`, `False` for `Or`.
    pub fn openOperand(self: *Builder, earlier: []const Ref, op: Op) Allocator.Error!RegionId {
        const r = try self.openRegion(.operand, &.{});
        const key: u32 = switch (op) {
            .and_ => 1,
            .or_ => 0,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .switch_, .for_range, .for_list, .loop, .lambda, .apply => unreachable, // openOperand is only called for the operands of an And or Or node
        };
        for (earlier) |e| try self.facts.append(self.gpa, .{ .ref = e, .key = key, .region = r });
        return r;
    }

    /// Note that the open region `body` is the body of a `ForList` over
    /// `list`: its index parameter is in range of `list`, and its element
    /// parameter is the element at that index (N13m). The fact holds until
    /// the body closes.
    pub fn noteListLoop(self: *Builder, body: RegionId, list: Ref) Allocator.Error!void {
        std.debug.assert(self.open.items[self.open.items.len - 1].region == body);
        try self.facts.append(self.gpa, .{
            .ref = Ref.regionParam(body, 0),
            .key = 0,
            .region = body,
            .loop = .{ .list = list, .element = Ref.regionParam(body, 1) },
        });
    }

    /// Note that the open region `body` is the body of a `ForRange` from
    /// `start` to `end`: its index parameter runs from the least value of
    /// `start`'s interval to the greatest of `end`'s, less one when the range
    /// excludes its end (N13u). The fact holds until the body closes.
    pub fn noteRangeLoop(self: *Builder, body: RegionId, start: Ref, end: Ref, inclusive: bool) Allocator.Error!void {
        std.debug.assert(self.open.items[self.open.items.len - 1].region == body);
        const a = self.rangeOf(start) orelse return;
        const b = self.rangeOf(end) orelse return;
        try self.facts.append(self.gpa, .{
            .ref = Ref.regionParam(body, 0),
            .key = 0,
            .region = body,
            .index = ranges.ofIndex(a.interval, b.interval, inclusive),
        });
    }

    /// How a region ends, as the caller states it.
    pub const EndSpec = union(ir.EndKind) {
        open: void,
        value: []const Ref,
        jump: struct { join: RegionId, args: []const Ref },
        return_: Ref,
        branch: NodeId,
        continue_: []const Ref,
        break_: []const Ref,
    };

    // N13d on a region's value: a `Bool` that a dominating arm or an earlier
    // `And` or `Or` operand decided is the literal it decided, so `if c a else c`
    // ends its `False` arm in `False` and meets `c and a`.
    fn decidedRefs(self: *Builder, refs: []const Ref) Allocator.Error!ir.Span {
        var out: ?[]Ref = null;
        defer if (out) |o| self.gpa.free(o);
        for (refs, 0..) |r, i| {
            if (self.types.get(self.store.refTy(self.row, r)) != .bool_) continue;
            const key = self.knownKey(r) orelse continue;
            if (out == null) out = try self.gpa.dupe(Ref, refs);
            out.?[i] = try self.litBool(key == 1);
        }
        return self.store.addRefs(out orelse refs);
    }

    fn endOf(self: *Builder, end: EndSpec) Allocator.Error!ir.End {
        return switch (end) {
            .open => unreachable, // callers pass the end of a region being closed, never an open one
            .value => |refs| .{ .kind = .value, .target = 0, .refs = try self.decidedRefs(refs) },
            .jump => |j| .{ .kind = .jump, .target = j.join.index(), .refs = try self.store.addRefs(j.args) },
            .return_ => |r| .{ .kind = .return_, .target = 0, .refs = try self.store.addRefs(&.{r}) },
            .branch => |n| .{ .kind = .branch, .target = n.index(), .refs = .empty },
            .continue_ => |refs| .{ .kind = .continue_, .target = 0, .refs = try self.store.addRefs(refs) },
            .break_ => |refs| .{ .kind = .break_, .target = 0, .refs = try self.store.addRefs(refs) },
        };
    }

    /// Close the current region with `end`, restoring the facts outside it.
    ///
    /// A region an exiting switch continued out of closes its last join, and
    /// then each of its exiting switches, innermost first, takes the exit
    /// rules T2 to T5 in the region the switch ends. A region that ends in
    /// `Branch` of an exiting switch takes them for that switch too.
    pub fn close(self: *Builder, end: EndSpec) Allocator.Error!void {
        const top = &self.open.items[self.open.items.len - 1];
        self.store.setEnd(top.region, try self.endOf(end));
        if (end == .branch) try self.links.append(self.gpa, .{ .owner = top.region, .sw = end.branch, .join = RegionId.none });
        while (self.links.items.len > self.open.items[self.open.items.len - 1].link_mark) {
            const link = self.links.pop().?;
            self.open.items[self.open.items.len - 1].region = link.owner;
            try self.finishExit(link);
        }
        const popped = self.open.pop().?;
        self.facts.shrinkRetainingCapacity(popped.fact_mark);
    }

    /// A join for the code after an exiting switch, with parameters of
    /// `params`: the values the switch's continuing arms jump to it with.
    /// It is not open yet; arms name it in `Jump`, and `continueIn` opens it.
    pub fn reserveJoin(self: *Builder, params: []const TyId) Allocator.Error!RegionId {
        const parent = self.current();
        const param_span = try self.store.addTys(params);
        const r = try self.store.appendRegion(.{
            .kind = .join,
            .row = self.row,
            .parent = parent,
            .owner = .none,
            .params = param_span,
            .end = .{ .kind = .open, .target = 0, .refs = .empty },
            .depth = self.store.region(parent).depth + 1,
            .speculatable = true,
        });
        try self.trackRegion(r);
        return r;
    }

    /// An exiting switch on `scrutinee` over closed `arms`: a switch whose
    /// arms end in terminators or in jumps to `joins`, and which delivers no
    /// value. The region it stands in ends in it, through `continueIn` or
    /// through `close(.{ .branch = .. })`.
    pub fn exitingSwitch(self: *Builder, scrutinee: Ref, arms: []const RegionId, joins: []const RegionId, keys: []const u32) Allocator.Error!NodeId {
        const r = try self.switchOn(scrutinee, arms, joins, &.{}, keys);
        std.debug.assert(r.kind == .node and self.store.node(r.nodeId()).op == .switch_);
        return r.nodeId();
    }

    /// End the current region in the exiting switch `sw`, and go on building
    /// in `join`, a join of `sw`, which the region's own end closes (T1).
    pub fn continueIn(self: *Builder, sw: NodeId, join: RegionId) Allocator.Error!void {
        const top = &self.open.items[self.open.items.len - 1];
        self.store.setEnd(top.region, .{ .kind = .branch, .target = sw.index(), .refs = .empty });
        try self.links.append(self.gpa, .{ .owner = top.region, .sw = sw, .join = join });
        top.region = join;
    }

    // The exit rules for one exiting switch, built in the region it ends,
    // which is current. A join that no path jumps to is dropped; one with no
    // nodes of its own is substituted into its jumps (T4); one that one path
    // jumps to is inlined there (T2). A switch every path of which jumps to
    // the join it keeps is a value switch, and the join's code follows it
    // (T5). A switch every arm of which ends in one kind of terminator is a
    // value switch, and the region ends in that terminator over its
    // outputs (T3).
    fn finishExit(self: *Builder, link: Link) Allocator.Error!void {
        // What the rules build here stands for the exiting switch.
        const origins = try self.gpa.dupe(provenance.OriginId, self.store.provenance.of(link.sw));
        defer self.gpa.free(origins);
        const outer = self.origins;
        self.origins = origins;
        defer self.origins = outer;
        var join = link.join;
        if (join != RegionId.none) {
            var jumps: std.ArrayList(RegionId) = .empty;
            defer jumps.deinit(self.gpa);
            for (self.store.regionSlice(self.store.node(link.sw).regions)) |r| {
                if (r != join) try self.collectJumps(r, join, &jumps);
            }
            if (jumps.items.len == 0) {
                try self.dropRegion(link.sw, join);
                join = RegionId.none;
            } else if (self.region_nodes.items[join.index()] == 0 and self.exitRuleOn(.t4)) {
                for (jumps.items) |x| try self.substituteEnd(x, join);
                try self.dropRegion(link.sw, join);
                join = RegionId.none;
                self.exitRuleFired(.t4);
            } else if (jumps.items.len == 1 and self.exitRuleOn(.t2)) {
                try self.inlineJoin(jumps.items[0], join);
                try self.dropRegion(link.sw, join);
                join = RegionId.none;
                self.exitRuleFired(.t2);
            }
        }
        const sw = self.store.node(link.sw);
        const arms = try self.gpa.dupe(RegionId, self.store.regionSlice(sw.regions)[0..sw.payload]);
        defer self.gpa.free(arms);
        const keys = try self.gpa.dupe(u32, self.store.wordSlice(sw.aux));
        defer self.gpa.free(keys);
        const scrutinee = self.store.refSlice(sw.args)[0];
        if (join != RegionId.none) {
            if (self.store.regionSlice(sw.regions).len != arms.len + 1) return;
            for (arms) |a| {
                const e = self.store.region(a).end;
                if (e.kind != .jump or e.target != join.index()) return;
            }
            if (!self.exitRuleOn(.t5)) return;
            // T5: every arm jumps to the join, so the jumps are the values
            // of a value switch, and the join's code runs after it.
            for (arms) |a| self.store.regions.items(.end)[a.index()].kind = .value;
            const params = try self.gpa.dupe(TyId, self.store.tySlice(self.store.region(join).params));
            defer self.gpa.free(params);
            const v = try self.switchOn(scrutinee, arms, &.{}, params, keys);
            const outs = try self.gpa.alloc(Ref, params.len);
            defer self.gpa.free(outs);
            for (outs, 0..) |*o, k| o.* = if (v.kind == .node and params.len > 1) Ref.node(v.nodeId(), @intCast(k)) else v;
            // The exiting switch is dead now, and a join counts only live nodes.
            self.region_nodes.items[link.owner.index()] -= 1;
            try self.param_subst.put(self.gpa, join, outs);
            defer _ = self.param_subst.remove(join);
            const end = try self.copyEnd(join);
            self.store.setEnd(self.current(), end);
            self.exitRuleFired(.t5);
            return;
        }
        // T3: one kind of terminator on every arm.
        const kind = self.store.region(arms[0]).end.kind;
        switch (kind) {
            .return_, .continue_, .break_ => {},
            .open, .value, .jump, .branch => return,
        }
        const width = self.store.region(arms[0]).end.refs.len;
        for (arms) |a| {
            const e = self.store.region(a).end;
            if (e.kind != kind or e.refs.len != width) return;
        }
        if (self.store.regionSlice(sw.regions).len != arms.len) return;
        if (!self.exitRuleOn(.t3)) return;
        const tys = try self.gpa.alloc(TyId, width);
        defer self.gpa.free(tys);
        for (self.store.refSlice(self.store.region(arms[0]).end.refs), tys) |r, *t| t.* = self.store.refTy(self.row, r);
        for (arms) |a| self.store.regions.items(.end)[a.index()].kind = .value;
        const v = try self.switchOn(scrutinee, arms, &.{}, tys, keys);
        const outs = try self.gpa.alloc(Ref, width);
        defer self.gpa.free(outs);
        for (outs, 0..) |*o, k| o.* = if (v.kind == .node and width > 1) Ref.node(v.nodeId(), @intCast(k)) else v;
        self.region_nodes.items[link.owner.index()] -= 1;
        self.store.setEnd(self.current(), .{ .kind = kind, .target = 0, .refs = try self.store.addRefs(outs) });
        self.exitRuleFired(.t3);
    }

    // The regions in `r`'s paths that end in a jump to `join`: `r` itself,
    // or the arms and joins of the exiting switches its paths pass.
    fn collectJumps(self: *Builder, r: RegionId, join: RegionId, out: *std.ArrayList(RegionId)) Allocator.Error!void {
        const e = self.store.region(r).end;
        switch (e.kind) {
            .jump => if (e.target == join.index()) try out.append(self.gpa, r),
            .branch => for (self.store.regionSlice(self.store.node(NodeId.of(e.target)).regions)) |sub| try self.collectJumps(sub, join, out),
            .open, .value, .return_, .continue_, .break_ => {},
        }
    }

    // Remove region `r` from the regions `sw` owns.
    fn dropRegion(self: *Builder, sw: NodeId, r: RegionId) Allocator.Error!void {
        const old = self.store.regionSlice(self.store.node(sw).regions);
        var kept: std.ArrayList(RegionId) = .empty;
        defer kept.deinit(self.gpa);
        for (old) |o| if (o != r) try kept.append(self.gpa, o);
        self.store.nodes.items(.regions)[sw.index()] = try self.store.addRegionIds(kept.items);
    }

    // T4: region `x` jumps to `join`, whose end reads only its parameters and
    // values outside it; `x` ends in that end instead, over the jump's values.
    fn substituteEnd(self: *Builder, x: RegionId, join: RegionId) Allocator.Error!void {
        const jump = self.store.region(x).end;
        const args = try self.gpa.dupe(Ref, self.store.refSlice(jump.refs));
        defer self.gpa.free(args);
        const end = self.store.region(join).end;
        const refs = try self.gpa.dupe(Ref, self.store.refSlice(end.refs));
        defer self.gpa.free(refs);
        for (refs) |*r| {
            if (r.kind == .region_param and r.target == join.index()) r.* = args[r.output];
        }
        self.store.setEnd(x, .{ .kind = end.kind, .target = end.target, .refs = try self.store.addRefs(refs) });
    }

    // T2: region `x` is the one path that jumps to `join`; `x` ends in a copy
    // of the join, built in `x` under `x`'s facts, with the join's
    // parameters standing for the jump's values.
    fn inlineJoin(self: *Builder, x: RegionId, join: RegionId) Allocator.Error!void {
        const args = try self.gpa.dupe(Ref, self.store.refSlice(self.store.region(x).end.refs));
        defer self.gpa.free(args);
        try self.enter(x);
        try self.param_subst.put(self.gpa, join, args);
        defer _ = self.param_subst.remove(join);
        const end = try self.copyEnd(join);
        self.leave(end);
    }

    // Build in the closed region `x`, nested in the current region along
    // arms and joins, under the facts of the arms on the way.
    fn enter(self: *Builder, x: RegionId) Allocator.Error!void {
        const here = self.current();
        const mark = self.facts.items.len;
        var path: std.ArrayList(RegionId) = .empty;
        defer path.deinit(self.gpa);
        var cur = x;
        while (cur != here) : (cur = self.store.region(cur).parent) try path.append(self.gpa, cur);
        var i = path.items.len;
        while (i > 0) {
            i -= 1;
            const r = self.store.region(path.items[i]);
            switch (r.kind) {
                .arm => try self.pushArmFact(r.owner, path.items[i]),
                .join => {},
                .row_body, .operand, .loop_body, .lambda_body => unreachable, // the path runs along arms and joins only, as enter's contract states
            }
        }
        try self.pushOpen(x, mark);
    }

    fn leave(self: *Builder, end: ir.End) void {
        const top = self.open.pop().?;
        std.debug.assert(self.links.items.len == top.link_mark);
        self.store.setEnd(top.region, end);
        self.facts.shrinkRetainingCapacity(top.fact_mark);
    }

    // The fact arm `arm` of switch `sw` stands under.
    fn pushArmFact(self: *Builder, sw: NodeId, arm: RegionId) Allocator.Error!void {
        const nd = self.store.node(sw);
        const scrutinee = self.store.refSlice(nd.args)[0];
        const k: u32 = @intCast(std.mem.findScalar(RegionId, self.store.regionSlice(nd.regions), arm).?);
        const keys = self.store.wordSlice(nd.aux);
        if (keys.len == 0) return self.facts.append(self.gpa, .{ .ref = scrutinee, .key = self.armKey(scrutinee, k), .region = arm });
        try self.facts.append(self.gpa, if (k < keys.len)
            .{ .ref = scrutinee, .key = k, .region = arm, .lit = LitId.of(keys[k]) }
        else
            .{ .ref = scrutinee, .key = k, .region = arm, .excluded = nd.aux });
    }

    // A copy of region `r`'s end built in the current region, copying what
    // it reads that is not visible here.
    fn copyEnd(self: *Builder, r: RegionId) Allocator.Error!ir.End {
        const end = self.store.region(r).end;
        const old_refs = try self.gpa.dupe(Ref, self.store.refSlice(end.refs));
        defer self.gpa.free(old_refs);
        const refs = try self.gpa.alloc(Ref, old_refs.len);
        defer self.gpa.free(refs);
        for (old_refs, refs) |a, *o| o.* = try self.available(a);
        return switch (end.kind) {
            .open => unreachable, // copyEnd copies closed regions, whose end is never open
            .branch => .{ .kind = .branch, .target = (try self.available(Ref.of(NodeId.of(end.target)))).nodeId().index(), .refs = .empty },
            .jump => .{ .kind = .jump, .target = self.joinCopy(RegionId.of(end.target)).index(), .refs = try self.store.addRefs(refs) },
            .value, .return_, .continue_, .break_ => .{ .kind = end.kind, .target = 0, .refs = try self.store.addRefs(refs) },
        };
    }

    // The fact key of arm `k` of a switch on `scrutinee` that has no literal
    // keys: the arm number for a `Bool`, and the index of the name of
    // member `k` for a tag union.
    fn armKey(self: *const Builder, scrutinee: Ref, k: u32) u32 {
        return switch (self.types.get(self.store.refTy(self.row, scrutinee))) {
            .tag_union => |span| self.types.memberSlice(span)[k].name.index(),
            .bool_, .str, .int, .float, .dec, .record, .tuple, .list, .nominal, .func, .opaque_, .recursive => k,
        };
    }

    // The arm of a switch on `scrutinee` that the fact key `key` selects, when
    // the scrutinee's type has such an arm.
    fn armOfKey(self: *const Builder, scrutinee: Ref, key: u32) ?u32 {
        const ty = self.store.refTy(self.row, scrutinee);
        return switch (self.types.get(ty)) {
            .tag_union => self.types.memberIndex(ty, NameId.of(key)),
            .bool_ => if (key < 2) key else null,
            .str, .int, .float, .dec, .record, .tuple, .list, .nominal, .func, .opaque_, .recursive => null,
        };
    }

    /// The arm key a dominating test established for `ref`, if any: 0 or 1
    /// for a `Bool`, the index of the tag's name for a tag union (`Fact`).
    pub fn knownKey(self: *const Builder, ref: Ref) ?u32 {
        var i = self.facts.items.len;
        while (i > 0) {
            i -= 1;
            const f = self.facts.items[i];
            if (f.ref == ref and f.isTest()) return f.key;
        }
        return null;
    }

    /// Whether a dominating arm decided that `ref` is the literal `lit`: true
    /// where an arm keyed `lit` holds, false where an arm keyed on another
    /// literal holds or a default arm excludes `lit`, and null where no arm
    /// decided it.
    pub fn litFact(self: *const Builder, ref: Ref, lit: LitId) ?bool {
        var i = self.facts.items.len;
        while (i > 0) {
            i -= 1;
            const f = self.facts.items[i];
            if (f.ref != ref or !f.isTest()) continue;
            if (f.lit) |l| return l == lit;
            if (std.mem.findScalar(u32, self.store.wordSlice(f.excluded), lit.index()) != null) return false;
        }
        return null;
    }

    /// An integer literal of the integer type `ty`.
    pub fn litInt(self: *Builder, ty: TyId, value: i128) Allocator.Error!Ref {
        return self.litRef(ty, .{ .int = @bitCast(value) });
    }

    /// A `Bool` literal.
    pub fn litBool(self: *Builder, value: bool) Allocator.Error!Ref {
        return self.litRef(try self.types.boolTy(), .{ .bool_ = value });
    }

    /// A float literal of the float type `ty`, given by its bits.
    pub fn litFloatBits(self: *Builder, ty: TyId, bits: u64) Allocator.Error!Ref {
        return self.litRef(ty, .{ .float = bits });
    }

    /// A `Str` literal.
    pub fn litStr(self: *Builder, text: []const u8) Allocator.Error!Ref {
        const span = try self.store.addBytes(text);
        return self.litRef(try self.types.strTy(), .{ .str = span });
    }

    fn litRef(self: *Builder, ty: TyId, value: ir.LitValue) Allocator.Error!Ref {
        const id = try self.internLit(ty, value);
        return self.make(.{ .op = .lit, .payload = id.index(), .tys = &.{ty} });
    }

    /// Intern a literal value of type `ty`.
    pub fn internLit(self: *Builder, ty: TyId, value: ir.LitValue) Allocator.Error!LitId {
        const key: LitKey = switch (value) {
            .int => |b| .{ .ty = ty, .tag = 0, .bits = b, .str = .empty },
            .float => |b| .{ .ty = ty, .tag = 1, .bits = b, .str = .empty },
            .bool_ => |b| .{ .ty = ty, .tag = 2, .bits = @intFromBool(b), .str = .empty },
            .str => |s| .{ .ty = ty, .tag = 3, .bits = 0, .str = s },
            .dec => |b| .{ .ty = ty, .tag = 4, .bits = b, .str = .empty },
            .bytes => |s| .{ .ty = ty, .tag = 5, .bits = 0, .str = s },
        };
        const gop = try self.lits.getOrPutContext(self.gpa, key, .{ .store = self.store });
        if (gop.found_existing) return gop.value_ptr.*;
        const id = LitId.of(@intCast(self.store.lits.items.len));
        try self.store.lits.append(self.gpa, .{ .ty = ty, .value = value });
        gop.value_ptr.* = id;
        return id;
    }

    /// `Prim(id, args)` with the result type the builtin gives.
    pub fn prim(self: *Builder, id: ir.PrimId, args: []const Ref) Allocator.Error!Ref {
        return self.make(.{ .op = .prim, .payload = id.index(), .args = args, .tys = &.{try self.primResultTy(id, args)} });
    }

    /// `owner.method(args)`, with the result type the builtin gives.
    pub fn call(self: *Builder, owner: prims.Owner, method: prims.Method, args: []const Ref) Allocator.Error!Ref {
        return self.prim(prims.find(owner, method).?, args);
    }

    /// `Record` of `ty` with its fields in the type's order.
    pub fn record(self: *Builder, ty: TyId, fields: []const Ref) Allocator.Error!Ref {
        return self.make(.{ .op = .record, .args = fields, .tys = &.{ty} });
    }

    /// `Record` of `ty` that sets only the members at `set`, which are
    /// optional or all of them, in the type's order; `fields` are their
    /// values in that order. A record that sets every member is the dense
    /// form `record` builds, so one value has one form (`ir.RecordForm`).
    pub fn recordSetting(self: *Builder, ty: TyId, set: []const u32, fields: []const Ref) Allocator.Error!Ref {
        std.debug.assert(set.len == fields.len);
        const members = self.types.memberSlice(self.types.get(ty).record);
        if (set.len == members.len) return self.record(ty, fields);
        return self.make(.{ .op = .record, .args = fields, .tys = &.{ty}, .aux = set });
    }

    /// Where the value of member `k` of the record type of the `record` node
    /// `nd` sits among the node's arguments, or null when the node leaves the
    /// member unset.
    pub fn recordArgAt(self: *const Builder, nd: ir.Node, k: u32) ?u32 {
        const members = self.types.memberSlice(self.types.get(self.store.tySlice(nd.tys)[0]).record);
        if (nd.args.len == members.len) return k;
        for (self.store.wordSlice(nd.aux), 0..) |set, at| {
            if (set == k) return @intCast(at);
        }
        return null;
    }

    /// `Tuple` of `ty`.
    pub fn tuple(self: *Builder, ty: TyId, elems: []const Ref) Allocator.Error!Ref {
        return self.make(.{ .op = .tuple, .args = elems, .tys = &.{ty} });
    }

    /// The tag `name` of the union `ty`, over `components`. The node holds the
    /// name, not a position, so it is the same node at every union that has the tag.
    pub fn tag(self: *Builder, ty: TyId, name: NameId, components: []const Ref) Allocator.Error!Ref {
        if (std.debug.runtime_safety and self.types.memberIndex(ty, name) == null)
            @import("base").invariant("reify builder: the union has no tag {s}", .{self.types.nameText(name)});
        return self.make(.{ .op = .tag, .payload = name.index(), .args = components, .tys = &.{ty} });
    }

    /// `Field(x, index)`, `index` in the record type's order.
    pub fn field(self: *Builder, x: Ref, field_index: u32) Allocator.Error!Ref {
        const rec = self.store.refTy(self.row, x);
        const members = self.types.memberSlice(self.types.get(rec).record);
        const fty = self.types.tySlice(members[field_index].tys)[0];
        return self.make(.{ .op = .field, .payload = field_index, .args = &.{x}, .tys = &.{fty} });
    }

    /// `Index(x, k)` of a tuple.
    pub fn index(self: *Builder, x: Ref, k: u32) Allocator.Error!Ref {
        const tup = self.store.refTy(self.row, x);
        const ety = self.types.tySlice(self.types.get(tup).tuple)[k];
        return self.make(.{ .op = .index, .payload = k, .args = &.{x}, .tys = &.{ety} });
    }

    /// `Payload(x, name, k)`: payload `k` of the tag `name` of a union value.
    pub fn payload(self: *Builder, x: Ref, name: NameId, k: u32) Allocator.Error!Ref {
        const un = self.store.refTy(self.row, x);
        const members = self.types.memberSlice(self.types.get(un).tag_union);
        const at = self.types.memberIndex(un, name).?;
        const pty = self.types.tySlice(members[at].tys)[k];
        return self.make(.{ .op = .payload, .payload = name.index(), .args = &.{x}, .tys = &.{pty}, .aux = &.{k} });
    }

    /// `Wrap(x)` into the nominal `ty`.
    pub fn wrap(self: *Builder, ty: TyId, x: Ref) Allocator.Error!Ref {
        return self.make(.{ .op = .wrap, .args = &.{x}, .tys = &.{ty} });
    }

    /// `Unwrap(x)` of a nominal to its backing type, unfolded (`Types.unfold`).
    pub fn unwrap(self: *Builder, x: Ref) Allocator.Error!Ref {
        const backing = try self.types.unfold(self.store.refTy(self.row, x));
        return self.make(.{ .op = .unwrap, .args = &.{x}, .tys = &.{backing} });
    }

    /// `Crash` of type `ty`, with its message.
    pub fn crash(self: *Builder, ty: TyId, message: Ref) Allocator.Error!Ref {
        return self.make(.{ .op = .crash, .payload = @backingInt(ir.CrashKind.written), .args = &.{message}, .tys = &.{ty} });
    }

    /// The crash of a literal that its conversion rejected, a `Crash` the
    /// compiler wrote rather than the author (`ir.CrashKind`).
    pub fn rejectedLiteral(self: *Builder, ty: TyId, message: Ref) Allocator.Error!Ref {
        return self.make(.{ .op = .crash, .payload = @backingInt(ir.CrashKind.rejected_literal), .args = &.{message}, .tys = &.{ty} });
    }

    /// The primitive `owner.method`: the table's entry when it holds one, and
    /// otherwise one this store names. A builtin the table lacks and a
    /// function of another package (N8h) are both named ones.
    pub fn namedPrim(self: *Builder, owner: []const u8, method: []const u8) Allocator.Error!ir.PrimId {
        return self.namedPrimWithRole(owner, method, .none);
    }

    /// `namedPrim`, for a builtin iterator procedure the checker gave a role
    /// (N11k). The role is part of the primitive's identity: two primitives
    /// with one owner and method and different roles are two primitives.
    pub fn namedPrimWithRole(self: *Builder, owner: []const u8, method: []const u8, role: ir.IteratorRole) Allocator.Error!ir.PrimId {
        if (role == .none) if (prims.findNamed(owner, method)) |id| return id;
        const key = try std.fmt.allocPrint(self.gpa, "{s}\x00{s}\x00{d}", .{ owner, method, @backingInt(role) });
        const gop = try self.named_prims.getOrPut(self.gpa, key);
        if (gop.found_existing) {
            self.gpa.free(key);
            return gop.value_ptr.*;
        }
        const id = ir.PrimId.of(@intCast(prims.table.len + self.store.named_prims.items.len));
        try self.store.named_prims.append(self.gpa, .{ .owner = try self.store.addBytes(owner), .method = try self.store.addBytes(method), .role = role });
        gop.value_ptr.* = id;
        return id;
    }

    /// `Prim(id, args)` of the type `ty` the checker solved for the call.
    pub fn primOf(self: *Builder, id: ir.PrimId, args: []const Ref, ty: TyId) Allocator.Error!Ref {
        return self.make(.{ .op = .prim, .payload = id.index(), .args = args, .tys = &.{ty} });
    }

    /// `Closure(row, captures)` of the function type `ty`. A closure that
    /// captures nothing, of a row that only calls another row with its own
    /// parameters in order, is a closure of that row (N8c), and so on to the
    /// end of such a chain, so a rebuild finds nothing more to do. A chain
    /// that comes back to a row it passed is a cycle of rows that only call
    /// each other, and stays where it is.
    pub fn closure(self: *Builder, row: RowId, captures: []const Ref, ty: TyId) Allocator.Error!Ref {
        if (captures.len == 0 and self.rulesActive()) {
            var target = row;
            var steps: usize = 0;
            while (self.etaTarget(target)) |next| {
                if (next == row or steps == self.store.rows.items.len) break;
                target = next;
                steps += 1;
            }
            if (target != row) {
                self.algorithmStep();
                return self.make(.{ .op = .closure, .payload = target.index(), .tys = &.{ty} });
            }
        }
        return self.make(.{ .op = .closure, .payload = row.index(), .args = captures, .tys = &.{ty} });
    }

    // The row that `row` only calls, with `row`'s parameters in order, when
    // `row` has ended and its body is that call.
    fn etaTarget(self: *const Builder, row: RowId) ?RowId {
        const info = self.store.row(row);
        const end = self.store.region(info.body).end;
        if (end.kind != .value or end.refs.len != 1) return null;
        const ref = self.store.refSlice(end.refs)[0];
        if (ref.kind != .node) return null;
        const nd = self.store.node(ref.nodeId());
        if (nd.op != .call or nd.region != info.body) return null;
        const args = self.store.refSlice(nd.args);
        if (args.len != info.params.len) return null;
        for (args, 0..) |a, k| if (a != Ref.rowParam(@intCast(k))) return null;
        return RowId.of(nd.payload);
    }

    /// `Derived(method, subject)` over `args`, of type `ty`.
    pub fn derived(self: *Builder, method: []const u8, subject: TyId, args: []const Ref, ty: TyId) Allocator.Error!Ref {
        const name = try self.types.name(method);
        return self.make(.{ .op = .derived, .payload = name.index(), .args = args, .tys = &.{ty}, .aux = &.{subject.index()} });
    }

    /// `OptField(x, index)`: the optional field `index` of a record, as the
    /// `Try` of type `ty` that holds it.
    pub fn optField(self: *Builder, x: Ref, field_index: u32, ty: TyId) Allocator.Error!Ref {
        return self.make(.{ .op = .opt_field, .payload = field_index, .args = &.{x}, .tys = &.{ty} });
    }

    /// `Elem(list, index)` of the element type `ty`, under a bound that a
    /// dominating test proved.
    pub fn elem(self: *Builder, list: Ref, at: Ref, ty: TyId) Allocator.Error!Ref {
        return self.make(.{ .op = .elem, .args = &.{ list, at }, .tys = &.{ty} });
    }

    /// A `Dec` literal, by the bits of its `i128` representation.
    pub fn litDec(self: *Builder, bits: i128) Allocator.Error!Ref {
        return self.litRef(try self.types.decTy(), .{ .dec = @bitCast(bits) });
    }

    /// An embedded file's contents, a literal of the `List(U8)` type `ty`.
    pub fn litBytes(self: *Builder, ty: TyId, contents: []const u8) Allocator.Error!Ref {
        const span = try self.store.addBytes(contents);
        return self.litRef(ty, .{ .bytes = span });
    }

    /// `Call(row, args)`.
    pub fn callRow(self: *Builder, row: RowId, args: []const Ref) Allocator.Error!Ref {
        return self.callRowAt(row, args, self.store.row(row).result);
    }

    /// `Call(row, args)` of the type `ty`: the row's result type, or a wider
    /// one where the call is read at a wider union (design.md "Row Coercion
    /// Primitive"). The verifier checks that the result widens to `ty`.
    pub fn callRowAt(self: *Builder, row: RowId, args: []const Ref, ty: TyId) Allocator.Error!Ref {
        return self.make(.{ .op = .call, .payload = row.index(), .args = args, .tys = &.{ty} });
    }

    /// A switch on `scrutinee` with closed `arms` and `joins`, delivering
    /// `outputs`. A rule can replace it by a value that is not a switch, so
    /// the result is a reference: output `k` of a switch is `Ref.node(n, k)`
    /// where `n` is the result's node.
    pub fn switchOn(self: *Builder, scrutinee: Ref, arms: []const RegionId, joins: []const RegionId, outputs: []const TyId, keys: []const u32) Allocator.Error!Ref {
        const regions = try self.gpa.alloc(RegionId, arms.len + joins.len);
        defer self.gpa.free(regions);
        @memcpy(regions[0..arms.len], arms);
        @memcpy(regions[arms.len..], joins);
        return self.make(.{ .op = .switch_, .payload = @intCast(arms.len), .args = &.{scrutinee}, .tys = outputs, .regions = regions, .aux = keys });
    }

    /// A switch on the tag union `scrutinee` with one closed arm per tag in
    /// `names`, in `arms`, and closed `joins`, delivering `outputs`. The
    /// scrutinee's own type fixes the switch: it gets one arm per member of
    /// that type, in name order, found by name. A given arm for a tag the
    /// type does not have is dead, because the value cannot hold that tag, and
    /// is dropped. A member with no given arm is a compiler bug.
    pub fn tagSwitchOn(self: *Builder, scrutinee: Ref, names: []const NameId, arms: []const RegionId, joins: []const RegionId, outputs: []const TyId) Allocator.Error!Ref {
        const kept = try self.liveTagArms(scrutinee, names, arms);
        defer self.gpa.free(kept);
        return self.switchOn(scrutinee, kept, joins, outputs, &.{});
    }

    /// `tagSwitchOn` for an exiting switch: no outputs, and arms that end in
    /// terminators or in jumps to `joins`.
    pub fn exitingTagSwitch(self: *Builder, scrutinee: Ref, names: []const NameId, arms: []const RegionId, joins: []const RegionId) Allocator.Error!NodeId {
        const kept = try self.liveTagArms(scrutinee, names, arms);
        defer self.gpa.free(kept);
        return self.exitingSwitch(scrutinee, kept, joins, &.{});
    }

    /// Whether the type of `scrutinee` has the tag `name`: whether an arm for
    /// it is live. A caller that knows the answer can skip building a dead arm.
    pub fn tagLive(self: *const Builder, scrutinee: Ref, name: NameId) bool {
        return self.types.memberIndex(self.store.refTy(self.row, scrutinee), name) != null;
    }

    /// The arms of `arms`, which are for the tags `names`, that `scrutinee`'s
    /// type has, one per member in the type's order. The caller frees the result.
    pub fn liveTagArms(self: *Builder, scrutinee: Ref, names: []const NameId, arms: []const RegionId) Allocator.Error![]RegionId {
        std.debug.assert(names.len == arms.len);
        const ty = self.store.refTy(self.row, scrutinee);
        const members = self.types.memberSlice(self.types.get(ty).tag_union);
        const kept = try self.gpa.alloc(RegionId, members.len);
        errdefer self.gpa.free(kept);
        for (members, kept) |m, *arm| {
            const at = std.mem.findScalar(NameId, names, m.name) orelse
                @import("base").invariant("reify builder: a switch has no arm for the tag {s}", .{self.types.nameText(m.name)});
            arm.* = arms[at];
        }
        return kept;
    }

    /// `And(first, operands...)`, each later operand a closed region.
    pub fn andOf(self: *Builder, first: Ref, operands: []const RegionId) Allocator.Error!Ref {
        return self.make(.{ .op = .and_, .args = &.{first}, .tys = &.{try self.types.boolTy()}, .regions = operands });
    }

    /// `Or(first, operands...)`.
    pub fn orOf(self: *Builder, first: Ref, operands: []const RegionId) Allocator.Error!Ref {
        return self.make(.{ .op = .or_, .args = &.{first}, .tys = &.{try self.types.boolTy()}, .regions = operands });
    }

    /// `List` of the list type `ty`, over its items.
    pub fn listOf(self: *Builder, ty: TyId, items: []const Ref) Allocator.Error!Ref {
        return self.make(.{ .op = .list, .args = items, .tys = &.{ty} });
    }

    /// A `ForRange` over `start` and `end` and then the initial slots in
    /// `args`, with `body` closed, one output per slot.
    pub fn forRange(self: *Builder, inclusive: bool, args: []const Ref, body: RegionId, outputs: []const TyId) Allocator.Error!Ref {
        return self.make(.{ .op = .for_range, .payload = @intFromBool(inclusive), .args = args, .tys = outputs, .regions = &.{body} });
    }

    /// A loop node of `op` over `args` (bounds or list, then initial slots).
    pub fn loopOf(self: *Builder, op: Op, args: []const Ref, body: RegionId, outputs: []const TyId) Allocator.Error!Ref {
        std.debug.assert(op.isLoop());
        return self.make(.{ .op = op, .args = args, .tys = outputs, .regions = &.{body} });
    }

    /// The input slot of the run-time name the walk numbered `leaf` (N18a).
    pub fn input(self: *Builder, ty: TyId, leaf: u32) Allocator.Error!Ref {
        return Ref.input(try self.store.slot(ty, .{ .leaf = leaf }));
    }

    /// Build a node: apply the first rule that matches, or hash-cons it.
    pub fn make(self: *Builder, spec: NodeSpec) Allocator.Error!Ref {
        // N18b: a projection of a slot is a slot. This is the form of the
        // value, not a rewrite, so it holds with the rules off too.
        if (spec.args.len == 1 and spec.args[0].kind == .input) {
            const of = spec.args[0].slotId();
            const source: ?ir.Slot.Source = switch (spec.op) {
                .field => .{ .field = .{ .of = of, .k = spec.payload } },
                .index => .{ .index = .{ .of = of, .k = spec.payload } },
                .unwrap => .{ .unwrap = of },
                .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .payload, .elem, .opt_field, .prim, .call, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => null,
            };
            if (source) |projected| return Ref.input(try self.store.slot(spec.tys[0], projected));
        }
        if (std.debug.runtime_safety and spec.op == .switch_ and spec.aux.len == 0) {
            // A tag switch has one arm per member of its scrutinee's own type.
            if (self.types.armCount(self.store.refTy(self.row, spec.args[0]))) |count| {
                if (count != spec.payload) @import("base").invariant("reify builder: a switch has {d} arms for a scrutinee of {d} members", .{ spec.payload, count });
            }
        }
        if (self.rulesActive() and spec.op == .switch_) {
            if (spec.aux.len > 0) {
                if (self.laws != null) if (try laws_mod.lenSwitchToEmpty(self, spec)) |r| return r;
                return self.litSwitch(spec);
            }
            if (try self.decidedSwitch(spec)) |r| return r;
        }
        if (self.rulesActive() and (spec.op == .and_ or spec.op == .or_)) {
            if (try self.decidedOperands(spec)) |r| return r;
        }
        if (self.rulesActive() and spec.op == .prim) {
            if (self.laws != null) if (try laws_mod.prim(self, spec)) |r| return r;
            if (try self.decidedNot(spec)) |r| return r;
            if (try self.boundedGet(spec)) |r| return r;
            if (try self.rangeCompare(spec)) |r| return r;
            if (try self.paramOrder(spec)) |r| return r;
        }
        if (self.rulesActive() and spec.op == .elem) {
            if (self.loopElement(spec)) |r| return r;
        }
        if (self.rulesActive() and spec.op == .call) {
            if (try self.forwardedCall(spec)) |r| return r;
            if (try self.specializedCall(spec)) |r| return r;
            if (try self.scalarizedCall(spec)) |r| return r;
        }
        if (self.rulesActive() and spec.op == .apply) {
            if (try self.appliedClosure(spec)) |r| return r;
        }
        return self.makeByTable(spec);
    }

    // N8c over calls: a call of a finalized row that is not recursive and
    // whose body only calls another row over its own parameters is that
    // call, over the arguments those parameters stand for. So a call
    // through the row that gives a closure its calling convention (N8f)
    // meets the direct call, and dropped arguments go with the row.
    fn forwardedCall(self: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
        const n = self.store.forwardingCall(RowId.of(spec.payload)) orelse return null;
        const inner = self.store.node(n);
        const inner_args = self.store.refSlice(inner.args);
        const args = try self.gpa.alloc(Ref, inner_args.len);
        defer self.gpa.free(args);
        for (inner_args, args) |a, *o| o.* = spec.args[a.output];
        self.algorithmStep();
        return try self.callRowAt(RowId.of(inner.payload), args, spec.tys[0]);
    }

    /// `Apply(f, args)` of the type `ty`: a call through the function value `f`.
    pub fn apply(self: *Builder, f: Ref, args: []const Ref, ty: TyId) Allocator.Error!Ref {
        const all = try self.gpa.alloc(Ref, args.len + 1);
        defer self.gpa.free(all);
        all[0] = f;
        @memcpy(all[1..], args);
        return self.make(.{ .op = .apply, .args = all, .tys = &.{ty} });
    }

    /// The row and captures of `ref` where it is a `Closure` node, and null
    /// for any other value. The captures stay valid until the next node is
    /// built.
    pub fn knownClosure(self: *const Builder, ref: Ref) ?struct { row: RowId, captures: []const Ref } {
        const n = self.nodeOf(ref) orelse return null;
        if (n.op != .closure) return null;
        return .{ .row = RowId.of(n.payload), .captures = self.store.refSlice(n.args) };
    }

    // N8i: `Apply(Closure(r, captures), args)` is `Call(r, captures ++ args)`,
    // and `Apply` of a switch output that every arm gives as a known
    // `Closure` is a switch whose every arm applies its own closure. The
    // second runs the call in exactly the cases it ran after the switch: the
    // switch stands in the region the `Apply` is built in, it has no joins,
    // and the arguments are built before it.
    fn appliedClosure(self: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
        const f = spec.args[0];
        const rest = spec.args[1..];
        const n = self.nodeOf(f) orelse return null;
        if (n.op == .closure) {
            const captures = self.store.refSlice(n.args);
            const args = try self.gpa.alloc(Ref, captures.len + rest.len);
            defer self.gpa.free(args);
            @memcpy(args[0..captures.len], captures);
            @memcpy(args[captures.len..], rest);
            self.algorithmStep();
            return try self.callRowAt(RowId.of(n.payload), args, spec.tys[0]);
        }
        if (n.op != .switch_ or n.tys.len == 0 or n.regions.len != n.payload) return null;
        if (n.region != self.current()) return null;
        for (rest) |a| if (a.kind == .node and a.target >= f.target) return null;
        const arms = try self.gpa.dupe(RegionId, self.store.regionSlice(n.regions));
        defer self.gpa.free(arms);
        for (arms) |arm| {
            const end = self.store.region(arm).end;
            if (end.kind != .value) return null;
            const v = self.nodeOf(self.store.refSlice(end.refs)[f.output]) orelse return null;
            if (v.op != .closure) return null;
        }
        const scrutinee = self.store.refSlice(n.args)[0];
        const keys = try self.gpa.dupe(u32, self.store.wordSlice(n.aux));
        defer self.gpa.free(keys);
        const new_arms = try self.gpa.alloc(RegionId, arms.len);
        defer self.gpa.free(new_arms);
        for (arms, new_arms, 0..) |arm, *new, i| {
            new.* = try self.openArmAt(scrutinee, keys, @intCast(i));
            const clo = try self.available(self.store.refSlice(self.store.region(arm).end.refs)[f.output]);
            const v = try self.apply(clo, rest, spec.tys[0]);
            try self.close(.{ .value = &.{v} });
        }
        self.algorithmStep();
        return try self.switchOn(scrutinee, new_arms, &.{}, spec.tys, keys);
    }

    // N8i with N8d: a call that passes a known closure for a function
    // parameter of a finalized row calls the row specialized to that
    // closure, keyed by the rows' digests, over the closure's captures in
    // the parameter's place.
    fn specializedCall(self: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
        const specializer = self.specializer orelse return null;
        const row = RowId.of(spec.payload);
        if (self.store.row(row).digest == null) return null;
        const at = for (spec.args, 0..) |a, i| {
            const n = self.nodeOf(a) orelse continue;
            if (n.op == .closure) break i;
        } else return null;
        const clo = self.nodeOf(spec.args[at]).?;
        const captures = try self.gpa.dupe(Ref, self.store.refSlice(clo.args));
        defer self.gpa.free(captures);
        const capture_tys = try self.gpa.alloc(TyId, captures.len);
        defer self.gpa.free(capture_tys);
        for (captures, capture_tys) |c, *t| t.* = self.store.refTy(self.row, c);
        const found = specializer.run(specializer.ctx, self, row, @intCast(at), RowId.of(clo.payload), capture_tys) catch |err| switch (err) {
            error.OutOfMemory => |e| return e,
            // The driver keeps the reason and stops after the caller's round.
            error.MeasureDidNotFall, error.RoundBoundExceeded, error.InvariantBroken => return null,
        };
        const target = found orelse return null;
        const built = try self.gpa.alloc(Ref, spec.args.len - 1 + captures.len);
        defer self.gpa.free(built);
        @memcpy(built[0..at], spec.args[0..at]);
        @memcpy(built[at..][0..captures.len], captures);
        @memcpy(built[at + captures.len ..], spec.args[at + 1 ..]);
        // The row was built over these arguments in this order, and its
        // finalize may have renumbered its parameters since.
        const order = target.order orelse {
            self.algorithmStep();
            return try self.callRowAt(target.row, built, spec.tys[0]);
        };
        const args = try self.gpa.alloc(Ref, order.len);
        defer self.gpa.free(args);
        for (order, args) |k, *a| a.* = built[k];
        self.algorithmStep();
        return try self.callRowAt(target.row, args, spec.tys[0]);
    }

    // N14a: a call of a finalized row, with an aggregate parameter that the
    // row only reads by field or index, is a call of the row with that
    // parameter split, over the components of the argument. A component of a
    // construction is the value the construction was given, so the call that
    // passes `{ a, b }` passes `a` and `b`. The row was built over the leaves
    // in order, and its finalize may have renumbered its parameters since.
    fn scalarizedCall(self: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
        const scalarizer = self.scalarizer orelse return null;
        if (!self.algorithmOn(.scalar_call)) return null;
        const row = RowId.of(spec.payload);
        const found = scalarizer.run(scalarizer.ctx, self, row) catch |err| switch (err) {
            error.OutOfMemory => |e| return e,
            // The driver keeps the reason and stops after the caller's round.
            error.MeasureDidNotFall, error.RoundBoundExceeded, error.InvariantBroken => return null,
        };
        const target = found orelse return null;
        var scratch = std.heap.ArenaAllocator.init(self.gpa);
        defer scratch.deinit();
        const leaves = try scalar.leavesOf(scratch.allocator(), target.shapes);
        const count = if (target.order) |order| order.len else leaves.len;
        const args = try self.gpa.alloc(Ref, count);
        defer self.gpa.free(args);
        for (args, 0..) |*a, k| {
            const leaf = leaves[if (target.order) |order| order[k] else k];
            var ref = spec.args[leaf.index];
            for (leaf.path) |component| {
                const ty = self.store.refTy(self.row, ref);
                ref = switch (self.types.get(ty)) {
                    .record => try self.field(ref, component),
                    .tuple => try self.index(ref, component),
                    .bool_, .str, .int, .float, .dec, .tag_union, .list, .nominal, .func, .opaque_, .recursive => unreachable, // a shape splits records and tuples only
                };
            }
            a.* = ref;
        }
        self.algorithmFired(.scalar_call);
        return try self.callRowAt(target.row, args, spec.tys[0]);
    }

    // N13d over `And` and `Or` operands (normal-form 3.13): an operand that
    // an earlier operand, or a dominating arm, already decided to the value
    // that lets the connective go on, `True` for `And` and `False` for `Or`,
    // is removed. With no operand left the connective is that value.
    fn decidedOperands(self: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
        const goes_on: u32 = @intFromBool(spec.op == .and_);
        const first = spec.args[0];
        const first_decided = self.knownKey(first) == goes_on;
        var kept: std.ArrayList(RegionId) = .empty;
        defer kept.deinit(self.gpa);
        var earlier: std.ArrayList(Ref) = .empty;
        defer earlier.deinit(self.gpa);
        try earlier.append(self.gpa, first);
        for (spec.regions) |r| {
            const v = self.armValue(r) orelse {
                try kept.append(self.gpa, r);
                continue;
            };
            if (std.mem.findScalar(Ref, earlier.items, v) != null or self.knownKey(v) == goes_on) continue;
            try kept.append(self.gpa, r);
            try earlier.append(self.gpa, v);
        }
        if (!first_decided) {
            if (kept.items.len == spec.regions.len) return null;
            self.algorithmStep();
            return try self.make(.{ .op = spec.op, .args = &.{first}, .tys = spec.tys, .regions = kept.items });
        }
        if (kept.items.len == 0) {
            self.algorithmStep();
            return try self.litBool(goes_on == 1);
        }
        // The next operand is first, built where the connective is.
        const next_value = self.armValue(kept.items[0]) orelse return null;
        self.algorithmStep();
        const next = try self.available(next_value);
        return try self.make(.{ .op = spec.op, .args = &.{next}, .tys = spec.tys, .regions = kept.items[1..] });
    }

    // N13m (normal-form 3.13): `List.get(xs, i)` where a dominating test
    // proved `i < List.len(xs)`, or inside the body of a `ForList` over `xs`
    // whose index is `i`, is `Ok` of the element: `Elem(xs, i)`, or the
    // body's element parameter. The result has the call's type, which is the
    // `Try` nominal when the call is read at it.
    fn boundedGet(self: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
        const p = prims.lookup(ir.PrimId.of(spec.payload)) orelse return null;
        if (p.owner != .list or p.method != .get or !self.algorithmOn(.bounded_get)) return null;
        const xs = spec.args[0];
        const i = spec.args[1];
        const ty = spec.tys[0];
        const backing = switch (self.types.get(ty)) {
            .nominal => try self.types.unfold(ty),
            .tag_union => ty,
            .bool_, .str, .int, .float, .dec, .record, .tuple, .list, .func, .opaque_, .recursive => @import("base").invariant("reify builder: List.get does not give a Try", .{}),
        };
        const ok = self.types.findName("Ok") orelse @import("base").invariant("reify builder: List.get gives a type without Ok", .{});
        const at = self.types.memberIndex(backing, ok) orelse @import("base").invariant("reify builder: List.get gives a type without Ok", .{});
        const element_ty = self.types.tySlice(self.types.memberSlice(self.types.get(backing).tag_union)[at].tys)[0];
        const element = for (self.facts.items) |f| {
            const loop = f.loop orelse continue;
            if (loop.list == xs and f.ref == i) break loop.element;
        } else blk: {
            if (!self.provedInBounds(xs, i)) return null;
            break :blk try self.elem(xs, i, element_ty);
        };
        self.algorithmFired(.bounded_get);
        const tagged = try self.tag(backing, ok, &.{element});
        return if (backing == ty) tagged else try self.wrap(ty, tagged);
    }

    // N13m over `Item`: the item of the list a `ForList` body is over, at
    // that body's own index, is the body's element parameter, whichever
    // spelling of the loop gave the read.
    fn loopElement(self: *Builder, spec: NodeSpec) ?Ref {
        if (!self.algorithmOn(.bounded_get)) return null;
        for (self.facts.items) |f| {
            const loop = f.loop orelse continue;
            if (loop.list == spec.args[0] and f.ref == spec.args[1]) {
                self.algorithmFired(.bounded_get);
                return loop.element;
            }
        }
        return null;
    }

    // Whether a dominating test proved `i < List.len(xs)`.
    fn provedInBounds(self: *const Builder, xs: Ref, i: Ref) bool {
        for (self.facts.items) |f| {
            if (!f.isTest()) continue;
            if (self.impliesInBounds(f.ref, f.key, xs, i)) return true;
        }
        return false;
    }

    // Whether `ref` having arm `key` (1 for `True`) implies `i < List.len(xs)`.
    fn impliesInBounds(self: *const Builder, ref: Ref, key: u32, xs: Ref, i: Ref) bool {
        const n = self.nodeOf(ref) orelse return false;
        switch (n.op) {
            .prim => {
                const p = prims.lookup(ir.PrimId.of(n.payload)) orelse return false;
                const args = self.store.refSlice(n.args);
                if (p.owner == .bool_ and p.method == .not) return self.impliesInBounds(args[0], 1 - key, xs, i);
                if (p.owner != .u64) return false;
                // `i < len` is true, or `len <= i` is false.
                if (key == 1 and p.method == .is_lt) return args[0] == i and self.isLen(args[1], xs);
                if (key == 0 and p.method == .is_lte) return args[1] == i and self.isLen(args[0], xs);
                return false;
            },
            // Every operand of a true `And`, and of a false `Or`, has that value.
            .and_, .or_ => {
                if (key != @intFromBool(n.op == .and_)) return false;
                if (self.impliesInBounds(self.store.refSlice(n.args)[0], key, xs, i)) return true;
                for (self.store.regionSlice(n.regions)) |r| {
                    const v = self.armValue(r) orelse continue;
                    if (self.impliesInBounds(v, key, xs, i)) return true;
                }
                return false;
            },
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .call, .switch_, .for_range, .for_list, .loop, .lambda, .apply => return false,
        }
    }

    // Whether `ref` is `List.len(xs)`.
    fn isLen(self: *const Builder, ref: Ref, xs: Ref) bool {
        const n = self.nodeOf(ref) orelse return false;
        if (n.op != .prim) return false;
        const p = prims.lookup(ir.PrimId.of(n.payload)) orelse return false;
        return p.owner == .list and p.method == .len and self.store.refSlice(n.args)[0] == xs;
    }

    // N13u (normal-form 3.13): the interval of a value of a builtin integer
    // type where it is read. A literal is its value; a node N13u gave an
    // interval when it was built has it (`nodeRange`); anything else has its
    // type's full range. Each fact on the stack that bounds the value narrows
    // it: a dominating arm of a comparison with a literal, an arm of a
    // literal switch on it, and the index of the `ForRange` body it is.
    // `holds_in` is the innermost region whose fact the interval read, or
    // `none` where it read none.
    pub fn rangeOf(self: *const Builder, ref: Ref) ?Ranged {
        const int = self.intOf(ref) orelse return null;
        var out: Ranged = .{ .interval = ranges.full(int), .holds_in = RegionId.none };
        if (ref.kind == .node) {
            if (self.intLit(ref)) |v| return .{ .interval = ranges.point(v), .holds_in = RegionId.none };
            if (self.store.ranges.get(ref.nodeId())) |r| {
                // A node is read only where it is in scope, which its facts
                // enclose (`appendNode`), so its interval holds here.
                std.debug.assert(r.holds_in == RegionId.none or self.store.encloses(r.holds_in, self.current()));
                out = .{ .interval = r.interval, .holds_in = r.holds_in };
            }
        }
        for (self.facts.items) |f| {
            const iv = self.factInterval(f, ref, int) orelse continue;
            out.interval = ranges.meet(out.interval, iv);
            out.holds_in = self.deeper(out.holds_in, f.region);
        }
        return out;
    }

    /// An interval and the region it holds in (`rangeOf`).
    pub const Ranged = struct { interval: ir.Interval, holds_in: RegionId };

    // The builtin integer type of `ref`, if it has one.
    fn intOf(self: *const Builder, ref: Ref) ?types_mod.IntTy {
        return switch (self.types.get(self.store.refTy(self.row, ref))) {
            .int => |i| i,
            .bool_, .str, .float, .dec, .record, .tuple, .list, .tag_union, .nominal, .func, .opaque_, .recursive => null,
        };
    }

    // The value of `ref` when it is an integer literal.
    fn intLit(self: *const Builder, ref: Ref) ?i256 {
        const n = self.nodeOf(ref) orelse return null;
        if (n.op != .lit) return null;
        return litIntValue(self.types, self.store.lit(LitId.of(n.payload)));
    }

    // The interval fact `f` gives `ref`, of type `int`, if it bounds it.
    fn factInterval(self: *const Builder, f: Fact, ref: Ref, int: types_mod.IntTy) ?ir.Interval {
        if (f.index) |iv| return if (f.ref == ref) iv else null;
        if (f.loop != null) return null;
        if (f.ref == ref) {
            const l = f.lit orelse return null;
            return ranges.point(litIntValue(self.types, self.store.lit(l)) orelse return null);
        }
        if (f.key > 1) return null;
        return self.testInterval(f.ref, f.key == 1, ref, int);
    }

    // The interval `x`, of type `int`, has where the `Bool` `t` is `holds`:
    // `t` compares `x` with a literal, or is a true `And` or a false `Or`
    // one of whose operands does, as N13m reads a bound through them.
    fn testInterval(self: *const Builder, t: Ref, holds: bool, x: Ref, int: types_mod.IntTy) ?ir.Interval {
        const n = self.nodeOf(t) orelse return null;
        switch (n.op) {
            .prim => {
                const p = prims.lookup(ir.PrimId.of(n.payload)) orelse return null;
                if (p.owner.int() != int) return null;
                switch (p.method) {
                    .is_lt, .is_lte, .is_eq => {},
                    else => return null,
                }
                const args = self.store.refSlice(n.args);
                if (self.sameValue(args[0], x)) return ranges.ofTest(int, p.method, true, self.intLit(args[1]) orelse return null, holds);
                if (self.sameValue(args[1], x)) return ranges.ofTest(int, p.method, false, self.intLit(args[0]) orelse return null, holds);
                return null;
            },
            .and_, .or_ => {
                if (holds != (n.op == .and_)) return null;
                var out: ?ir.Interval = self.testInterval(self.store.refSlice(n.args)[0], holds, x, int);
                for (self.store.regionSlice(n.regions)) |r| {
                    const v = self.armValue(r) orelse continue;
                    const iv = self.testInterval(v, holds, x, int) orelse continue;
                    out = if (out) |o| ranges.meet(o, iv) else iv;
                }
                return out;
            },
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .call, .switch_, .for_range, .for_list, .loop, .lambda, .apply => return null,
        }
    }

    // Whether `a` and `b` give one value wherever both are evaluated: one
    // ref, or two nodes of one regionless projection or builtin op, with the
    // same payload, types and immediates, over operands that give one value.
    // A test in an `And` operand compares the copy of a value built in that
    // operand's region, not the copy the arm builds.
    fn sameValue(self: *const Builder, a: Ref, b: Ref) bool {
        if (a == b) return true;
        const x = self.nodeOf(a) orelse return false;
        const y = self.nodeOf(b) orelse return false;
        if (x.op != y.op or x.payload != y.payload) return false;
        switch (x.op) {
            .lit, .prim, .field, .index, .payload, .opt_field, .unwrap => {},
            .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .elem, .call, .switch_, .for_range, .for_list, .loop, .lambda, .apply, .and_, .or_ => return false,
        }
        if (x.regions.len != 0 or y.regions.len != 0) return false;
        if (!std.mem.eql(TyId, self.store.tySlice(x.tys), self.store.tySlice(y.tys))) return false;
        if (!std.mem.eql(u32, self.store.wordSlice(x.aux), self.store.wordSlice(y.aux))) return false;
        if (x.op == .lit) return std.meta.eql(self.store.lit(LitId.of(x.payload)), self.store.lit(LitId.of(y.payload)));
        const xs = self.store.refSlice(x.args);
        const ys = self.store.refSlice(y.args);
        if (xs.len != ys.len) return false;
        for (xs, ys) |p, q| if (!self.sameValue(p, q)) return false;
        return true;
    }

    // Of two regions on the chain of open regions, the inner one; `none`
    // stands for no region.
    fn deeper(self: *const Builder, a: RegionId, b: RegionId) RegionId {
        if (a == RegionId.none) return b;
        if (b == RegionId.none) return a;
        return if (self.store.region(b).depth > self.store.region(a).depth) b else a;
    }

    // N13u's interval of a node of a builtin integer type being built, where
    // it narrows the type or proves a checked op fits: interval arithmetic
    // over its operands' intervals for `plus`, `minus`, `times` and the
    // `_wrap` forms, and the result range of a finalized row for a `Call`
    // (N8k). Null for anything else.
    fn nodeRange(self: *Builder, spec: NodeSpec) Allocator.Error!?ir.NodeRange {
        if (spec.tys.len != 1) return null;
        const int = switch (self.types.get(spec.tys[0])) {
            .int => |i| i,
            .bool_, .str, .float, .dec, .record, .tuple, .list, .tag_union, .nominal, .func, .opaque_, .recursive => return null,
        };
        switch (spec.op) {
            .prim => {
                const p = prims.lookup(ir.PrimId.of(spec.payload)) orelse return null;
                if (p.owner.int() != int) return null;
                switch (p.method) {
                    .plus, .minus, .times, .plus_wrap, .times_wrap => {},
                    else => return null,
                }
                const ivs = try self.gpa.alloc(ir.Interval, spec.args.len);
                defer self.gpa.free(ivs);
                var holds_in = RegionId.none;
                for (spec.args, ivs) |a, *iv| {
                    const r = self.rangeOf(a) orelse return null;
                    iv.* = r.interval;
                    holds_in = self.deeper(holds_in, r.holds_in);
                }
                const interval = ranges.of(int, p.method, ivs).?;
                const fits = ranges.fits(int, p.method, ivs) and self.algorithmOn(.range_fit);
                if (fits) self.algorithmFired(.range_fit);
                if (!fits and !ranges.narrows(interval, int)) return null;
                return .{ .interval = interval, .holds_in = holds_in, .fits = fits };
            },
            .call => {
                const row = self.store.row(RowId.of(spec.payload));
                if (row.digest == null) return null;
                const r = row.result_range orelse return null;
                if (!ranges.narrows(r, int)) return null;
                return .{ .interval = r, .holds_in = RegionId.none, .fits = false };
            },
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => return null,
        }
    }

    // N13u (normal-form 3.13): a comparison of a value with a literal that
    // the value's interval decides is that answer, as N13d decides a test a
    // dominating arm made. So inside `if x < 10`, `x < 20` is `True`, and in
    // the body of `for i in 0..10`, `i < 10` is.
    fn rangeCompare(self: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
        if (spec.args.len != 2 or !self.algorithmOn(.range_compare)) return null;
        const p = prims.lookup(ir.PrimId.of(spec.payload)) orelse return null;
        if (p.owner.int() == null) return null;
        switch (p.method) {
            .is_lt, .is_lte, .is_eq => {},
            else => return null,
        }
        const k0 = self.intLit(spec.args[0]);
        const k1 = self.intLit(spec.args[1]);
        if ((k0 == null) == (k1 == null)) return null;
        const x_first = k1 != null;
        const x = self.rangeOf(spec.args[if (x_first) 0 else 1]) orelse return null;
        const answer = ranges.decide(p.method, x_first, x.interval, (k1 orelse k0).?) orelse return null;
        self.algorithmFired(.range_compare);
        return try self.litBool(answer);
    }

    // N15c, the parameter half (normal-form 3.15): two parameters of the
    // root row as the operands of integer `plus` or `times`, or of `is_eq`
    // over a builtin integer type or `Str`, go in parameter order. The
    // root's parameters are its type in `Code(f)`, so no unrelated edit moves
    // them. Another row's parameters are numbered in first-read order (N8f),
    // which an order by position would change, so they stay as written.
    fn paramOrder(self: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
        if (spec.args.len != 2 or !self.algorithmOn(.param_order)) return null;
        const p = prims.lookup(ir.PrimId.of(spec.payload)) orelse return null;
        if (!prims.ordersLiteralLast(p.owner, p.method)) return null;
        const a = spec.args[0];
        const b = spec.args[1];
        if (a.kind != .row_param or b.kind != .row_param or a.output <= b.output) return null;
        if (!self.store.row(self.row).fixed_params) return null;
        self.algorithmFired(.param_order);
        return try self.make(.{ .op = .prim, .payload = spec.payload, .args = &.{ b, a }, .tys = spec.tys });
    }

    // N15a over a checked `plus` (normal-form 3.15, N13u): a `plus` whose
    // operands include `plus` nodes of its type is one `Prim` over all of
    // their operands, in order, when the sum of the operands' negative lower
    // bounds and the sum of their positive upper bounds both fit the type.
    // Then every partial sum of every grouping fits, so `(a + b) + c` and
    // `a + (b + c)` fail nowhere and meet. Where the intervals do not prove
    // it, the grouping as written stays, because a regrouped sum can
    // overflow where the written one does not.
    fn rangeChain(self: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
        if (!self.algorithmOn(.range_chain)) return null;
        const p = prims.lookup(ir.PrimId.of(spec.payload)) orelse return null;
        const int = p.owner.int() orelse return null;
        if (p.method != .plus) return null;
        var flat: std.ArrayList(Ref) = .empty;
        defer flat.deinit(self.gpa);
        var spliced = false;
        for (spec.args) |a| {
            if (self.nodeOf(a)) |n| if (n.op == .prim and n.payload == spec.payload and a.output == 0) {
                try flat.appendSlice(self.gpa, self.store.refSlice(n.args));
                spliced = true;
                continue;
            };
            try flat.append(self.gpa, a);
        }
        if (!spliced) return null;
        const ivs = try self.gpa.alloc(ir.Interval, flat.items.len);
        defer self.gpa.free(ivs);
        for (flat.items, ivs) |x, *iv| iv.* = (self.rangeOf(x) orelse return null).interval;
        if (!ranges.chainFits(int, ivs)) return null;
        self.algorithmFired(.range_chain);
        return try self.make(.{ .op = .prim, .payload = spec.payload, .args = flat.items, .tys = spec.tys });
    }

    // N13d over `Bool.not` (normal-form 3.13): the negation of a value that a
    // dominating arm, or an earlier operand of an enclosing `And` or `Or`,
    // decided is the opposite literal. So `if c !c else b` is
    // `Switch(c) { False: b, True: False }`, which N13o turns into
    // `And(Bool.not(c), b)`.
    fn decidedNot(self: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
        const p = prims.lookup(ir.PrimId.of(spec.payload)) orelse return null;
        if (p.owner != .bool_ or p.method != .not or !self.algorithmOn(.decided_not)) return null;
        const key = self.knownKey(spec.args[0]) orelse return null;
        self.algorithmFired(.decided_not);
        return try self.litBool(key == 0);
    }

    // N13d over a `Bool` or tag switch (normal-form 3.13): a scrutinee that a
    // dominating arm, or an earlier operand of an enclosing `And` or `Or`,
    // tested selects its arm, when the switch has one output and that arm
    // ends in a value.
    fn decidedSwitch(self: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
        const key = self.knownKey(spec.args[0]) orelse return null;
        const arm = self.armOfKey(spec.args[0], key) orelse return null;
        if (arm >= spec.payload) return null;
        const r = try self.armResult(spec, spec.regions[arm]) orelse return null;
        self.algorithmStep();
        return r;
    }

    fn makeByTable(self: *Builder, spec: NodeSpec) Allocator.Error!Ref {
        if (self.rulesActive()) {
            for (table.rules, 0..) |rule, i| {
                if (rule.root != spec.op) continue;
                if (hooks_enabled and self.hooks.knocked_out[i]) continue;
                var b: Bindings = .{ .conds = rule.conds, .root = spec };
                if (!try self.matchRoot(rule, spec, &b)) continue;
                if (!try self.condsHold(rule, &b)) continue;
                if (hooks_enabled) self.hooks.fired[i] += 1;
                return self.instantiate(rule.result, &b, spec.tys);
            }
            // After the rows, so N15c puts a literal last in a two-operand
            // `plus` before the chain flattens: `1 + (a + b)` is `a + b + 1`.
            if (spec.op == .prim) {
                if (try self.rangeChain(spec)) |r| return r;
            }
            if (spec.op == .switch_) {
                if (try self.rejectedArm(spec)) |r| return r;
                if (try self.caseOfCase(spec)) |r| return r;
                if (try self.interchange(spec)) |r| return r;
            }
        }
        return self.cons_(spec);
    }

    // N7b (normal-form 3.7, rule 2): a switch one of whose arms ends in a
    // switch on a position that comes before its own, in the canonical order
    // of match.zig, is rebuilt with that position first. For each constructor
    // of the earlier position, the switch on its own position has the arms
    // the earlier test left: an arm that ended in the earlier test is its arm
    // for the constructor, and an arm that did not test it is copied under
    // the constructor's fact. So two matches with the same mapping from
    // inputs to arms reach one tree, whichever position their patterns test
    // first. What the rule leaves alone, each by a stated limit:
    //
    // | Left alone | Why |
    // |---|---|
    // | two `Bool` switches | N7d and N13o own their order: nested `if`s meet `and`, in the operand order the nesting gave |
    // | a position of another root, unless both are parameters of the root row | two parameters of the root are in parameter order, N15c's parameter half (`match.rootedBefore`); other roots have no order |
    // | a test that is not a position | a guard keeps its place: the first guard that holds wins |
    // | a switch with several outputs, or joins | N13c and N13d decide only single-output switches |
    fn interchange(self: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
        if (!self.algorithmOn(.interchange)) return null;
        if (spec.tys.len != 1 or spec.regions.len != spec.payload) return null;
        for (spec.regions) |r| if (self.armValue(r) == null or !match.copyable(self.store, null, r)) return null;
        const p = spec.args[0];
        var p_steps: std.ArrayList(match.Step) = .empty;
        defer p_steps.deinit(self.gpa);
        const p_root = try match.positionOf(self.gpa, self.store, p, &p_steps);
        const p_is_bool = self.types.get(self.store.refTy(self.row, p)) == .bool_;

        // The earliest position an arm ends in a test of, and which arms do.
        const inner_of = try self.gpa.alloc(?NodeId, spec.regions.len);
        defer self.gpa.free(inner_of);
        var best: ?Ref = null;
        var best_root: Ref = undefined;
        var best_steps: std.ArrayList(match.Step) = .empty;
        defer best_steps.deinit(self.gpa);
        var steps: std.ArrayList(match.Step) = .empty;
        defer steps.deinit(self.gpa);
        for (spec.regions, inner_of) |arm, *slot| {
            slot.* = self.topSwitch(arm);
            const inner = slot.* orelse continue;
            const q = self.store.refSlice(self.store.node(inner).args)[0];
            steps.clearRetainingCapacity();
            const root = try match.positionOf(self.gpa, self.store, q, &steps);
            const q_is_bool = self.types.get(self.store.refTy(self.row, q)) == .bool_;
            if (!match.rootedBefore(self.store, self.types, self.row, root, steps.items, p_root, p_steps.items) or (p_is_bool and q_is_bool) or !self.readable(q)) {
                slot.* = null;
                continue;
            }
            if (best == null or match.rootedBefore(self.store, self.types, self.row, root, steps.items, best_root, best_steps.items)) {
                best = q;
                best_root = root;
                best_steps.clearRetainingCapacity();
                try best_steps.appendSlice(self.gpa, steps.items);
            }
        }
        const first = best orelse return null;
        // Only the arms that end in a test of that position take part; one that ends in a test of another position is copied whole.
        for (spec.regions, inner_of) |_, *slot| {
            const inner = slot.* orelse continue;
            steps.clearRetainingCapacity();
            const root = try match.positionOf(self.gpa, self.store, self.store.refSlice(self.store.node(inner).args)[0], &steps);
            if (root != best_root or !match.samePosition(self.types, steps.items, best_steps.items)) slot.* = null;
        }

        // The constructors of the position: the arms of a tag or `Bool`
        // switch, or the keys that any of the tests names, and a default.
        const q = try self.available(first);
        const q_ty = self.store.refTy(self.row, q);
        const by_arm = self.types.armCount(q_ty) != null;
        var keys: std.ArrayList(u32) = .empty;
        defer keys.deinit(self.gpa);
        const count: u32 = if (self.types.armCount(q_ty)) |n| n else blk: {
            for (inner_of) |slot| {
                const inner = slot orelse continue;
                for (self.store.wordSlice(self.store.node(inner).aux)) |k| {
                    if (std.mem.findScalar(u32, keys.items, k) == null) try keys.append(self.gpa, k);
                }
            }
            std.mem.sort(u32, keys.items, self, struct {
                fn lt(b: *const Builder, x: u32, y: u32) bool {
                    return match.keyLess(b.store, b.types, x, y);
                }
            }.lt);
            break :blk @intCast(keys.items.len + 1);
        };

        const arms = try self.gpa.dupe(RegionId, spec.regions);
        defer self.gpa.free(arms);
        const p_keys = try self.gpa.dupe(u32, spec.aux);
        defer self.gpa.free(p_keys);
        const out_ty = try self.gpa.dupe(TyId, spec.tys);
        defer self.gpa.free(out_ty);
        // The inner tests, copied out of the store, which building grows.
        const InnerTest = struct { keys: []u32, arms: []RegionId };
        const inners = try self.gpa.alloc(?InnerTest, arms.len);
        defer {
            for (inners) |t| if (t) |x| {
                self.gpa.free(x.keys);
                self.gpa.free(x.arms);
            };
            self.gpa.free(inners);
        }
        for (inners, inner_of) |*t, slot| {
            const inner = slot orelse {
                t.* = null;
                continue;
            };
            const n = self.store.node(inner);
            t.* = .{ .keys = try self.gpa.dupe(u32, self.store.wordSlice(n.aux)), .arms = try self.gpa.dupe(RegionId, self.store.regionSlice(n.regions)) };
        }

        const q_arms = try self.gpa.alloc(RegionId, count);
        defer self.gpa.free(q_arms);
        const new_arms = try self.gpa.alloc(RegionId, arms.len);
        defer self.gpa.free(new_arms);
        for (q_arms, 0..) |*q_arm, c| {
            q_arm.* = try self.openArmAt(q, keys.items, @intCast(c));
            for (new_arms, arms, inners, 0..) |*na, old, inner, i| {
                na.* = try self.openArmAt(p, p_keys, @intCast(i));
                if (inner) |t| {
                    // The inner arm for this constructor: the arm of its index, or for a key the test does not name, its default.
                    const at = if (by_arm)
                        c
                    else if (c < keys.items.len)
                        std.mem.findScalar(u32, t.keys, keys.items[c]) orelse t.keys.len
                    else
                        t.keys.len;
                    try self.fillFrom(t.arms[at]);
                } else try self.fillFrom(old);
            }
            const inner_switch = try self.switchOn(p, new_arms, &.{}, out_ty, p_keys);
            try self.close(.{ .value = &.{inner_switch} });
        }
        self.algorithmFired(.interchange);
        return try self.switchOn(q, q_arms, &.{}, out_ty, keys.items);
    }

    // N13r, case-of-case (normal-form 3.13): a switch on the output of a
    // value switch `s` that stands in this region, where every arm of `s` ends
    // in a known `Tag` or `Lit`, is `s` with each arm continuing into the
    // outer arm its value selects. The outer arm is built in the arm of `s`,
    // with the output standing for the value the arm gave, so N13a and N13c
    // read its payloads and its own tests off it. Every test runs in the order
    // it ran, and an outer arm runs in the cases it ran. An outer arm that
    // two arms of `s` select would be copied, and the normal form shares such
    // an arm in a join of `s`; an exiting switch carries one join, the code
    // after it, so the rule does not apply there (plan 3.3, N13r).
    fn caseOfCase(self: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
        const outer_t = spec.args[0];
        if (self.sole_reader != outer_t or !self.algorithmOn(.case_of_case)) return null;
        // The output may be read through the `Unwrap`s of a nominal, which the
        // arms built with `Wrap`s.
        var t = outer_t;
        var depth: u32 = 0;
        while (self.nodeOf(t)) |n| {
            if (n.op != .unwrap) break;
            t = self.store.refSlice(n.args)[0];
            depth += 1;
        }
        if (t.kind != .node or t.output != 0) return null;
        const inner = self.store.node(t.nodeId());
        if (inner.op != .switch_ or inner.region != self.current() or inner.tys.len != 1) return null;
        const inner_arms = self.store.regionSlice(inner.regions);
        if (inner_arms.len != inner.payload) return null;
        const joins_given = spec.regions[spec.payload..];
        if (spec.tys.len > 0 and joins_given.len != 0) return null;
        if (spec.tys.len == 0 and joins_given.len > 1) return null;
        for (spec.regions[0..spec.payload]) |r| {
            if (spec.tys.len > 0 and self.armValue(r) == null) return null;
        }

        // The outer arm each inner arm selects, once each.
        const known = try self.gpa.alloc(Ref, inner_arms.len);
        defer self.gpa.free(known);
        const selected = try self.gpa.alloc(u32, inner_arms.len);
        defer self.gpa.free(selected);
        const t_ty = self.store.refTy(self.row, outer_t);
        for (inner_arms, known, selected) |arm, *v, *sel| {
            v.* = self.armValue(arm) orelse return null;
            for (0..depth) |_| {
                const w = self.nodeOf(v.*) orelse return null;
                if (w.op != .wrap) return null;
                v.* = self.store.refSlice(w.args)[0];
            }
            const n = self.nodeOf(v.*) orelse return null;
            sel.* = switch (n.op) {
                .tag => self.types.memberIndex(t_ty, NameId.of(n.payload)) orelse return null,
                .lit => blk: {
                    const lit = self.store.lit(LitId.of(n.payload));
                    switch (lit.value) {
                        .bool_ => |b| break :blk @intFromBool(b),
                        .int, .str => {
                            const at = std.mem.findScalar(u32, spec.aux, n.payload) orelse break :blk @intCast(spec.aux.len);
                            break :blk @intCast(at);
                        },
                        .float, .dec, .bytes => return null,
                    }
                },
                .crash, .derived, .record, .tuple, .list, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => return null,
            };
        }
        for (selected, 0..) |a, i| {
            if (std.mem.findScalar(u32, selected[0..i], a) != null) return null;
        }

        // `s` rebuilt with the outer arms in its arms.
        const outer = try self.gpa.dupe(RegionId, spec.regions[0..spec.payload]);
        defer self.gpa.free(outer);
        const joins = try self.gpa.dupe(RegionId, joins_given);
        defer self.gpa.free(joins);
        const keys = try self.gpa.dupe(u32, self.store.wordSlice(inner.aux));
        defer self.gpa.free(keys);
        const out_tys = try self.gpa.dupe(TyId, spec.tys);
        defer self.gpa.free(out_tys);
        const scrutinee = self.store.refSlice(inner.args)[0];
        const new_arms = try self.gpa.alloc(RegionId, inner_arms.len);
        defer self.gpa.free(new_arms);
        for (new_arms, known, selected, 0..) |*arm, v, sel, i| {
            arm.* = try self.openArmAt(scrutinee, keys, @intCast(i));
            const value = try self.available(v);
            const saved = self.case_subst;
            self.case_subst = .{ .from = outer_t, .to = value };
            defer self.case_subst = saved;
            try self.fillFrom(outer[sel]);
        }
        self.algorithmFired(.case_of_case);
        if (spec.tys.len == 0) return Ref.of(try self.exitingSwitch(scrutinee, new_arms, joins, keys));
        return try self.switchOn(scrutinee, new_arms, &.{}, out_tys, keys);
    }

    // N13w, a rejected literal's arm (normal-form 3.13): a switch `o` on the
    // output of a value switch `s` that stands in this region, one of whose
    // arms ends in the crash of a rejected literal. Follow each arm of `s`,
    // and of each value switch such an arm ends in, to the value it gives
    // for the output. When every such value but one is a known `Tag` or
    // `Lit` that selects an arm of `o` ending in a rejected literal's crash,
    // and the work the one other value needs from inside `s` is
    // speculatable, `o` switches on that value, and `s` and its tests go.
    // C2 allows it: a path to a rejected literal crashes, so only the one
    // other path computes a result, and the work moved out of `s` cannot
    // fail. Unlike N13r, several values may select one rejected arm,
    // because `o` keeps its own arms and nothing is copied into `s`. `o` is
    // the only reader of the output, as for N13r, so nothing is computed
    // twice.
    fn rejectedArm(self: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
        const outer_t = spec.args[0];
        if (self.sole_reader != outer_t or !self.algorithmOn(.rejected_arm)) return null;
        if (spec.tys.len == 0 or spec.regions.len != spec.payload) return null;
        const found = try match.rejectedKept(self.gpa, self.store, self.types, self.row, self.current(), outer_t, spec.regions, spec.aux) orelse return null;

        // `o` rebuilt over the kept value, its arms reading it for the output.
        const outer = try self.gpa.dupe(RegionId, spec.regions);
        defer self.gpa.free(outer);
        const keys = try self.gpa.dupe(u32, spec.aux);
        defer self.gpa.free(keys);
        const out_tys = try self.gpa.dupe(TyId, spec.tys);
        defer self.gpa.free(out_tys);
        const t_ty = self.store.refTy(self.row, outer_t);
        var scrutinee = try self.available(found.value);
        for (0..found.depth) |_| scrutinee = try self.unwrap(scrutinee);
        const saved = self.case_subst;
        self.case_subst = .{ .from = outer_t, .to = scrutinee };
        defer self.case_subst = saved;
        self.algorithmFired(.rejected_arm);
        switch (self.types.get(t_ty)) {
            .tag_union => |span| {
                const members = self.types.memberSlice(span);
                const names = try self.gpa.alloc(NameId, members.len);
                defer self.gpa.free(names);
                for (members, names) |m, *name| name.* = m.name;
                var live_names: std.ArrayList(NameId) = .empty;
                defer live_names.deinit(self.gpa);
                var live_arms: std.ArrayList(RegionId) = .empty;
                defer live_arms.deinit(self.gpa);
                for (names, outer) |name, old| {
                    if (!self.tagLive(scrutinee, name)) continue;
                    try live_names.append(self.gpa, name);
                    try live_arms.append(self.gpa, try self.openTagArm(scrutinee, name));
                    try self.fillFrom(old);
                }
                return try self.tagSwitchOn(scrutinee, live_names.items, live_arms.items, &.{}, out_tys);
            },
            .bool_, .str, .int, .float, .dec, .record, .tuple, .list, .nominal, .func, .opaque_, .recursive => {
                const new_arms = try self.gpa.alloc(RegionId, outer.len);
                defer self.gpa.free(new_arms);
                for (new_arms, outer, 0..) |*arm, old, i| {
                    arm.* = try self.openArmAt(scrutinee, keys, @intCast(i));
                    try self.fillFrom(old);
                }
                return try self.switchOn(scrutinee, new_arms, &.{}, out_tys, keys);
            },
        }
    }

    // The switch an arm ends in, when the arm ends in exactly its one
    // output, the switch has no joins, and its arms all end in a value.
    fn topSwitch(self: *const Builder, arm: RegionId) ?NodeId {
        const end = self.store.region(arm).end;
        if (end.kind != .value) return null;
        const refs = self.store.refSlice(end.refs);
        if (refs.len != 1 or refs[0].kind != .node or refs[0].output != 0) return null;
        const id = refs[0].nodeId();
        const n = self.store.node(id);
        if (n.op != .switch_ or n.region != arm or n.tys.len != 1) return null;
        const regions = self.store.regionSlice(n.regions);
        if (regions.len != n.payload) return null;
        for (regions) |r| if (self.store.region(r).end.kind != .value) return null;
        return id;
    }

    // Whether the position `q` can be read where the switch being built
    // stands: its root is visible, and every payload on the way is of a tag
    // that a dominating arm decided.
    fn readable(self: *const Builder, q: Ref) bool {
        var at = q;
        while (at.kind == .node) {
            const n = self.store.node(at.nodeId());
            const arg = self.store.refSlice(n.args);
            switch (n.op) {
                .field, .index, .unwrap => {},
                .payload => if (self.knownKey(arg[0]) != n.payload) return false,
                .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .elem, .opt_field, .prim, .call, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => break,
            }
            at = arg[0];
        }
        return self.visible(at);
    }

    // N7 over one literal switch (normal-form 3.7, 3.13). An arm that a
    // known scrutinee selects replaces the switch; arms a dominating arm
    // rules out, and the later arm of a repeated key, are dropped; the keyed
    // arms go in ascending key order; and a default arm that ends in a
    // literal switch on the same scrutinee merges into this one (N7c).
    fn litSwitch(self: *Builder, spec: NodeSpec) Allocator.Error!Ref {
        const scrutinee = spec.args[0];
        const keys = spec.aux;
        const arms = spec.regions[0..spec.payload];
        std.debug.assert(arms.len == keys.len + 1);
        var excluded: std.ArrayList(u32) = .empty;
        defer excluded.deinit(self.gpa);
        var known = try self.litKnown(scrutinee, &excluded);
        // N13u: a key outside the scrutinee's interval selects no input, and
        // an interval that is one key's value selects that key's arm, as a
        // comparison with the key would decide (`rangeCompare`).
        const range: ?ir.Interval = if (self.algorithmOn(.range_compare)) if (self.rangeOf(scrutinee)) |r| r.interval else null else null;
        if (known == null) if (range) |iv| if (iv.lo == iv.hi) for (keys) |k| {
            if (litIntValue(self.types, self.store.lit(LitId.of(k))) == iv.lo) known = LitId.of(k);
        };
        var kept: std.ArrayList(u32) = .empty;
        defer kept.deinit(self.gpa);
        if (known) |l| {
            const i = std.mem.findScalar(u32, keys, l.index()) orelse keys.len;
            if (try self.armResult(spec, arms[i])) |r| {
                self.algorithmStep();
                return r;
            }
            if (i < keys.len) try kept.append(self.gpa, @intCast(i));
        } else for (keys, 0..) |k, i| {
            if (std.mem.findScalar(u32, excluded.items, k) != null) continue;
            if (std.mem.findScalar(u32, keys[0..i], k) != null) continue;
            if (range) |iv| if (litIntValue(self.types, self.store.lit(LitId.of(k)))) |v| if (!ranges.contains(iv, v)) {
                self.algorithmFired(.range_compare);
                continue;
            };
            try kept.append(self.gpa, @intCast(i));
        }
        std.mem.sort(u32, kept.items, LitOrder{ .b = self, .keys = keys }, LitOrder.lt);
        if (kept.items.len == 0) {
            if (try self.armResult(spec, arms[keys.len])) |r| {
                self.algorithmStep();
                return r;
            }
        }
        if (try self.mergeDefault(spec, kept.items)) |r| {
            self.algorithmStep();
            return r;
        }
        // Keys dropped or reordered.
        const same = kept.items.len == keys.len and for (kept.items, 0..) |k, i| {
            if (k != i) break false;
        } else true;
        if (!same) self.algorithmStep();

        const regions = try self.gpa.alloc(RegionId, kept.items.len + 1 + (spec.regions.len - arms.len));
        defer self.gpa.free(regions);
        const new_keys = try self.gpa.alloc(u32, kept.items.len);
        defer self.gpa.free(new_keys);
        for (kept.items, regions[0..kept.items.len], new_keys) |i, *r, *k| {
            r.* = arms[i];
            k.* = keys[i];
        }
        regions[kept.items.len] = arms[keys.len];
        @memcpy(regions[kept.items.len + 1 ..], spec.regions[arms.len..]);
        var out = spec;
        out.payload = @intCast(kept.items.len + 1);
        out.regions = regions;
        out.aux = new_keys;
        return self.makeByTable(out);
    }

    const LitOrder = struct {
        b: *const Builder,
        keys: []const u32,

        // Integers by value, strings by their bytes (`match.keyLess`).
        fn lt(self: LitOrder, x: u32, y: u32) bool {
            return match.keyLess(self.b.store, self.b.types, self.keys[x], self.keys[y]);
        }
    };

    // The literal `scrutinee` is, when it is one or a dominating arm says so;
    // otherwise null, with the keys dominating default arms exclude appended.
    fn litKnown(self: *Builder, scrutinee: Ref, excluded: *std.ArrayList(u32)) Allocator.Error!?LitId {
        if (self.nodeOf(scrutinee)) |n| if (n.op == .lit) return LitId.of(n.payload);
        for (self.facts.items) |f| {
            if (f.ref != scrutinee or !f.isTest()) continue;
            if (f.lit) |l| return l;
            try excluded.appendSlice(self.gpa, self.store.wordSlice(f.excluded));
        }
        return null;
    }

    // The value of a one-output switch whose taken arm is `arm`, when the
    // arm ends in a value.
    fn armResult(self: *Builder, spec: NodeSpec, arm: RegionId) Allocator.Error!?Ref {
        if (spec.tys.len != 1) return null;
        const v = self.armValue(arm) orelse return null;
        return try self.available(v);
    }

    // N7c: when the default arm ends in exactly the outputs of a literal
    // switch on the same scrutinee, built in that arm and without joins, the
    // two become one switch. The inner arms are copied under the merged
    // switch's facts; an inner key the outer arms already test is unreachable.
    fn mergeDefault(self: *Builder, spec: NodeSpec, kept: []const u32) Allocator.Error!?Ref {
        const keys = spec.aux;
        const default = spec.regions[keys.len];
        const end = self.store.region(default).end;
        if (end.kind != .value) return null;
        const refs = self.store.refSlice(end.refs);
        if (refs.len != spec.tys.len or refs.len == 0 or refs[0].kind != .node) return null;
        const inner_id = refs[0].nodeId();
        for (refs, 0..) |r, k| if (r.kind != .node or r.nodeId() != inner_id or r.output != k) return null;
        const inner = self.store.node(inner_id);
        if (inner.op != .switch_ or inner.aux.len == 0 or inner.region != default) return null;
        if (self.store.refSlice(inner.args)[0] != spec.args[0]) return null;
        if (self.store.regionSlice(inner.regions).len != inner.payload) return null;

        const inner_keys = try self.gpa.dupe(u32, self.store.wordSlice(inner.aux));
        defer self.gpa.free(inner_keys);
        const inner_arms = try self.gpa.dupe(RegionId, self.store.regionSlice(inner.regions));
        defer self.gpa.free(inner_arms);
        var merged: std.ArrayList(u32) = .empty;
        defer merged.deinit(self.gpa);
        var regions: std.ArrayList(RegionId) = .empty;
        defer regions.deinit(self.gpa);
        for (kept) |i| {
            try merged.append(self.gpa, keys[i]);
            try regions.append(self.gpa, spec.regions[i]);
        }
        var copied: std.ArrayList(u32) = .empty;
        defer copied.deinit(self.gpa);
        for (inner_keys, 0..) |k, j| {
            if (std.mem.findScalar(u32, merged.items, k) != null) continue;
            try merged.append(self.gpa, k);
            try copied.append(self.gpa, @intCast(j));
        }
        for (copied.items, kept.len..) |j, idx| {
            try regions.append(self.gpa, try self.openLitArm(spec.args[0], merged.items, @intCast(idx)));
            try self.fillFrom(inner_arms[j]);
        }
        try regions.append(self.gpa, try self.openLitArm(spec.args[0], merged.items, @intCast(merged.items.len)));
        try self.fillFrom(inner_arms[inner_keys.len]);
        try regions.appendSlice(self.gpa, spec.regions[keys.len + 1 ..]);
        var out = spec;
        out.payload = @intCast(merged.items.len + 1);
        out.regions = regions.items;
        out.aux = merged.items;
        return try self.litSwitch(out);
    }

    fn rulesActive(self: *const Builder) bool {
        if (hooks_enabled) return !self.hooks.rules_off;
        return true;
    }

    /// Build a node without applying any rule. Only the derivation tool and
    /// tests reach this, through the rules-off mode or directly.
    pub fn makeRaw(self: *Builder, spec: NodeSpec) Allocator.Error!Ref {
        return self.cons_(spec);
    }

    /// Whether table row `row` matches node `ref` and its conditions hold
    /// there. The derivation tool asks this of a critical pair's peak, built
    /// in the rules-off mode, before the row's region closes.
    pub fn rewrites(self: *Builder, row: usize, ref: Ref) Allocator.Error!bool {
        comptime std.debug.assert(hooks_enabled);
        const n = self.nodeOf(ref) orelse return false;
        const rule = table.rules[row];
        if (rule.root != n.op) return false;
        const spec: NodeSpec = .{
            .op = n.op,
            .payload = n.payload,
            .args = self.store.refSlice(n.args),
            .tys = self.store.tySlice(n.tys),
            .regions = self.store.regionSlice(n.regions),
            .aux = self.store.wordSlice(n.aux),
        };
        var b: Bindings = .{ .conds = rule.conds, .root = spec };
        return try self.matchRoot(rule, spec, &b) and try self.condsHold(rule, &b);
    }

    // A node that owns regions is keyed without its region ids, which are
    // new for every node, and a candidate with the key is the same node only
    // when each of its regions ends alike over equal values (`equal.zig`).
    // So an `if` written twice is one node, like any value written twice.
    // A switch with joins or with no outputs never merges: its joins are
    // still open, and it ends the region it stands in.
    fn cons_(self: *Builder, spec: NodeSpec) Allocator.Error!Ref {
        const here = self.current();
        const start: u32 = @intCast(self.key_words.items.len);
        try self.appendKey(spec);
        const key: NodeKey = .{ .start = start, .len = @as(u32, @intCast(self.key_words.items.len)) - start };
        const gop = try self.cons.getOrPutContext(self.gpa, key, .{ .words = &self.key_words });
        if (gop.found_existing) {
            self.key_words.shrinkRetainingCapacity(start);
            var cand = gop.value_ptr.*;
            while (cand != NodeId.none) {
                if (self.store.encloses(self.store.nodes.items(.region)[cand.index()], here) and try self.sameRegions(cand, spec)) {
                    try self.store.provenance.add(self.gpa, cand, self.origins);
                    return Ref.of(cand);
                }
                cand = self.same_key.items[cand.index()];
            }
        }
        const prev = if (gop.found_existing) gop.value_ptr.* else NodeId.none;
        const n = try self.appendNode(spec, here);
        try self.same_key.append(self.gpa, prev);
        gop.value_ptr.* = n;
        try self.store.provenance.add(self.gpa, n, self.origins);
        return Ref.of(n);
    }

    fn appendKey(self: *Builder, spec: NodeSpec) Allocator.Error!void {
        const w = &self.key_words;
        try w.appendSlice(self.gpa, &.{ @backingInt(spec.op), spec.payload, @intCast(spec.tys.len) });
        for (spec.tys) |t| try w.append(self.gpa, t.index());
        try w.append(self.gpa, @intCast(spec.args.len));
        for (spec.args) |a| {
            const bits: u64 = @bitCast(a);
            try w.appendSlice(self.gpa, &.{ @truncate(bits), @truncate(bits >> 32) });
        }
        try w.append(self.gpa, @intCast(spec.regions.len));
        for (spec.regions) |r| try w.append(self.gpa, @backingInt(self.store.region(r).kind));
        try w.append(self.gpa, @intCast(spec.aux.len));
        try w.appendSlice(self.gpa, spec.aux);
    }

    // Whether node `cand`'s regions end alike, one by one, over equal values
    // to the regions of `spec`.
    fn sameRegions(self: *Builder, cand: NodeId, spec: NodeSpec) Allocator.Error!bool {
        const regions = spec.regions;
        if (regions.len == 0) return true;
        if (spec.op == .switch_ and spec.tys.len == 0) return false;
        if (!self.mergeable(regions)) return false;
        const theirs = self.store.regionSlice(self.store.node(cand).regions);
        if (theirs.len != regions.len) return false;
        var cmp: equal.Comparison = .{ .gpa = self.gpa, .store = self.store };
        defer cmp.deinit();
        for (theirs, regions) |a, b| if (!try cmp.regions(a, b)) return false;
        return true;
    }

    fn mergeable(self: *const Builder, regions: []const RegionId) bool {
        for (regions) |r| {
            const reg = self.store.region(r);
            if (reg.kind == .join or reg.end.kind == .open) return false;
        }
        return true;
    }

    fn appendNode(self: *Builder, spec: NodeSpec, here: RegionId) Allocator.Error!NodeId {
        const range = try self.nodeRange(spec);
        const spec_flag = self.speculatableOf(spec) or (range != null and range.?.fits);
        const n = try self.store.appendNode(.{
            .op = spec.op,
            .flags = .{ .speculatable = spec_flag },
            .payload = spec.payload,
            .region = here,
            .args = try self.store.addRefs(spec.args),
            .tys = try self.store.addTys(spec.tys),
            .regions = try self.store.addRegionIds(spec.regions),
            .aux = try self.store.addWords(spec.aux),
        });
        try self.copy_of.append(self.gpa, null);
        // The facts an interval read are on the stack, so their region
        // encloses the node's, and hash-consing finds the node only in a
        // region its own encloses (`cons_`): the interval holds wherever the
        // node is read.
        if (range) |r| std.debug.assert(r.holds_in == RegionId.none or self.store.encloses(r.holds_in, here));
        if (range) |r| try self.store.ranges.put(self.gpa, n, r);
        self.region_nodes.items[here.index()] += 1;
        for (spec.regions) |r| self.store.setOwner(r, n);
        if (!spec_flag) self.store.regions.items(.speculatable)[here.index()] = false;
        return n;
    }

    fn speculatableOf(self: *const Builder, spec: NodeSpec) bool {
        return switch (opSpeculatable(spec.op)) {
            .always => true,
            .never => false,
            .by_prim => if (prims.lookup(ir.PrimId.of(spec.payload))) |p| p.speculatable else false,
            .by_row => self.store.row(RowId.of(spec.payload)).speculatable,
            .by_regions => for (spec.regions) |r| {
                const reg = self.store.region(r);
                if (!reg.speculatable) break false;
                switch (reg.end.kind) {
                    .value, .continue_ => {},
                    .open, .jump, .return_, .branch, .break_ => break false,
                }
            } else true,
        };
    }

    fn primResultTy(self: *Builder, id: ir.PrimId, args: []const Ref) Allocator.Error!TyId {
        const p = prims.get(id);
        return switch (p.method) {
            .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not => self.types.boolTy(),
            .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat => self.store.refTy(self.row, args[0]),
            .len => self.types.intTy(.u64),
            .is_empty => self.types.boolTy(),
            .append, .keep_if => self.store.refTy(self.row, args[0]),
            .fold => self.store.refTy(self.row, args[1]),
            .get, .map, .collect => unreachable, // their result types are not derivable from their arguments, and they are never built through `call`
        };
    }

    const Bindings = struct {
        vars: [16]?Ref = @splat(null),
        /// A variable bound to a literal that no node holds: a literal
        /// switch's key. Matching builds nothing, so the node is built only
        /// where the rule's result reads the variable as a value.
        lits: [16]?LitId = @splat(null),
        owners: [4]?prims.Owner = @splat(null),
        regions: [4]?RegionId = @splat(null),
        seqs: [4]?Seq = @splat(null),
        /// Runs of a chain's arguments, by the same sequence variables: a
        /// rule's runs are all operands or all arguments.
        arg_seqs: [4]?ArgSeq = @splat(null),
        /// The operands of the node being built, when its root is an `And` or `Or`.
        root_first: Ref = undefined,
        root_regions: []const RegionId = &.{},
        /// The rule's conditions, checked as soon as their variables are
        /// bound, so a failing one makes a sequence variable try its next run.
        conds: []const table.Cond = &.{},
        /// The node being built, which `folds` and `folded` evaluate.
        root: NodeSpec,
    };

    /// Where a run of operands lives: the node being built, or a built node.
    const SeqSrc = union(enum) { root, node: NodeId };

    /// Arguments `lo` to `hi` of `src`. They are read when used: building
    /// nodes can move the store's argument arrays.
    const ArgSeq = struct { src: SeqSrc, lo: u32, hi: u32 };

    fn argsOf(self: *const Builder, src: SeqSrc, b: *const Bindings) []const Ref {
        return switch (src) {
            .root => b.root.args,
            .node => |n| self.store.refSlice(self.store.node(n).args),
        };
    }

    // Arguments `pos` onward of `src` against `pats`, where a run binds a
    // sequence variable, shortest first, as `matchOperands` does.
    fn matchArgs(self: *Builder, pats: []const table.Pat, src: SeqSrc, pos: u32, root: NodeSpec, b: *Bindings) Allocator.Error!bool {
        const count: u32 = @intCast(self.argsOf(src, b).len);
        if (pats.len == 0) return pos == count and try self.boundCondsHold(b);
        switch (pats[0]) {
            .rest => |k| {
                var hi = pos;
                while (hi <= count) : (hi += 1) {
                    var trial = b.*;
                    trial.arg_seqs[k] = .{ .src = src, .lo = pos, .hi = hi };
                    if (try self.matchArgs(pats[1..], src, hi, root, &trial)) {
                        b.* = trial;
                        return true;
                    }
                }
                return false;
            },
            .any, .lit_bool, .lit_int, .prim, .op, .component, .bool_switch, .connective, .same_arms, .tag_arm, .identity, .absorbing, .lit_switch => {
                if (pos >= count) return false;
                var trial = b.*;
                if (!try self.matchPat(pats[0], self.argsOf(src, b)[pos], root, &trial)) return false;
                if (!try self.matchArgs(pats[1..], src, pos + 1, root, &trial)) return false;
                b.* = trial;
                return true;
            },
        }
    }

    /// Operands `lo` to `hi` of `src`, where operand 0 is the first and
    /// operand `i` is region `i - 1`.
    const Seq = struct { src: SeqSrc, lo: u32, hi: u32 };

    fn operandCount(self: *const Builder, src: SeqSrc, b: *const Bindings) u32 {
        return 1 + @as(u32, @intCast(switch (src) {
            .root => b.root_regions.len,
            .node => |n| self.store.node(n).regions.len,
        }));
    }

    fn operandFirst(self: *const Builder, src: SeqSrc, b: *const Bindings) Ref {
        return switch (src) {
            .root => b.root_first,
            .node => |n| self.store.refSlice(self.store.node(n).args)[0],
        };
    }

    fn operandRegion(self: *const Builder, src: SeqSrc, b: *const Bindings, i: u32) RegionId {
        return switch (src) {
            .root => b.root_regions[i - 1],
            .node => |n| self.store.regionSlice(self.store.node(n).regions)[i - 1],
        };
    }

    // The value operand `i` of `src` delivers.
    fn matchRoot(self: *Builder, rule: table.Rule, spec: NodeSpec, b: *Bindings) Allocator.Error!bool {
        if (rule.root == .switch_) {
            if (spec.args.len != 1) return false;
            return switch (rule.args[0]) {
                .bool_switch => |bs| self.matchSwitch(bs, spec.args[0], spec.regions, spec.payload, spec.tys.len, spec.aux.len, spec, b),
                .same_arms => |sa| self.matchSameArms(sa, spec, b),
                .tag_arm => |k| self.matchTagArm(k, spec, b),
                .lit_switch => |ls| self.matchLitSwitch(ls, spec, spec, b),
                .any, .lit_bool, .lit_int, .prim, .op, .component, .connective, .rest, .identity, .absorbing => unreachable, // the table check keeps only switch-shaped argument patterns at a switch_ root
            };
        }
        if (rule.root == .and_ or rule.root == .or_) {
            if (spec.args.len != 1) return false;
            b.root_first = spec.args[0];
            b.root_regions = spec.regions;
            return self.matchOperands(rule.args[0].connective.operands, .root, 0, spec, b);
        }
        if (rule.root_prim) |rp| {
            const p = prims.lookup(ir.PrimId.of(spec.payload)) orelse return false;
            if (p.method != rp.method) return false;
            if (!bindOwner(rp.owner, p.owner, b)) return false;
        }
        return self.matchArgs(rule.args, .root, 0, spec, b);
    }

    fn matchSwitch(self: *Builder, bs: @FieldType(table.Pat, "bool_switch"), scrutinee: Ref, regions: []const RegionId, arms: u32, outputs: usize, keys: usize, root: NodeSpec, b: *Bindings) Allocator.Error!bool {
        if (!polarity.isBoolSwitch(self.types, self.store.refTy(self.row, scrutinee), arms, regions.len, outputs, keys)) return false;
        if (!try self.matchPat(bs.scrutinee.*, scrutinee, root, b)) return false;
        // The arms of this switch bind their region variables before a nested
        // switch's arms do, so a template reuses the arm it can reuse.
        for (bs.arms, regions) |arm, r| switch (arm) {
            .lit, .region => if (!try self.matchArm(arm, r, root, b)) return false,
            .value => {},
        };
        for (bs.arms, regions) |arm, r| switch (arm) {
            .value => if (!try self.matchArm(arm, r, root, b)) return false,
            .lit, .region => {},
        };
        return true;
    }

    // A switch with one output whose every arm ends in one value, which a
    // result reads through `region_value`.
    fn valueArms(self: *const Builder, spec: NodeSpec) bool {
        if (spec.tys.len != 1 or spec.regions.len != spec.payload) return false;
        for (spec.regions) |r| if (self.armValue(r) == null) return false;
        return true;
    }

    fn matchSameArms(self: *Builder, sa: @FieldType(table.Pat, "same_arms"), spec: NodeSpec, b: *Bindings) Allocator.Error!bool {
        if (!self.valueArms(spec)) return false;
        if (!try self.matchPat(sa.scrutinee.*, spec.args[0], spec, b)) return false;
        for (spec.regions) |r| if (!try self.matchArm(.{ .region = sa.region }, r, spec, b)) return false;
        return true;
    }

    // The key reads as its literal node, built here like any literal.
    fn matchLitSwitch(self: *Builder, ls: @FieldType(table.Pat, "lit_switch"), spec: NodeSpec, root: NodeSpec, b: *Bindings) Allocator.Error!bool {
        if (spec.aux.len != 1 or spec.tys.len != 1 or spec.payload != 2 or spec.regions.len != 2) return false;
        const lit = self.store.lit(LitId.of(spec.aux[0]));
        const int = switch (self.types.get(lit.ty)) {
            .int => |i| i,
            .bool_, .str, .float, .dec, .record, .tuple, .tag_union, .list, .nominal, .func, .opaque_, .recursive => return false,
        };
        if (!bindOwner(ls.owner, prims.Owner.ofInt(int), b)) return false;
        if (!try self.matchPat(ls.scrutinee.*, spec.args[0], root, b)) return false;
        // Every key pattern of the table is a variable (`table.zig`, the mirror of a `Bool` switch).
        const key = switch (ls.key.*) {
            .any => |k| k,
            .lit_bool, .lit_int, .prim, .op, .component, .bool_switch, .connective, .same_arms, .tag_arm, .rest, .identity, .absorbing, .lit_switch => unreachable, // every key pattern of a literal-switch rule is a variable (table check)
        };
        if (!self.bindLit(key, LitId.of(spec.aux[0]), b)) return false;
        // As in `matchSwitch`, this switch's arms bind their region variables first.
        for (ls.arms, spec.regions) |arm, r| switch (arm) {
            .lit, .region => if (!try self.matchArm(arm, r, root, b)) return false,
            .value => {},
        };
        for (ls.arms, spec.regions) |arm, r| switch (arm) {
            .value => if (!try self.matchArm(arm, r, root, b)) return false,
            .lit, .region => {},
        };
        return true;
    }

    fn matchTagArm(self: *Builder, k: table.RegionVar, spec: NodeSpec, b: *Bindings) Allocator.Error!bool {
        if (!self.valueArms(spec) or spec.aux.len != 0) return false;
        const n = self.nodeOf(spec.args[0]) orelse return false;
        if (n.op != .tag) return false;
        // A tag switch has one arm per member of its scrutinee's type, in
        // member order, so the tag's name finds its arm.
        const arm = self.types.memberIndex(self.store.tySlice(n.tys)[0], NameId.of(n.payload)) orelse
            @import("base").invariant("reify builder: a tag is not a member of its own union", .{});
        b.regions[k] = spec.regions[arm];
        return true;
    }

    // Match `elems` against the operands of `src` from operand `pos` on. A
    // sequence variable tries its shortest run first, and the next when the
    // rest of the elements, or a condition bound by then, fails.
    fn matchOperands(self: *Builder, elems: []const table.OperandPat, src: SeqSrc, pos: u32, root: NodeSpec, b: *Bindings) Allocator.Error!bool {
        const count = self.operandCount(src, b);
        if (elems.len == 0) return pos == count and try self.boundCondsHold(b);
        switch (elems[0]) {
            .arm => |arm| {
                if (pos >= count) return false;
                var trial = b.*;
                const ok = if (pos == 0)
                    try self.matchFirst(arm, self.operandFirst(src, b), root, &trial)
                else
                    try self.matchArm(arm, self.operandRegion(src, b, pos), root, &trial);
                if (!ok or !try self.matchOperands(elems[1..], src, pos + 1, root, &trial)) return false;
                b.* = trial;
                return true;
            },
            .rest => |k| {
                var hi = pos;
                while (hi <= count) : (hi += 1) {
                    var trial = b.*;
                    trial.seqs[k] = .{ .src = src, .lo = pos, .hi = hi };
                    if (try self.matchOperands(elems[1..], src, hi, root, &trial)) {
                        b.* = trial;
                        return true;
                    }
                }
                return false;
            },
        }
    }

    // The first operand is a value, not a region.
    fn matchFirst(self: *Builder, arm: table.Arm, ref: Ref, root: NodeSpec, b: *Bindings) Allocator.Error!bool {
        switch (arm) {
            .region => return false,
            .lit => |want| {
                const n = self.nodeOf(ref) orelse return false;
                if (n.op != .lit) return false;
                return switch (self.store.lit(LitId.of(n.payload)).value) {
                    .bool_ => |v| v == want,
                    .int, .float, .str, .dec, .bytes => false,
                };
            },
            .value => |pat| return self.matchPat(pat.*, ref, root, b),
        }
    }

    fn matchArm(self: *Builder, arm: table.Arm, r: RegionId, root: NodeSpec, b: *Bindings) Allocator.Error!bool {
        switch (arm) {
            .region => |k| {
                if (b.regions[k]) |bound| {
                    var cmp: equal.Comparison = .{ .gpa = self.gpa, .store = self.store };
                    defer cmp.deinit();
                    return cmp.regions(bound, r);
                }
                b.regions[k] = r;
                return true;
            },
            .lit => |want| {
                const n = self.nodeOf(self.armValue(r) orelse return false) orelse return false;
                if (n.op != .lit) return false;
                return switch (self.store.lit(LitId.of(n.payload)).value) {
                    .bool_ => |v| v == want,
                    .int, .float, .str, .dec, .bytes => false,
                };
            },
            .value => |pat| return self.matchPat(pat.*, self.armValue(r) orelse return false, root, b),
        }
    }

    // The one value a region ends with, if it ends in `Value` with one.
    fn armValue(self: *const Builder, r: RegionId) ?Ref {
        return polarity.armValue(self.store, r);
    }

    fn bindOwner(pat: table.OwnerPat, owner: prims.Owner, b: *Bindings) bool {
        switch (pat) {
            .fixed => |o| return o == owner,
            .bind => |k| {
                if (b.owners[k]) |bound| return bound == owner;
                b.owners[k] = owner;
                return true;
            },
        }
    }

    fn bindVar(self: *const Builder, k: table.Var, ref: Ref, b: *Bindings) bool {
        if (b.lits[k]) |l| return self.isLit(ref, l);
        if (b.vars[k]) |bound| return bound == ref;
        b.vars[k] = ref;
        return true;
    }

    fn bindLit(self: *const Builder, k: table.Var, l: LitId, b: *Bindings) bool {
        if (b.vars[k]) |bound| return self.isLit(bound, l);
        if (b.lits[k]) |bound| return bound == l;
        b.lits[k] = l;
        return true;
    }

    // Whether `ref` is the node of literal `l`.
    fn isLit(self: *const Builder, ref: Ref, l: LitId) bool {
        const n = self.nodeOf(ref) orelse return false;
        return n.op == .lit and n.payload == l.index();
    }

    fn matchPat(self: *Builder, pat: table.Pat, ref: Ref, root: NodeSpec, b: *Bindings) Allocator.Error!bool {
        switch (pat) {
            .any => |k| return self.bindVar(k, ref, b),
            .lit_bool => |want| {
                const n = self.nodeOf(ref) orelse return false;
                if (n.op != .lit) return false;
                return switch (self.store.lit(LitId.of(n.payload)).value) {
                    .bool_ => |v| v == want,
                    .int, .float, .str, .dec, .bytes => false,
                };
            },
            .lit_int => |want| {
                const n = self.nodeOf(ref) orelse return false;
                if (n.op != .lit) return false;
                return litIntValue(self.types, self.store.lit(LitId.of(n.payload))) == want;
            },
            .prim => |pp| {
                const n = self.nodeOf(ref) orelse return false;
                if (n.op != .prim) return false;
                const p = prims.lookup(ir.PrimId.of(n.payload)) orelse return false;
                if (p.method != pp.method) return false;
                if (!bindOwner(pp.owner, p.owner, b)) return false;
                return self.matchArgs(pp.args, .{ .node = ref.nodeId() }, 0, root, b);
            },
            .identity => {
                const n = self.nodeOf(ref) orelse return false;
                const p = prims.get(ir.PrimId.of(root.payload));
                // The identity of `List.concat` is the empty list, and of `Str.concat` the empty string.
                if (p.method == .concat) return switch (p.owner) {
                    .list => n.op == .list and n.args.len == 0,
                    .str => n.op == .lit and switch (self.store.lit(LitId.of(n.payload)).value) {
                        .str => |text| text.len == 0,
                        .int, .float, .bool_, .dec, .bytes => false,
                    },
                    .bool_, .iter, .u8, .i8, .u16, .i16, .u32, .i32, .u64, .i64, .u128, .i128, .f32, .f64 => false,
                };
                if (n.op != .lit) return false;
                const want = prims.identityInt(p.owner.int() orelse return false, p.method) orelse return false;
                return litIntValue(self.types, self.store.lit(LitId.of(n.payload))) == want;
            },
            .absorbing => |k| {
                const n = self.nodeOf(ref) orelse return false;
                if (n.op != .lit) return false;
                const p = prims.get(ir.PrimId.of(root.payload));
                const want = prims.absorbingInt(p.owner.int() orelse return false, p.method) orelse return false;
                if (litIntValue(self.types, self.store.lit(LitId.of(n.payload))) != want) return false;
                return self.bindVar(k, ref, b);
            },
            // `matchArgs` binds a run.
            .rest => unreachable, // matchArgs binds a run, so a rest pattern never reaches matchPat
            .op => |op| {
                const n = self.nodeOf(ref) orelse return false;
                if (n.op != op.op) return false;
                const args = self.store.refSlice(n.args);
                if (args.len != op.args.len) return false;
                for (op.args, args) |sub, a| {
                    if (!try self.matchPat(sub, a, root, b)) return false;
                }
                return true;
            },
            .component => |c| {
                const n = self.nodeOf(ref) orelse return false;
                if (n.op != c.op) return false;
                const position: u32 = switch (root.op) {
                    .field, .index => root.payload,
                    .payload => blk: {
                        if (n.payload != root.payload) return false;
                        break :blk root.aux[0];
                    },
                    .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => return false,
                };
                const args = self.store.refSlice(n.args);
                // A record that leaves a member unset lists the members it
                // sets, and a read of an unset member has no value to bind.
                const at = if (n.op == .record) self.recordArgAt(n, position) orelse return false else position;
                return self.bindVar(c.bind, args[at], b);
            },
            .bool_switch => |bs| {
                const n = self.nodeOf(ref) orelse return false;
                if (n.op != .switch_ or ref.output != 0) return false;
                return self.matchSwitch(bs, self.store.refSlice(n.args)[0], self.store.regionSlice(n.regions), n.payload, n.tys.len, n.aux.len, root, b);
            },
            .connective => |c| {
                const n = self.nodeOf(ref) orelse return false;
                if (n.op != c.op) return false;
                return self.matchOperands(c.operands, .{ .node = ref.nodeId() }, 0, root, b);
            },
            .lit_switch => |ls| {
                const n = self.nodeOf(ref) orelse return false;
                if (n.op != .switch_ or ref.output != 0) return false;
                return self.matchLitSwitch(ls, .{
                    .op = n.op,
                    .payload = n.payload,
                    .args = self.store.refSlice(n.args),
                    .tys = self.store.tySlice(n.tys),
                    .regions = self.store.regionSlice(n.regions),
                    .aux = self.store.wordSlice(n.aux),
                }, root, b);
            },
            // The table's check keeps these at a `switch_` root.
            .same_arms, .tag_arm => unreachable, // the table check keeps same_arms and tag_arm at a switch_ root
        }
    }

    fn nodeOf(self: *const Builder, ref: Ref) ?ir.Node {
        return switch (ref.kind) {
            .node => self.store.node(ref.nodeId()),
            .row_param, .region_param, .input => null,
        };
    }

    fn condsHold(self: *Builder, rule: table.Rule, b: *const Bindings) Allocator.Error!bool {
        for (rule.conds) |c| if (!try self.condHolds(c, b)) return false;
        return true;
    }

    fn boundCondsHold(self: *Builder, b: *const Bindings) Allocator.Error!bool {
        for (b.conds) |c| {
            const bound = switch (c) {
                .int_owner, .key_owner, .not_float_owner => |k| b.owners[k] != null,
                .is_lit, .speculatable, .nonzero_lit, .polarity_flips, .same_ty, .lit_bool_switch, .not_lit => |k| b.vars[k] != null or b.lits[k] != null,
                .movable => |k| b.regions[k] != null,
                .movable_rest => |k| b.seqs[k] != null,
                .speculatable_rest => |k| b.arg_seqs[k] != null,
                // Its operands are the root's, checked once the rule matched.
                .folds, .folds_pair => false,
            };
            if (bound and !try self.condHolds(c, b)) return false;
        }
        return true;
    }

    fn condHolds(self: *Builder, c: table.Cond, b: *const Bindings) Allocator.Error!bool {
        // A literal no node holds is a literal, speculatable, and no `Bool` switch.
        switch (c) {
            .is_lit, .speculatable, .nonzero_lit, .polarity_flips, .same_ty, .lit_bool_switch, .not_lit => |k| if (b.lits[k]) |l| return switch (c) {
                .is_lit, .speculatable => true,
                .nonzero_lit => litNonzero(self.store.lit(l).value),
                .same_ty => self.store.lit(l).ty == b.root.tys[0],
                .polarity_flips, .lit_bool_switch, .not_lit => false,
                .int_owner, .key_owner, .not_float_owner, .movable, .movable_rest, .speculatable_rest, .folds, .folds_pair => unreachable, // these conditions are not literal-indexed, so the outer prong never selects them
            },
            .int_owner, .key_owner, .not_float_owner, .movable, .movable_rest, .speculatable_rest, .folds, .folds_pair => {},
        }
        return switch (c) {
            .int_owner => |k| b.owners[k].?.int() != null,
            .key_owner => |k| b.owners[k].?.int() != null or b.owners[k].? == .str,
            .not_float_owner => |k| b.owners[k].?.float() == null,
            .is_lit => |k| if (self.nodeOf(b.vars[k].?)) |n| n.op == .lit else false,
            .speculatable => |k| try self.coneSpeculatable(b.vars[k].?),
            .nonzero_lit => |k| if (self.nodeOf(b.vars[k].?)) |n| n.op == .lit and litNonzero(self.store.lit(LitId.of(n.payload)).value) else false,
            .movable => |k| try self.movable(b.regions[k].?),
            .movable_rest => |k| blk: {
                const seq = b.seqs[k].?;
                var i = @max(seq.lo, 1);
                while (i < seq.hi) : (i += 1) {
                    if (!try self.movable(self.operandRegion(seq.src, b, i))) break :blk false;
                }
                break :blk true;
            },
            .speculatable_rest => |k| blk: {
                const seq = b.arg_seqs[k].?;
                for (self.argsOf(seq.src, b)[seq.lo..seq.hi]) |a| {
                    if (!try self.coneSpeculatable(a)) break :blk false;
                }
                break :blk true;
            },
            .polarity_flips => |k| polarity.flips(self.store, self.types, b.vars[k].?),
            .folds => blk: {
                const folded = try self.foldOf(b.root) orelse break :blk false;
                if (folded == .str) self.gpa.free(folded.str);
                break :blk true;
            },
            .folds_pair => |pair| blk: {
                const folded = try self.foldPair(b, pair) orelse break :blk false;
                if (folded == .str) self.gpa.free(folded.str);
                break :blk true;
            },
            .same_ty => |k| self.store.refTy(self.row, b.vars[k].?) == b.root.tys[0],
            .lit_bool_switch => |k| if (self.nodeOf(b.vars[k].?)) |n| n.op == .switch_ and n.aux.len > 0 and polarity.boolArms(self.store, self.types, n) != null else false,
            .not_lit => |k| if (self.nodeOf(b.vars[k].?)) |n| n.op != .lit else true,
        };
    }

    // The root's builtin over the two literals the variables of `pair` bound.
    fn foldPair(self: *const Builder, b: *const Bindings, pair: [2]table.Var) Allocator.Error!?prims.Folded {
        const args = [2]Ref{ b.vars[pair[0]].?, b.vars[pair[1]].? };
        return self.foldOf(.{ .op = .prim, .payload = b.root.payload, .args = &args, .tys = b.root.tys });
    }

    // The value of the builtin `spec` builds over its literal operands, or
    // null where it fails or no literal of its owner folds. Integers fold by
    // the evaluator's arithmetic, which is exact; floats fold by the IEEE
    // operations of their type in strict float mode, with Roc's canonical
    // `NaN` (`prims.foldFloat`), so the bits do not depend on the host; and
    // `Str` folds its equality and its concatenation. A `str` result is owned
    // by the caller.
    fn foldOf(self: *const Builder, spec: NodeSpec) Allocator.Error!?prims.Folded {
        // A builtin the table does not hold, or a function of another package,
        // has no semantics to fold with.
        const p = prims.lookup(ir.PrimId.of(spec.payload)) orelse return null;
        if (p.owner.int()) |int| {
            const ints = try self.gpa.alloc(i256, spec.args.len);
            defer self.gpa.free(ints);
            for (spec.args, ints) |a, *v| v.* = litIntValue(self.types, self.store.lit(LitId.of(self.nodeOf(a).?.payload))).?;
            return prims.foldIntAll(int, p.method, ints);
        }
        const lits = try self.gpa.alloc(ir.Lit, spec.args.len);
        defer self.gpa.free(lits);
        for (spec.args, lits) |a, *v| v.* = self.store.lit(LitId.of(self.nodeOf(a).?.payload));
        if (p.owner.float()) |float| {
            const second: u64 = if (lits.len > 1) lits[1].value.float else 0;
            return prims.foldFloat(float, p.method, lits[0].value.float, second);
        }
        return switch (p.owner) {
            .bool_ => switch (p.method) {
                .not => .{ .bool_ = !lits[0].value.bool_ },
                .is_eq => .{ .bool_ = lits[0].value.bool_ == lits[1].value.bool_ },
                .is_lt, .is_lte, .is_gt, .is_gte, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect => unreachable, // bool owners only have the not and is_eq folds
            },
            .str => switch (p.method) {
                .is_eq => .{ .bool_ = std.mem.eql(u8, self.store.byteSlice(lits[0].value.str), self.store.byteSlice(lits[1].value.str)) },
                // A chain N15a flattened concatenates every operand in order.
                .concat => blk: {
                    var out: std.ArrayList(u8) = .empty;
                    errdefer out.deinit(self.gpa);
                    for (lits) |l| try out.appendSlice(self.gpa, self.store.byteSlice(l.value.str));
                    break :blk .{ .str = try out.toOwnedSlice(self.gpa) };
                },
                .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect => unreachable, // str owners only have the is_eq and concat folds
            },
            // A list literal is the embedded bytes of a file, whose elements
            // the rules do not read, and an iterator is never a literal.
            .list, .iter => null,
            .f32, .f64, .u8, .i8, .u16, .i16, .u32, .i32, .u64, .i64, .u128, .i128 => unreachable, // number owners fold above
        };
    }

    // The value of an integer literal, or null for another literal. The bits
    // of `-1` at `I128` and of the highest `U128` are one `u128`; only the
    // type tells them apart.
    fn litIntValue(types: *const types_mod.Types, lit: ir.Lit) ?i256 {
        return match.litIntValue(types, lit);
    }

    fn litNonzero(v: ir.LitValue) bool {
        return switch (v) {
            .int => |bits| bits != 0,
            .float => |bits| (bits << 1) != 0,
            .bool_ => |x| x,
            .dec => |bits| bits != 0,
            .str, .bytes => false,
        };
    }

    // `tys` are the output types of the node the rule replaces; a result
    // switch delivers them.
    fn instantiate(self: *Builder, t: table.Tmpl, b: *const Bindings, tys: []const TyId) Allocator.Error!Ref {
        switch (t) {
            .var_ => |k| {
                if (b.lits[k]) |l| return self.makeByTable(.{ .op = .lit, .payload = l.index(), .tys = &.{self.store.lit(l).ty} });
                return self.available(b.vars[k].?);
            },
            .prim => |pp| {
                const owner: prims.Owner = switch (pp.owner) {
                    .fixed => |o| o,
                    .bind => |k| b.owners[k].?,
                };
                var args: std.ArrayList(Ref) = .empty;
                defer args.deinit(self.gpa);
                for (pp.args) |sub| switch (sub) {
                    .rest => |k| {
                        const seq = b.arg_seqs[k].?;
                        const run = try self.gpa.dupe(Ref, self.argsOf(seq.src, b)[seq.lo..seq.hi]);
                        defer self.gpa.free(run);
                        for (run) |a| try args.append(self.gpa, try self.available(a));
                    },
                    .var_, .prim, .bool_switch, .and_, .or_, .region_value, .lit_bool, .lit_int, .folded, .folded_pair, .negation, .lit_switch => try args.append(self.gpa, try self.instantiate(sub, b, tys)),
                };
                // A chain of one operand is that operand, as a one-operand `And` is.
                if (args.items.len == 1 and prims.associativeOf(pp.method)) return args.items[0];
                return self.call(owner, pp.method, args.items);
            },
            .rest => unreachable, // rest is expanded among a chain's arguments above
            .bool_switch => |bs| {
                const bool_ty = try self.types.boolTy();
                const scrutinee = try self.instantiate(bs.scrutinee.*, b, &.{bool_ty});
                var arms: [2]RegionId = undefined;
                for (&arms, bs.arms, 0..) |*arm, a, key| switch (a) {
                    .region => |k| {
                        const r = b.regions[k].?;
                        if (self.store.region(r).owner == NodeId.none) {
                            arm.* = r;
                        } else {
                            arm.* = try self.openArm(scrutinee, @intCast(key));
                            try self.fillFrom(r);
                        }
                    },
                    .value => |v| {
                        arm.* = try self.openArm(scrutinee, @intCast(key));
                        const value = try self.instantiate(v.*, b, tys);
                        try self.close(.{ .value = &.{value} });
                    },
                };
                return self.switchOn(scrutinee, &arms, &.{}, tys, &.{});
            },
            .and_, .or_ => |ops| return self.connectiveOf(if (t == .and_) .and_ else .or_, ops, b),
            .region_value => |k| return self.available(self.armValue(b.regions[k].?).?),
            .lit_bool => |v| return self.litBool(v),
            .lit_int => |l| {
                const owner: prims.Owner = switch (l.owner) {
                    .fixed => |o| o,
                    .bind => |k| b.owners[k].?,
                };
                return self.litInt(try self.types.intTy(owner.int().?), l.value);
            },
            .negation => |v| return self.negationOf(try self.instantiate(v.*, b, tys)),
            .lit_switch => |ls| {
                const scrutinee = try self.instantiate(ls.scrutinee.*, b, tys);
                // The key is a literal by the row's condition, read without a
                // node where no node holds it.
                const key: u32 = switch (ls.key.*) {
                    .var_ => |k| if (b.lits[k]) |l| l.index() else self.nodeOf(try self.instantiate(ls.key.*, b, tys)).?.payload,
                    .prim, .bool_switch, .and_, .or_, .region_value, .lit_bool, .lit_int, .folded, .folded_pair, .rest, .negation, .lit_switch => self.nodeOf(try self.instantiate(ls.key.*, b, tys)).?.payload,
                };
                const keys = [_]u32{key};
                var arms: [2]RegionId = undefined;
                for (ls.arms, &arms, 0..) |a, *arm, i| {
                    arm.* = try self.openLitArm(scrutinee, &keys, @intCast(i));
                    switch (a) {
                        .region => |k| try self.fillFrom(b.regions[k].?),
                        .value => |v| {
                            const value = try self.instantiate(v.*, b, tys);
                            try self.close(.{ .value = &.{value} });
                        },
                    }
                }
                return self.switchOn(scrutinee, &arms, &.{}, tys, &keys);
            },
            .folded => return self.literalOf((try self.foldOf(b.root)).?, tys[0]),
            .folded_pair => |pair| return self.literalOf((try self.foldPair(b, pair)).?, tys[0]),
        }
    }

    // The literal of type `ty` that holds a folded value.
    fn literalOf(self: *Builder, folded: prims.Folded, ty: TyId) Allocator.Error!Ref {
        return switch (folded) {
            .bool_ => |v| self.litBool(v),
            .int => |v| self.litRef(ty, .{ .int = @truncate(@as(u256, @bitCast(v))) }),
            .float => |bits| self.litRef(ty, .{ .float = bits }),
            .str => |text| {
                defer self.gpa.free(text);
                return self.litStr(text);
            },
        };
    }

    /// The negation of `ref`, built in the current region with the
    /// `Bool.not` pushed to the leaves (`table.Tmpl.negation`).
    fn negationOf(self: *Builder, ref: Ref) Allocator.Error!Ref {
        const n = self.nodeOf(ref) orelse return self.call(.bool_, .not, &.{ref});
        switch (n.op) {
            .and_, .or_ => {
                const dual: Op = if (n.op == .and_) .or_ else .and_;
                const first = try self.negationOf(try self.available(self.store.refSlice(n.args)[0]));
                const old = try self.gpa.dupe(RegionId, self.store.regionSlice(n.regions));
                defer self.gpa.free(old);
                const regions = try self.gpa.alloc(RegionId, old.len);
                defer self.gpa.free(regions);
                for (old, regions) |r, *o| {
                    o.* = try self.openOperand(&.{first}, dual);
                    const v = try self.negationOf(try self.available(self.armValue(r).?));
                    try self.close(.{ .value = &.{v} });
                }
                return if (dual == .and_) self.andOf(first, regions) else self.orOf(first, regions);
            },
            .prim => {
                const p = prims.lookup(ir.PrimId.of(n.payload)) orelse return self.call(.bool_, .not, &.{ref});
                const args = self.store.refSlice(n.args);
                if (p.method == .not) return self.available(args[0]);
                if (p.owner.int() != null and (p.method == .is_lt or p.method == .is_lte)) {
                    const a = args[0];
                    const c = args[1];
                    return self.call(p.owner, if (p.method == .is_lt) .is_lte else .is_lt, &.{ c, a });
                }
                return self.call(.bool_, .not, &.{ref});
            },
            .switch_ => {
                const arms_now = polarity.boolArms(self.store, self.types, n) orelse return self.call(.bool_, .not, &.{ref});
                const scrutinee = self.store.refSlice(n.args)[0];
                const keys = try self.gpa.dupe(u32, self.store.wordSlice(n.aux));
                defer self.gpa.free(keys);
                const old = try self.gpa.dupe(RegionId, arms_now);
                defer self.gpa.free(old);
                const arms = try self.gpa.alloc(RegionId, old.len);
                defer self.gpa.free(arms);
                for (old, arms, 0..) |r, *o, key| {
                    o.* = try self.openArmAt(scrutinee, keys, @intCast(key));
                    const v = try self.negationOf(try self.available(self.armValue(r).?));
                    try self.close(.{ .value = &.{v} });
                }
                return self.switchOn(scrutinee, arms, &.{}, &.{try self.types.boolTy()}, keys);
            },
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .call, .for_range, .for_list, .loop, .lambda, .apply => return self.call(.bool_, .not, &.{ref}),
        }
    }

    /// One operand of an `And` or `Or` result, before it is placed.
    const Item = struct {
        what: union(enum) { ref: Ref, region: RegionId, tmpl: *const table.Tmpl },
        negated: bool = false,
    };

    fn connectiveOf(self: *Builder, op: Op, ops: []const table.OperandTmpl, b: *const Bindings) Allocator.Error!Ref {
        var items: std.ArrayList(Item) = .empty;
        defer items.deinit(self.gpa);
        for (ops) |o| switch (o) {
            .value => |t| try items.append(self.gpa, .{ .what = .{ .tmpl = t } }),
            .region => |k| try items.append(self.gpa, .{ .what = .{ .region = b.regions[k].? } }),
            .rest, .negated_rest => |k| {
                const seq = b.seqs[k].?;
                var i = seq.lo;
                while (i < seq.hi) : (i += 1) {
                    const what: @FieldType(Item, "what") = if (i == 0) .{ .ref = self.operandFirst(seq.src, b) } else .{ .region = self.operandRegion(seq.src, b, i) };
                    try items.append(self.gpa, .{ .what = what, .negated = o == .negated_rest });
                }
            },
        };
        const first = try self.itemValue(items.items[0], b);
        // A one-operand `And` or `Or` is its operand, as N13p makes it.
        if (items.items.len == 1) return first;
        var regions: std.ArrayList(RegionId) = .empty;
        defer regions.deinit(self.gpa);
        for (items.items[1..]) |item| {
            // An operand region of the node being built is placed as it is.
            if (item.what == .region and !item.negated and self.store.region(item.what.region).owner == NodeId.none) {
                self.store.regions.items(.kind)[item.what.region.index()] = .operand;
                try regions.append(self.gpa, item.what.region);
                continue;
            }
            const r = try self.openOperand(&.{first}, op);
            const value = try self.itemValue(item, b);
            try self.close(.{ .value = &.{value} });
            try regions.append(self.gpa, r);
        }
        return if (op == .and_) self.andOf(first, regions.items) else self.orOf(first, regions.items);
    }

    // The item's value, built in the current region.
    fn itemValue(self: *Builder, item: Item, b: *const Bindings) Allocator.Error!Ref {
        const bool_ty = try self.types.boolTy();
        const v = switch (item.what) {
            .ref => |r| try self.available(r),
            .region => |r| try self.available(self.armValue(r).?),
            .tmpl => |t| try self.instantiate(t.*, b, &.{bool_ty}),
        };
        return if (item.negated) self.negationOf(v) else v;
    }

    /// The value `ref` reads, available in the current region: `ref` itself
    /// when its node or parameter is visible here, else a copy built here,
    /// with every region the copied nodes own copied too.
    pub fn available(self: *Builder, ref: Ref) Allocator.Error!Ref {
        if (self.case_subst) |sub| if (ref == sub.from) return sub.to;
        if (self.visible(ref)) return ref;
        switch (ref.kind) {
            .row_param, .input => unreachable, // a row parameter or a slot is visible in every region of its own row
            .region_param => {
                if (self.param_subst.get(ref.regionId())) |values| return values[ref.output];
                const c = self.region_copy.items[ref.target];
                std.debug.assert(c != RegionId.none and self.store.encloses(c, self.current()));
                return Ref.regionParam(c, ref.output);
            },
            .node => {
                const n = ref.nodeId();
                const copy = if (self.copy_of.items[n.index()]) |c| (if (self.visible(c)) c else try self.copyNode(n)) else try self.copyNode(n);
                if (ref.output == 0) return copy;
                return Ref.node(copy.nodeId(), ref.output);
            },
        }
    }

    fn visible(self: *const Builder, ref: Ref) bool {
        const here = self.current();
        return switch (ref.kind) {
            .row_param, .input => true,
            .region_param => self.store.encloses(ref.regionId(), here),
            .node => self.store.encloses(self.store.nodes.items(.region)[ref.target], here),
        };
    }

    fn copyNode(self: *Builder, n: NodeId) Allocator.Error!Ref {
        // The copy is the node, so it comes from where the node came from.
        const origins = try self.gpa.dupe(provenance.OriginId, self.store.provenance.of(n));
        defer self.gpa.free(origins);
        const outer = self.origins;
        self.origins = origins;
        defer self.origins = outer;
        const nd = self.store.node(n);
        // Building appends to the pools these spans point into, so the copy reads owned slices.
        const old_args = try self.gpa.dupe(Ref, self.store.refSlice(nd.args));
        defer self.gpa.free(old_args);
        const tys = try self.gpa.dupe(TyId, self.store.tySlice(nd.tys));
        defer self.gpa.free(tys);
        const aux = try self.gpa.dupe(u32, self.store.wordSlice(nd.aux));
        defer self.gpa.free(aux);
        const old_regions = try self.gpa.dupe(RegionId, self.store.regionSlice(nd.regions));
        defer self.gpa.free(old_regions);

        const args = try self.gpa.alloc(Ref, old_args.len);
        defer self.gpa.free(args);
        for (old_args, args) |a, *o| o.* = try self.available(a);
        const regions = try self.gpa.alloc(RegionId, old_regions.len);
        defer self.gpa.free(regions);
        if (old_regions.len > 0) {
            // What the regions read from outside is built here, where the
            // original's owner read it, not inside one of the copies.
            var free: std.ArrayList(Ref) = .empty;
            defer free.deinit(self.gpa);
            try self.freeRefs(old_regions, &free);
            for (free.items) |f| _ = try self.available(f);
            // A join is created before an arm that jumps to it, so copying in
            // id order creates every join before its jumps.
            const order = try self.gpa.alloc(usize, old_regions.len);
            defer self.gpa.free(order);
            for (order, 0..) |*o, i| o.* = i;
            std.mem.sort(usize, order, old_regions, struct {
                fn lt(rs: []const RegionId, a: usize, b: usize) bool {
                    return rs[a].index() < rs[b].index();
                }
            }.lt);
            for (order) |i| {
                const old = old_regions[i];
                const kind = self.store.region(old).kind;
                const params = try self.gpa.dupe(TyId, self.store.tySlice(self.store.region(old).params));
                defer self.gpa.free(params);
                regions[i] = switch (kind) {
                    .arm => try self.openArmAt(args[0], aux, @intCast(i)),
                    .operand => try self.openOperand(args[0..1], nd.op),
                    .join, .loop_body, .lambda_body => try self.openRegion(kind, params),
                    .row_body => unreachable, // row_body regions are never owned by a node
                };
                if (kind == .loop_body and nd.op == .for_list) try self.noteListLoop(regions[i], args[0]);
                if (kind == .loop_body and nd.op == .for_range) try self.noteRangeLoop(regions[i], args[0], args[1], nd.payload == 1);
                self.region_copy.items[old.index()] = regions[i];
                try self.fillFrom(old);
            }
        }
        const out = try self.make(.{ .op = nd.op, .payload = nd.payload, .args = args, .tys = tys, .regions = regions, .aux = aux });
        self.copy_of.items[n.index()] = out;
        return out;
    }

    /// Close the current region with a copy of region `old`'s end, copying
    /// what the end reads.
    fn fillFrom(self: *Builder, old: RegionId) Allocator.Error!void {
        const end = self.store.region(old).end;
        const old_refs = try self.gpa.dupe(Ref, self.store.refSlice(end.refs));
        defer self.gpa.free(old_refs);
        const refs = try self.gpa.alloc(Ref, old_refs.len);
        defer self.gpa.free(refs);
        for (old_refs, refs) |a, *o| o.* = try self.available(a);
        const spec: EndSpec = switch (end.kind) {
            .open => unreachable, // copyEnd copies closed regions, whose end is never open
            .value => .{ .value = refs },
            .jump => .{ .jump = .{ .join = self.joinCopy(RegionId.of(end.target)), .args = refs } },
            .return_ => .{ .return_ = refs[0] },
            .branch => .{ .branch = (try self.available(Ref.of(NodeId.of(end.target)))).nodeId() },
            .continue_ => .{ .continue_ = refs },
            .break_ => .{ .break_ = refs },
        };
        try self.close(spec);
    }

    // A jump names the copy of its join when the join's switch is being
    // copied around it, and the join itself otherwise.
    fn joinCopy(self: *const Builder, join: RegionId) RegionId {
        const c = self.region_copy.items[join.index()];
        if (c != RegionId.none and self.store.encloses(self.store.region(c).parent, self.current())) return c;
        return join;
    }

    fn inRegions(self: *const Builder, regions: []const RegionId, n: NodeId) bool {
        const at = self.store.nodes.items(.region)[n.index()];
        for (regions) |r| if (self.store.encloses(r, at)) return true;
        return false;
    }

    /// The refs that the live nodes and the ends of `regions` read from
    /// outside them, in increasing node id order. A live node is one an end
    /// reaches.
    fn freeRefs(self: *Builder, regions: []const RegionId, out: *std.ArrayList(Ref)) Allocator.Error!void {
        var seen: collections.DenseMapUnmanaged(NodeId, void) = .empty;
        defer seen.deinit(self.gpa);
        var stack: std.ArrayList(Ref) = .empty;
        defer stack.deinit(self.gpa);
        for (regions) |r| try self.pushEnd(&stack, r);
        while (stack.pop()) |ref| switch (ref.kind) {
            .row_param, .region_param, .input => {},
            .node => {
                const n = ref.nodeId();
                if (!self.inRegions(regions, n)) {
                    for (out.items) |o| {
                        if (o == ref) break;
                    } else try out.append(self.gpa, ref);
                    continue;
                }
                if ((try seen.getOrPut(self.gpa, n)).found_existing) continue;
                const nd = self.store.node(n);
                try stack.appendSlice(self.gpa, self.store.refSlice(nd.args));
                for (self.store.regionSlice(nd.regions)) |sub| try self.pushEnd(&stack, sub);
            },
        };
        std.mem.sort(Ref, out.items, {}, struct {
            fn lt(_: void, a: Ref, b: Ref) bool {
                return a.target < b.target or (a.target == b.target and a.output < b.output);
            }
        }.lt);
    }

    /// Whether dropping or repeating `ref` drops or repeats no failure: the
    /// node and every live node it reads, through its operands and through
    /// the ends of the regions it owns, are speculatable (normal-form 1.1).
    /// A node's own flag covers only the node, so `Field` of a loop output is
    /// flagged speculatable although the loop it reads is not.
    fn coneSpeculatable(self: *Builder, ref: Ref) Allocator.Error!bool {
        var seen: collections.DenseMapUnmanaged(NodeId, void) = .empty;
        defer seen.deinit(self.gpa);
        var stack: std.ArrayList(Ref) = .empty;
        defer stack.deinit(self.gpa);
        try stack.append(self.gpa, ref);
        while (stack.pop()) |r| switch (r.kind) {
            .row_param, .region_param, .input => {},
            .node => {
                const n = r.nodeId();
                if ((try seen.getOrPut(self.gpa, n)).found_existing) continue;
                const nd = self.store.node(n);
                if (!nd.flags.speculatable) return false;
                try stack.appendSlice(self.gpa, self.store.refSlice(nd.args));
                for (self.store.regionSlice(nd.regions)) |sub| try self.pushEnd(&stack, sub);
            },
        };
        return true;
    }

    fn pushEnd(self: *Builder, stack: *std.ArrayList(Ref), r: RegionId) Allocator.Error!void {
        const end = self.store.region(r).end;
        try stack.appendSlice(self.gpa, self.store.refSlice(end.refs));
        if (end.kind == .branch) try stack.append(self.gpa, Ref.of(NodeId.of(end.target)));
    }

    // Whether everything region `r` reads from outside itself is visible
    // here, or is a constant that `available` builds again here.
    fn movable(self: *Builder, r: RegionId) Allocator.Error!bool {
        var free: std.ArrayList(Ref) = .empty;
        defer free.deinit(self.gpa);
        try self.freeRefs(&.{r}, &free);
        for (free.items) |f| if (!self.visible(f) and !self.isConstant(f)) return false;
        return true;
    }

    // A node that reads nothing and computes nothing, such as a literal. A
    // copy of it repeats no work, and its place is not meaning: the rebuild
    // places it late and the number stage hoists it (N5d, N5b).
    fn isConstant(self: *const Builder, ref: Ref) bool {
        const n = self.nodeOf(ref) orelse return false;
        return opSpeculatable(n.op) == .always and n.args.len == 0 and n.regions.len == 0;
    }
};

const testing = std.testing;

test "an integer literal reads by its type's signedness" {
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    const all_ones: u128 = std.math.maxInt(u128);
    try testing.expectEqual(@as(?i256, -1), Builder.litIntValue(&types, .{ .ty = try types.intTy(.i128), .value = .{ .int = all_ones } }));
    try testing.expectEqual(@as(?i256, all_ones), Builder.litIntValue(&types, .{ .ty = try types.intTy(.u128), .value = .{ .int = all_ones } }));
    try testing.expectEqual(@as(?i256, null), Builder.litIntValue(&types, .{ .ty = try types.boolTy(), .value = .{ .bool_ = true } }));
}

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
};

fn ruleIndex(step: []const u8, root: Op) usize {
    for (table.rules, 0..) |r, i| {
        if (std.mem.eql(u8, r.step, step) and r.root == root) return i;
    }
    unreachable; // every caller names a step and root present in the table
}

test "an if written twice is one node, and one with another arm is not" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    _ = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const x = Ref.rowParam(0);
    const y = Ref.rowParam(1);
    const c = try f.b.call(.i64, .is_lt, &.{ x, y });
    var ifs: [3]Ref = undefined;
    for (&ifs, [_]i128{ 1, 1, 2 }) |*v, k| {
        const arm0 = try f.b.openArm(c, 0);
        try f.b.close(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ x, try f.b.litInt(i64_ty, k) })} });
        const arm1 = try f.b.openArm(c, 1);
        try f.b.close(.{ .value = &.{y} });
        v.* = try f.b.switchOn(c, &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{});
    }
    try testing.expectEqual(ifs[0], ifs[1]);
    try testing.expect(ifs[0] != ifs[2]);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus_wrap, &.{ ifs[1], ifs[2] })} });
}

test "matching a literal switch builds no node, so a key literal read in one arm stays there" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    _ = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const x = Ref.rowParam(0);
    const keys = [_]u32{(try f.b.internLit(i64_ty, .{ .int = 13 })).index()};
    const keyed = try f.b.openLitArm(x, &keys, 0);
    try f.b.close(.{ .value = &.{Ref.rowParam(1)} });
    const default = try f.b.openLitArm(x, &keys, 1);
    try f.b.close(.{ .value = &.{x} });
    const before = f.store.nodeCount();
    const sw = try f.b.switchOn(x, &.{ keyed, default }, &.{}, &.{i64_ty}, &.{keys[0]});
    try testing.expectEqual(before + 1, f.store.nodeCount());
    try f.b.endRow(.{ .value = &.{sw} });
}

test "N13h: not of not is the operand, and the knockout stops it" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const bool_ty = try f.types.boolTy();
    _ = try f.b.beginRow(&.{bool_ty}, bool_ty);
    const x = Ref.rowParam(0);
    const once = try f.b.call(.bool_, .not, &.{x});
    try testing.expectEqual(x, try f.b.call(.bool_, .not, &.{once}));

    f.b.hooks.knocked_out[ruleIndex("N13h", .prim)] = true;
    const twice = try f.b.call(.bool_, .not, &.{once});
    try testing.expect(twice != x);
    try f.b.endRow(.{ .value = &.{twice} });
}

test "N13j: a builtin over literals is its value, unless it fails there, and the knockout stops it" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const bool_ty = try f.types.boolTy();
    const i64_ty = try f.types.intTy(.i64);
    const u8_ty = try f.types.intTy(.u8);
    const u128_ty = try f.types.intTy(.u128);
    _ = try f.b.beginRow(&.{}, bool_ty);
    try testing.expectEqual(try f.b.litInt(i64_ty, 3), try f.b.call(.i64, .plus, &.{ try f.b.litInt(i64_ty, 1), try f.b.litInt(i64_ty, 2) }));
    try testing.expectEqual(try f.b.litBool(true), try f.b.call(.i64, .is_lt, &.{ try f.b.litInt(i64_ty, -1), try f.b.litInt(i64_ty, 0) }));
    try testing.expectEqual(try f.b.litBool(false), try f.b.call(.bool_, .not, &.{try f.b.litBool(true)}));
    // A result above the highest `I128` keeps its `U128` bits.
    const top = try f.b.litRef(u128_ty, .{ .int = std.math.maxInt(u128) });
    try testing.expectEqual(top, try f.b.call(.u128, .plus_wrap, &.{ top, try f.b.litRef(u128_ty, .{ .int = 0 }) }));
    // Checked arithmetic that fails at the literals stays a call (C2 keeps the crash).
    const overflow = try f.b.call(.u8, .plus, &.{ try f.b.litInt(u8_ty, 255), try f.b.litInt(u8_ty, 1) });
    try testing.expect(f.store.node(overflow.nodeId()).op == .prim);
    const by_zero = try f.b.call(.i64, .div_trunc, &.{ try f.b.litInt(i64_ty, 1), try f.b.litInt(i64_ty, 0) });
    try testing.expect(f.store.node(by_zero.nodeId()).op == .prim);

    f.b.hooks.knocked_out[ruleIndexArgs("N13j", .prim, 1)] = true;
    const kept = try f.b.call(.i64, .is_eq, &.{ try f.b.litInt(i64_ty, 1), try f.b.litInt(i64_ty, 2) });
    try testing.expect(f.store.node(kept.nodeId()).op == .prim);
    try f.b.endRow(.{ .value = &.{kept} });
}

test "N13q flips a negated integer comparison and leaves floats alone" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const f64_ty = try f.types.floatTy(.f64);
    const bool_ty = try f.types.boolTy();
    _ = try f.b.beginRow(&.{ i64_ty, i64_ty, f64_ty, f64_ty }, bool_ty);
    const a = Ref.rowParam(0);
    const b = Ref.rowParam(1);
    const lt = try f.b.call(.i64, .is_lt, &.{ a, b });
    const flipped = try f.b.call(.bool_, .not, &.{lt});
    try testing.expectEqual(try f.b.call(.i64, .is_lte, &.{ b, a }), flipped);

    const flt = try f.b.call(.f64, .is_lt, &.{ Ref.rowParam(2), Ref.rowParam(3) });
    const fnot = try f.b.call(.bool_, .not, &.{flt});
    try testing.expectEqual(ir.Op.prim, f.store.node(fnot.nodeId()).op);
    try testing.expectEqual(prims.Method.not, prims.get(ir.PrimId.of(f.store.node(fnot.nodeId()).payload)).method);
    try f.b.endRow(.{ .value = &.{fnot} });
}

test "N13a: a field of a record construction is the component" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const bool_ty = try f.types.boolTy();
    const rec_ty = try f.types.recordTy(&.{ .{ .name = "x", .ty = i64_ty }, .{ .name = "y", .ty = bool_ty } });
    _ = try f.b.beginRow(&.{ i64_ty, bool_ty }, bool_ty);
    const r = try f.b.record(rec_ty, &.{ Ref.rowParam(0), Ref.rowParam(1) });
    try testing.expectEqual(Ref.rowParam(1), try f.b.field(r, 1));
    try f.b.endRow(.{ .value = &.{Ref.rowParam(1)} });
}

test "rules-off mode builds the redex as written" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const bool_ty = try f.types.boolTy();
    _ = try f.b.beginRow(&.{bool_ty}, bool_ty);
    f.b.hooks.rules_off = true;
    const x = Ref.rowParam(0);
    const twice = try f.b.call(.bool_, .not, &.{try f.b.call(.bool_, .not, &.{x})});
    try testing.expect(twice != x);
    try f.b.endRow(.{ .value = &.{twice} });
}

test "hash-consing reuses a node from an enclosing region, not from a sibling" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const bool_ty = try f.types.boolTy();
    _ = try f.b.beginRow(&.{ bool_ty, i64_ty }, i64_ty);
    const c = Ref.rowParam(0);
    const x = Ref.rowParam(1);
    const outer = try f.b.call(.i64, .plus_wrap, &.{ x, x });

    const arm0 = try f.b.openArm(c, 0);
    _ = try f.b.openRegion(.operand, &.{});
    try testing.expectEqual(outer, try f.b.call(.i64, .plus_wrap, &.{ x, x }));
    const inner0 = try f.b.call(.i64, .times_wrap, &.{ x, x });
    try f.b.close(.{ .value = &.{try f.b.litBool(true)} });
    try f.b.close(.{ .value = &.{inner0} });

    const arm1 = try f.b.openArm(c, 1);
    const inner1 = try f.b.call(.i64, .times_wrap, &.{ x, x });
    try testing.expect(inner1 != inner0);
    try f.b.close(.{ .value = &.{inner1} });

    const sw = try f.b.switchOn(c, &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{});
    try f.b.endRow(.{ .value = &.{sw} });
}

test "an arm's fact is known inside it and forgotten after it" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const bool_ty = try f.types.boolTy();
    _ = try f.b.beginRow(&.{bool_ty}, bool_ty);
    const c = Ref.rowParam(0);
    _ = try f.b.openArm(c, 1);
    try testing.expectEqual(@as(?u32, 1), f.b.knownKey(c));
    try f.b.close(.{ .value = &.{c} });
    try testing.expectEqual(@as(?u32, null), f.b.knownKey(c));
    try f.b.endRow(.{ .value = &.{c} });
}

test "N13d: a Bool or tag switch that a dominating arm or an earlier And operand decided is that arm" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const bool_ty = try f.types.boolTy();
    const i64_ty = try f.types.intTy(.i64);
    const union_ty = try f.types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{i64_ty} }, .{ .name = "B", .payload = &.{} } });
    _ = try f.b.beginRow(&.{ bool_ty, i64_ty, i64_ty, bool_ty, bool_ty, union_ty }, i64_ty);
    const p = Ref.rowParam;
    // In the True arm of a switch on c, a switch on c is its True arm.
    const Inner = struct {
        fn on(b: *Builder, scrutinee: Ref, values: [2]Ref, ty: TyId) Allocator.Error!Ref {
            var arms: [2]RegionId = undefined;
            for (&arms, values, 0..) |*a, v, key| {
                a.* = try b.openArmAt(scrutinee, &.{}, @intCast(key));
                try b.close(.{ .value = &.{v} });
            }
            return b.switchOn(scrutinee, &arms, &.{}, &.{ty}, &.{});
        }
    };
    _ = try f.b.openArm(p(0), 1);
    try testing.expectEqual(p(1), try Inner.on(&f.b, p(0), .{ p(2), p(1) }, i64_ty));
    try f.b.close(.{ .value = &.{p(1)} });
    // In an And operand after c, c is True.
    _ = try f.b.openOperand(&.{p(0)}, .and_);
    try testing.expectEqual(p(4), try Inner.on(&f.b, p(0), .{ p(3), p(4) }, bool_ty));
    try f.b.close(.{ .value = &.{p(4)} });
    // In tag B's arm of a switch on u, a switch on u is its B arm.
    _ = try f.b.openTagArm(p(5), try f.types.name("B"));
    try testing.expectEqual(p(2), try Inner.on(&f.b, p(5), .{ p(1), p(2) }, i64_ty));
    try f.b.close(.{ .value = &.{p(2)} });
    // Outside the arms nothing is decided.
    const free = try Inner.on(&f.b, p(0), .{ p(2), p(1) }, i64_ty);
    try testing.expect(free.kind == .node);
    try f.b.endRow(.{ .value = &.{free} });
}

test "N13d on operands: an And or Or operand an earlier operand or a dominating arm decided is removed" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const bool_ty = try f.types.boolTy();
    _ = try f.b.beginRow(&.{ bool_ty, bool_ty }, bool_ty);
    const c = Ref.rowParam(0);
    const d = Ref.rowParam(1);
    try testing.expectEqual(c, try connectiveOf(&f, .and_, c, &.{c}));
    try testing.expectEqual(c, try connectiveOf(&f, .or_, c, &.{c}));
    const cd = try connectiveOf(&f, .and_, c, &.{d});
    var cmp: equal.Comparison = .{ .gpa = testing.allocator, .store = &f.store };
    defer cmp.deinit();
    try testing.expect(try cmp.values(cd, try connectiveOf(&f, .and_, c, &.{ d, c })));
    // In the True arm of a switch on c, c goes from an And, and an And of c alone is True.
    _ = try f.b.openArm(c, 1);
    try testing.expectEqual(d, try connectiveOf(&f, .and_, c, &.{d}));
    try testing.expectEqual(d, try connectiveOf(&f, .and_, d, &.{c}));
    try testing.expectEqual(try f.b.litBool(true), try connectiveOf(&f, .and_, c, &.{c}));
    try f.b.close(.{ .value = &.{d} });
    // In its False arm, c goes from an Or.
    _ = try f.b.openArm(c, 0);
    try testing.expectEqual(d, try connectiveOf(&f, .or_, c, &.{d}));
    try f.b.close(.{ .value = &.{d} });
    try f.b.endRow(.{ .value = &.{cd} });
}

fn switchRuleIndex(step: []const u8, first_arm: table.Arm) usize {
    for (table.rules, 0..) |r, i| {
        if (!std.mem.eql(u8, r.step, step) or r.root != .switch_) continue;
        const arm = r.args[0].bool_switch.arms[0];
        if (std.meta.eql(arm, first_arm)) return i;
    }
    unreachable; // every caller names a switch rule present in the table
}

test "N13i: a switch on a negation swaps its arms, and knocking out N13i and N13s, which covers it, stops it" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const bool_ty = try f.types.boolTy();
    const i64_ty = try f.types.intTy(.i64);
    _ = try f.b.beginRow(&.{ bool_ty, i64_ty, i64_ty }, i64_ty);
    const c = Ref.rowParam(0);
    const nc = try f.b.call(.bool_, .not, &.{c});
    const a0 = try f.b.openArm(nc, 0);
    try f.b.close(.{ .value = &.{Ref.rowParam(1)} });
    const a1 = try f.b.openArm(nc, 1);
    try f.b.close(.{ .value = &.{Ref.rowParam(2)} });
    const sw = f.store.node((try f.b.switchOn(nc, &.{ a0, a1 }, &.{}, &.{i64_ty}, &.{})).nodeId());
    try testing.expectEqual(c, f.store.refSlice(sw.args)[0]);
    try testing.expectEqualSlices(RegionId, &.{ a1, a0 }, f.store.regionSlice(sw.regions));

    f.b.hooks.knocked_out[switchRuleIndex("N13i", .{ .region = 0 })] = true;
    f.b.hooks.knocked_out[ruleIndex("N13s", .switch_)] = true;
    const b0 = try f.b.openArm(nc, 0);
    try f.b.close(.{ .value = &.{Ref.rowParam(1)} });
    const b1 = try f.b.openArm(nc, 1);
    try f.b.close(.{ .value = &.{Ref.rowParam(2)} });
    const kept = f.store.node((try f.b.switchOn(nc, &.{ b0, b1 }, &.{}, &.{i64_ty}, &.{})).nodeId());
    try testing.expectEqual(nc, f.store.refSlice(kept.args)[0]);
    try f.b.endRow(.{ .value = &.{Ref.rowParam(1)} });
}

test "the critical pair of N13q and N13i: a switch on the negation of an integer comparison is one switch by either rule, and each knockout stops its rule" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    _ = try f.b.beginRow(&.{ i64_ty, i64_ty, i64_ty, i64_ty }, i64_ty);
    const a = Ref.rowParam(0);
    const b = Ref.rowParam(1);
    const lt = try f.b.call(.i64, .is_lt, &.{ a, b });
    // The negation as written: N13i takes the switch.
    f.b.hooks.rules_off = true;
    const negated = try f.b.call(.bool_, .not, &.{lt});
    f.b.hooks.rules_off = false;
    // The negation rewritten first: N13q takes the prim, then the switch.
    const lte = try f.b.call(.bool_, .not, &.{lt});
    try testing.expectEqual(try f.b.call(.i64, .is_lte, &.{ b, a }), lte);
    const Arms = struct {
        fn on(fx: *Fixture, scrutinee: Ref, ty: TyId) !Ref {
            const a0 = try fx.b.openArm(scrutinee, 0);
            try fx.b.close(.{ .value = &.{Ref.rowParam(2)} });
            const a1 = try fx.b.openArm(scrutinee, 1);
            try fx.b.close(.{ .value = &.{Ref.rowParam(3)} });
            return fx.b.switchOn(scrutinee, &.{ a0, a1 }, &.{}, &.{ty}, &.{});
        }
    };
    const by_i = try Arms.on(&f, negated, i64_ty);
    const by_q = try Arms.on(&f, lte, i64_ty);
    for ([_]Ref{ by_i, by_q }) |sw| {
        const n = f.store.node(sw.nodeId());
        try testing.expectEqual(lt, f.store.refSlice(n.args)[0]);
        try testing.expectEqual(Ref.rowParam(3), armOf(&f.b, sw, 0));
        try testing.expectEqual(Ref.rowParam(2), armOf(&f.b, sw, 1));
    }
    var cmp: equal.Comparison = .{ .gpa = testing.allocator, .store = &f.store };
    defer cmp.deinit();
    try testing.expect(try cmp.values(by_i, by_q));

    // With N13i and N13s knocked out the switch on the negation stays; with
    // the switch half of N13q knocked out the switch on `is_lte` stays.
    f.b.hooks.knocked_out[switchRuleIndex("N13i", .{ .region = 0 })] = true;
    f.b.hooks.knocked_out[ruleIndex("N13s", .switch_)] = true;
    const kept_negated = try Arms.on(&f, negated, i64_ty);
    try testing.expectEqual(negated, f.store.refSlice(f.store.node(kept_negated.nodeId()).args)[0]);
    f.b.hooks.knocked_out[ruleIndex("N13q", .switch_)] = true;
    const kept_lte = try Arms.on(&f, lte, i64_ty);
    try testing.expectEqual(lte, f.store.refSlice(f.store.node(kept_lte.nodeId()).args)[0]);
    try f.b.endRow(.{ .value = &.{by_i} });
}

test "N13c and N13g: a switch on a known tag is that tag's arm, one on any union with equal arms is the arm, and the knockouts stop them" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const u_ty = try f.types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{i64_ty} }, .{ .name = "B", .payload = &.{} } });
    _ = try f.b.beginRow(&.{ u_ty, i64_ty, i64_ty }, i64_ty);
    const b_tag = try f.b.tag(u_ty, try f.types.name("B"), &.{});
    const u = Ref.rowParam(0);
    const Case = struct { scrutinee: Ref, arms: [2]Ref, want: Ref, step: []const u8 };
    const cases = [_]Case{
        .{ .scrutinee = b_tag, .arms = .{ Ref.rowParam(1), Ref.rowParam(2) }, .want = Ref.rowParam(2), .step = "N13c" },
        .{ .scrutinee = u, .arms = .{ Ref.rowParam(1), Ref.rowParam(1) }, .want = Ref.rowParam(1), .step = "N13g" },
    };
    for (cases) |c| {
        for ([_]bool{ false, true }) |knocked| {
            f.b.hooks.knocked_out[ruleIndex(c.step, .switch_)] = knocked;
            var arms: [2]RegionId = undefined;
            for (&arms, c.arms, 0..) |*arm, v, key| {
                arm.* = try f.b.openArmAt(c.scrutinee, &.{}, @intCast(key));
                try f.b.close(.{ .value = &.{v} });
            }
            const out = try f.b.switchOn(c.scrutinee, &arms, &.{}, &.{i64_ty}, &.{});
            if (knocked) try testing.expect(out != c.want) else try testing.expectEqual(c.want, out);
        }
        f.b.hooks.knocked_out[ruleIndex(c.step, .switch_)] = false;
    }
    try f.b.endRow(.{ .value = &.{Ref.rowParam(1)} });
}

test "T4.1: a Wrap of an Unwrap is the unwrapped value only when both are one nominal" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const n_ty = try f.types.nominalTy("N", i64_ty);
    const m_ty = try f.types.nominalTy("M", i64_ty);
    _ = try f.b.beginRow(&.{n_ty}, n_ty);
    const x = Ref.rowParam(0);
    const inner = try f.b.unwrap(x);
    try testing.expectEqual(x, try f.b.wrap(n_ty, inner));
    try testing.expect(try f.b.wrap(m_ty, inner) != x);
    try f.b.endRow(.{ .value = &.{x} });
}

test "N13o: a switch whose False arm is False is an And over its True arm" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const bool_ty = try f.types.boolTy();
    _ = try f.b.beginRow(&.{ bool_ty, bool_ty }, bool_ty);
    const c = Ref.rowParam(0);
    const a0 = try f.b.openArm(c, 0);
    try f.b.close(.{ .value = &.{try f.b.litBool(false)} });
    const a1 = try f.b.openArm(c, 1);
    try f.b.close(.{ .value = &.{Ref.rowParam(1)} });
    const out = try f.b.switchOn(c, &.{ a0, a1 }, &.{}, &.{bool_ty}, &.{});
    const n = f.store.node(out.nodeId());
    try testing.expectEqual(Op.and_, n.op);
    try testing.expectEqualSlices(RegionId, &.{a1}, f.store.regionSlice(n.regions));
    try testing.expectEqual(ir.RegionKind.operand, f.store.region(a1).kind);
    try f.b.endRow(.{ .value = &.{out} });

    var report = try @import("verify.zig").verifyAll(testing.allocator, &f.store, &f.types);
    defer report.deinit();
    for (report.messages.items) |m| std.debug.print("{s}\n", .{m});
    try testing.expect(report.ok());
}

test "N13e: a switch on a Bool whose arms are False and True is its scrutinee" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const bool_ty = try f.types.boolTy();
    _ = try f.b.beginRow(&.{bool_ty}, bool_ty);
    const c = Ref.rowParam(0);
    const a0 = try f.b.openArm(c, 0);
    try f.b.close(.{ .value = &.{try f.b.litBool(false)} });
    const a1 = try f.b.openArm(c, 1);
    try f.b.close(.{ .value = &.{try f.b.litBool(true)} });
    const out = try f.b.make(.{ .op = .switch_, .payload = 2, .args = &.{c}, .tys = &.{bool_ty}, .regions = &.{ a0, a1 } });
    try testing.expectEqual(c, out);
    try f.b.endRow(.{ .value = &.{out} });
}

fn verifyOk(f: *Fixture) (Allocator.Error || error{TestUnexpectedResult})!void {
    var report = try @import("verify.zig").verifyAll(testing.allocator, &f.store, &f.types);
    defer report.deinit();
    for (report.messages.items) |m| std.debug.print("{s}\n", .{m});
    try testing.expect(report.ok());
}

test "N13p: And(True, b) is b, with b's nodes built where the And was" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const bool_ty = try f.types.boolTy();
    const i64_ty = try f.types.intTy(.i64);
    const row = try f.b.beginRow(&.{ i64_ty, i64_ty }, bool_ty);
    const t = try f.b.litBool(true);
    const operand = try f.b.openOperand(&.{t}, .and_);
    const lt = try f.b.call(.i64, .is_lt, &.{ Ref.rowParam(0), try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(1), Ref.rowParam(1) }) });
    try f.b.close(.{ .value = &.{lt} });
    const out = try f.b.andOf(t, &.{operand});
    const n = f.store.node(out.nodeId());
    try testing.expectEqual(prims.Method.is_lt, prims.get(ir.PrimId.of(n.payload)).method);
    try testing.expectEqual(f.store.row(row).body, n.region);
    try f.b.endRow(.{ .value = &.{out} });
    try verifyOk(&f);

    f.b.hooks.knocked_out[ruleIndexResult("N13p", .and_)] = true;
    _ = try f.b.beginRow(&.{bool_ty}, bool_ty);
    const operand2 = try f.b.openOperand(&.{t}, .and_);
    try f.b.close(.{ .value = &.{Ref.rowParam(0)} });
    const kept = try f.b.andOf(try f.b.litBool(true), &.{operand2});
    try testing.expectEqual(Op.and_, f.store.node(kept.nodeId()).op);
    try f.b.endRow(.{ .value = &.{kept} });
}

fn ruleIndexResult(step: []const u8, result: std.meta.Tag(table.Tmpl)) usize {
    for (table.rules, 0..) |r, i| {
        if (std.mem.eql(u8, r.step, step) and r.result == result) return i;
    }
    unreachable; // every caller names a result kind present in the table
}

// `if a { if b { x + 1 } else { y * 2 } } else { y * 2 }`, each arm computing
// its own nodes. `x_reads_t` makes the inner True arm read a node of the
// outer True arm.
fn buildNested(f: *Fixture, x_reads_t: bool) Allocator.Error!struct { row: RowId, out: Ref } {
    const bool_ty = try f.types.boolTy();
    const i64_ty = try f.types.intTy(.i64);
    const row = try f.b.beginRow(&.{ bool_ty, i64_ty, i64_ty, i64_ty }, i64_ty);
    const a = try f.b.call(.i64, .is_lt, &.{ Ref.rowParam(1), Ref.rowParam(3) });
    const y_arm = try f.b.openArm(a, 0);
    try f.b.close(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(2), try f.b.litInt(i64_ty, 2) })} });
    const t_arm = try f.b.openArm(a, 1);
    const shared = try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(1), Ref.rowParam(3) });
    const b = try f.b.call(.i64, .is_lt, &.{ shared, Ref.rowParam(2) });
    const y2 = try f.b.openArm(b, 0);
    try f.b.close(.{ .value = &.{try f.b.call(.i64, .times_wrap, &.{ Ref.rowParam(2), try f.b.litInt(i64_ty, 2) })} });
    const x_arm = try f.b.openArm(b, 1);
    const base = if (x_reads_t) shared else Ref.rowParam(1);
    // Another builtin than `shared`'s, so N15a does not flatten the read away.
    try f.b.close(.{ .value = &.{try f.b.call(.i64, .bitwise_xor, &.{ base, try f.b.litInt(i64_ty, 1) })} });
    const inner = try f.b.switchOn(b, &.{ y2, x_arm }, &.{}, &.{i64_ty}, &.{});
    try f.b.close(.{ .value = &.{inner} });
    const out = try f.b.switchOn(a, &.{ y_arm, t_arm }, &.{}, &.{i64_ty}, &.{});
    try f.b.endRow(.{ .value = &.{out} });
    return .{ .row = row, .out = out };
}

test "N7d: nested ifs sharing the else arm become one switch on And, and compute what they did" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const merged = try buildNested(&f, false);
    const sw = f.store.node(merged.out.nodeId());
    try testing.expectEqual(Op.switch_, sw.op);
    try testing.expectEqual(Op.and_, f.store.node(f.store.refSlice(sw.args)[0].nodeId()).op);
    try verifyOk(&f);

    var g: Fixture = undefined;
    g.init();
    defer g.deinit();
    g.b.hooks.rules_off = true;
    const nested = try buildNested(&g, false);

    const eval = @import("eval.zig");
    var e1 = try eval.Evaluator.init(arena.allocator(), &f.store, &f.types, .strict);
    var e2 = try eval.Evaluator.init(arena.allocator(), &g.store, &g.types, .strict);
    for ([_]i256{ -3, 0, 4 }) |x| for ([_]i256{ -1, 2 }) |y| for ([_]i256{ -2, 5 }) |z| {
        const args = [_]eval.Value{ .{ .bool_ = false }, .{ .int = x }, .{ .int = y }, .{ .int = z } };
        try testing.expect((try e1.run(merged.row, &args)).eql(try e2.run(nested.row, &args)));
    };
}

test "N7d leaves the nesting when the inner arm reads what the outer arm computes" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const kept = try buildNested(&f, true);
    const sw = f.store.node(kept.out.nodeId());
    try testing.expectEqual(Op.switch_, sw.op);
    try testing.expectEqual(Op.prim, f.store.node(f.store.refSlice(sw.args)[0].nodeId()).op);
    try verifyOk(&f);
}

const ParamTy = enum { bool_, i64 };

fn tyOf(f: *Fixture, p: ParamTy) Allocator.Error!TyId {
    return switch (p) {
        .bool_ => f.types.boolTy(),
        .i64 => f.types.intTy(.i64),
    };
}

const Build = *const fn (f: *Fixture) Allocator.Error!Ref;

// Build one row with rules on, less `knocked`, and with rules off; the first
// dumps as `want`, and both compute one value on every input.
fn expectRewrite(params: []const ParamTy, result: ParamTy, build: Build, knocked: []const usize, want: []const u8) (@import("eval.zig").Error || std.Io.Writer.Error || error{ TestExpectedEqual, TestUnexpectedResult })!void {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    var g: Fixture = undefined;
    g.init();
    defer g.deinit();
    for (knocked) |k| f.b.hooks.knocked_out[k] = true;
    g.b.hooks.rules_off = true;
    var rows: [2]RowId = undefined;
    for ([_]*Fixture{ &f, &g }, &rows) |x, *row| {
        var tys: [6]TyId = undefined;
        for (params, tys[0..params.len]) |p, *t| t.* = try tyOf(x, p);
        row.* = try x.b.beginRow(tys[0..params.len], try tyOf(x, result));
        try x.b.endRow(.{ .value = &.{try build(x)} });
    }
    try verifyOk(&f);

    var out: std.Io.Writer.Allocating = .init(testing.allocator);
    defer out.deinit();
    try @import("dump.zig").dumpRow(&out.writer, &f.store, &f.types, rows[0]);
    try testing.expectEqualStrings(want, out.written());

    const eval = @import("eval.zig");
    var e1 = try eval.Evaluator.init(arena.allocator(), &f.store, &f.types, .strict);
    var e2 = try eval.Evaluator.init(arena.allocator(), &g.store, &g.types, .strict);
    var args: [6]eval.Value = undefined;
    var digits: [6]usize = @splat(0);
    while (true) {
        for (params, args[0..params.len], digits[0..params.len]) |p, *a, d| a.* = switch (p) {
            .bool_ => .{ .bool_ = d == 1 },
            .i64 => .{ .int = @as(i256, @intCast(d)) - 1 },
        };
        try testing.expect((try e1.run(rows[0], args[0..params.len])).eql(try e2.run(rows[1], args[0..params.len])));
        var i: usize = 0;
        while (i < params.len) : (i += 1) {
            digits[i] += 1;
            if (digits[i] < @as(usize, if (params[i] == .bool_) 2 else 3)) break;
            digits[i] = 0;
        }
        if (i == params.len) break;
    }
}

// `op(first, rest...)`, each later operand a region whose value is computed outside it.
fn connectiveOf(f: *Fixture, op: Op, first: Ref, rest: []const Ref) Allocator.Error!Ref {
    var regions: [4]RegionId = undefined;
    var earlier: [5]Ref = undefined;
    earlier[0] = first;
    for (rest, 0..) |r, i| {
        regions[i] = try f.b.openOperand(earlier[0 .. i + 1], op);
        try f.b.close(.{ .value = &.{r} });
        earlier[i + 1] = r;
    }
    return f.b.make(.{ .op = op, .args = &.{first}, .tys = &.{try f.types.boolTy()}, .regions = regions[0..rest.len] });
}

// `switch scrutinee { F: arm0, T: arm1 }` over values computed outside it.
fn switchOf(f: *Fixture, scrutinee: Ref, arm0: Ref, arm1: Ref, ty: TyId) Allocator.Error!Ref {
    const a0 = try f.b.openArm(scrutinee, 0);
    try f.b.close(.{ .value = &.{arm0} });
    const a1 = try f.b.openArm(scrutinee, 1);
    try f.b.close(.{ .value = &.{arm1} });
    return f.b.switchOn(scrutinee, &.{ a0, a1 }, &.{}, &.{ty}, &.{});
}

fn ruleIndexArgs(step: []const u8, root: Op, nth: usize) usize {
    var seen: usize = 0;
    for (table.rules, 0..) |r, i| {
        if (!std.mem.eql(u8, r.step, step) or r.root != root) continue;
        if (seen == nth) return i;
        seen += 1;
    }
    unreachable; // every caller names a step, root and nth that exist in the table
}

fn nestedAnd(f: *Fixture) Allocator.Error!Ref {
    const r = try f.b.openOperand(&.{Ref.rowParam(0)}, .and_);
    try f.b.close(.{ .value = &.{try connectiveOf(f, .and_, Ref.rowParam(1), &.{Ref.rowParam(2)})} });
    return f.b.andOf(Ref.rowParam(0), &.{r});
}

test "N15b: an And in an And's operand flattens into it, and the knockout stops it" {
    try expectRewrite(&.{ .bool_, .bool_, .bool_ }, .bool_, nestedAnd, &.{},
        \\row r0 (Bool, Bool, Bool) -> Bool
        \\  n1 = and(p0) : Bool
        \\    operand
        \\      value p1
        \\    operand
        \\      value p2
        \\  value n1
        \\
    );
    try expectRewrite(&.{ .bool_, .bool_, .bool_ }, .bool_, nestedAnd, &.{ruleIndex("N15b", .and_)},
        \\row r0 (Bool, Bool, Bool) -> Bool
        \\  n1 = and(p0) : Bool
        \\    operand
        \\      n0 = and(p1) : Bool
        \\        operand
        \\          value p2
        \\      value n0
        \\  value n1
        \\
    );
}

// `And(p0 < p1, { s = p1 + p2; And(s < p0, { p0 < s }) })`, and with
// `rest_reads_s` false `p0 < p2` for `p0 < s`: only the inner And's later
// operand decides whether it can leave the outer operand.
fn nestedAndOver(f: *Fixture, rest_reads_s: bool) Allocator.Error!Ref {
    const first = try f.b.call(.i64, .is_lt, &.{ Ref.rowParam(0), Ref.rowParam(1) });
    const r = try f.b.openOperand(&.{first}, .and_);
    const s = try f.b.call(.i64, .plus_wrap, &.{ Ref.rowParam(1), Ref.rowParam(2) });
    const inner_first = try f.b.call(.i64, .is_lt, &.{ s, Ref.rowParam(0) });
    const inner = try f.b.openOperand(&.{inner_first}, .and_);
    try f.b.close(.{ .value = &.{try f.b.call(.i64, .is_lt, &.{ Ref.rowParam(0), if (rest_reads_s) s else Ref.rowParam(2) })} });
    try f.b.close(.{ .value = &.{try f.b.andOf(inner_first, &.{inner})} });
    return f.b.andOf(first, &.{r});
}

fn nestedAndReadingOuter(f: *Fixture) Allocator.Error!Ref {
    return nestedAndOver(f, true);
}

fn nestedAndFirstReadingOuter(f: *Fixture) Allocator.Error!Ref {
    return nestedAndOver(f, false);
}

test "N15b leaves an inner And whose later operands read the enclosing operand's nodes, and flattens one whose first does" {
    try expectRewrite(&.{ .i64, .i64, .i64 }, .bool_, nestedAndFirstReadingOuter, &.{},
        \\row r0 (I64, I64, I64) -> Bool
        \\  n0 = Num.I64.is_lt(p0, p1) : Bool
        \\  n8 = and(n0) : Bool
        \\    operand
        \\      n5 = Num.I64.plus_wrap(p1, p2) : I64
        \\      n6 = Num.I64.is_lt(n5, p0) : Bool
        \\      value n6
        \\    operand
        \\      n7 = Num.I64.is_lt(p0, p2) : Bool
        \\      value n7
        \\  value n8
        \\
    );
    try expectRewrite(&.{ .i64, .i64, .i64 }, .bool_, nestedAndReadingOuter, &.{},
        \\row r0 (I64, I64, I64) -> Bool
        \\  n0 = Num.I64.is_lt(p0, p1) : Bool
        \\  n5 = and(n0) : Bool
        \\    operand
        \\      n1 = Num.I64.plus_wrap(p1, p2) : I64
        \\      n2 = Num.I64.is_lt(n1, p0) : Bool
        \\      n4 = and(n2) : Bool
        \\        operand
        \\          n3 = Num.I64.is_lt(p0, n1) : Bool
        \\          value n3
        \\      value n4
        \\  value n5
        \\
    );
}

// `And(p0, { And(p1 == 2, { p2 == 2 }) })`: the inner And's later operand
// reads the literal its first operand built in the outer operand region.
fn nestedAndSharingLiteral(f: *Fixture) Allocator.Error!Ref {
    const i64_ty = try f.types.intTy(.i64);
    const r = try f.b.openOperand(&.{Ref.rowParam(0)}, .and_);
    const two = try f.b.litInt(i64_ty, 2);
    const inner_first = try f.b.call(.i64, .is_eq, &.{ Ref.rowParam(1), two });
    const inner = try f.b.openOperand(&.{inner_first}, .and_);
    try f.b.close(.{ .value = &.{try f.b.call(.i64, .is_eq, &.{ Ref.rowParam(2), two })} });
    try f.b.close(.{ .value = &.{try f.b.andOf(inner_first, &.{inner})} });
    return f.b.andOf(Ref.rowParam(0), &.{r});
}

test "N15b flattens an inner And whose later operands read only a literal of the enclosing operand" {
    try expectRewrite(&.{ .bool_, .i64, .i64 }, .bool_, nestedAndSharingLiteral, &.{},
        \\row r0 (Bool, I64, I64) -> Bool
        \\  n8 = and(p0) : Bool
        \\    operand
        \\      n4 = 2 : I64
        \\      n5 = Num.I64.is_eq(p1, n4) : Bool
        \\      value n5
        \\    operand
        \\      n6 = 2 : I64
        \\      n7 = Num.I64.is_eq(p2, n6) : Bool
        \\      value n7
        \\  value n8
        \\
    );
}

fn andDropsTrue(f: *Fixture) Allocator.Error!Ref {
    return connectiveOf(f, .and_, Ref.rowParam(0), &.{ try f.b.litBool(true), Ref.rowParam(1) });
}

fn orDropsFalse(f: *Fixture) Allocator.Error!Ref {
    return connectiveOf(f, .or_, Ref.rowParam(0), &.{ try f.b.litBool(false), Ref.rowParam(1) });
}

fn andAbsorbsFalse(f: *Fixture) Allocator.Error!Ref {
    return connectiveOf(f, .and_, Ref.rowParam(0), &.{ try f.b.litBool(false), Ref.rowParam(1) });
}

fn orAbsorbsTrue(f: *Fixture) Allocator.Error!Ref {
    return connectiveOf(f, .or_, Ref.rowParam(0), &.{ Ref.rowParam(1), try f.b.litBool(true) });
}

test "N13p: an identity operand drops out of an And or an Or at any position" {
    try expectRewrite(&.{ .bool_, .bool_ }, .bool_, andDropsTrue, &.{},
        \\row r0 (Bool, Bool) -> Bool
        \\  n0 = True : Bool
        \\  n1 = and(p0) : Bool
        \\    operand
        \\      value p1
        \\  value n1
        \\
    );
    try expectRewrite(&.{ .bool_, .bool_ }, .bool_, orDropsFalse, &.{},
        \\row r0 (Bool, Bool) -> Bool
        \\  n0 = False : Bool
        \\  n1 = or(p0) : Bool
        \\    operand
        \\      value p1
        \\  value n1
        \\
    );
    try expectRewrite(&.{ .bool_, .bool_ }, .bool_, andDropsTrue, &.{ruleIndexResult("N13p", .and_)},
        \\row r0 (Bool, Bool) -> Bool
        \\  n0 = True : Bool
        \\  n1 = and(p0) : Bool
        \\    operand
        \\      value n0
        \\    operand
        \\      value p1
        \\  value n1
        \\
    );
}

test "N13p: an absorbing operand is the value of an And or an Or at any position" {
    try expectRewrite(&.{ .bool_, .bool_ }, .bool_, andAbsorbsFalse, &.{},
        \\row r0 (Bool, Bool) -> Bool
        \\  n0 = False : Bool
        \\  value n0
        \\
    );
    try expectRewrite(&.{ .bool_, .bool_ }, .bool_, orAbsorbsTrue, &.{},
        \\row r0 (Bool, Bool) -> Bool
        \\  n0 = True : Bool
        \\  value n0
        \\
    );
}

fn notOfAnd(f: *Fixture) Allocator.Error!Ref {
    return f.b.call(.bool_, .not, &.{try connectiveOf(f, .and_, Ref.rowParam(0), &.{Ref.rowParam(1)})});
}

fn notOfOr(f: *Fixture) Allocator.Error!Ref {
    return f.b.call(.bool_, .not, &.{try connectiveOf(f, .or_, Ref.rowParam(0), &.{Ref.rowParam(1)})});
}

fn notOfSwitch(f: *Fixture) Allocator.Error!Ref {
    return f.b.call(.bool_, .not, &.{try switchOf(f, Ref.rowParam(0), Ref.rowParam(1), Ref.rowParam(2), try f.types.boolTy())});
}

test "N13t: a negated And, Or, or Bool switch is its dual over negated operands or arms" {
    try expectRewrite(&.{ .bool_, .bool_ }, .bool_, notOfAnd, &.{},
        \\row r0 (Bool, Bool) -> Bool
        \\  n0 = and(p0) : Bool
        \\    operand
        \\      value p1
        \\  n1 = Bool.not(p0) : Bool
        \\  n3 = or(n1) : Bool
        \\    operand
        \\      n2 = Bool.not(p1) : Bool
        \\      value n2
        \\  value n3
        \\
    );
    try expectRewrite(&.{ .bool_, .bool_ }, .bool_, notOfOr, &.{},
        \\row r0 (Bool, Bool) -> Bool
        \\  n0 = or(p0) : Bool
        \\    operand
        \\      value p1
        \\  n1 = Bool.not(p0) : Bool
        \\  n3 = and(n1) : Bool
        \\    operand
        \\      n2 = Bool.not(p1) : Bool
        \\      value n2
        \\  value n3
        \\
    );
    try expectRewrite(&.{ .bool_, .bool_, .bool_ }, .bool_, notOfSwitch, &.{},
        \\row r0 (Bool, Bool, Bool) -> Bool
        \\  n0 = switch p0 : Bool
        \\    arm 0
        \\      value p1
        \\    arm 1
        \\      value p2
        \\  n3 = switch p0 : Bool
        \\    arm 0
        \\      n1 = Bool.not(p1) : Bool
        \\      value n1
        \\    arm 1
        \\      n2 = Bool.not(p2) : Bool
        \\      value n2
        \\  value n3
        \\
    );
    try expectRewrite(&.{ .bool_, .bool_ }, .bool_, notOfAnd, &.{ruleIndexArgs("N13t", .prim, 0)},
        \\row r0 (Bool, Bool) -> Bool
        \\  n0 = and(p0) : Bool
        \\    operand
        \\      value p1
        \\  n1 = Bool.not(n0) : Bool
        \\  value n1
        \\
    );
}

fn switchOnNegatedOr(f: *Fixture) Allocator.Error!Ref {
    const a = try f.b.call(.bool_, .not, &.{Ref.rowParam(0)});
    const b = try f.b.call(.bool_, .not, &.{Ref.rowParam(1)});
    return switchOf(f, try connectiveOf(f, .or_, a, &.{b}), Ref.rowParam(2), Ref.rowParam(3), try f.types.intTy(.i64));
}

fn switchOnMixedOr(f: *Fixture) Allocator.Error!Ref {
    const a = try f.b.call(.bool_, .not, &.{Ref.rowParam(0)});
    return switchOf(f, try connectiveOf(f, .or_, a, &.{Ref.rowParam(1)}), Ref.rowParam(2), Ref.rowParam(3), try f.types.intTy(.i64));
}

// `And(not p0, p1, p2 <= p3)`: one negated leaf and one plain, so the `is_lte` decides.
fn switchOnAndWithLte(f: *Fixture) Allocator.Error!Ref {
    const a = try f.b.call(.bool_, .not, &.{Ref.rowParam(0)});
    const lte = try f.b.call(.i64, .is_lte, &.{ Ref.rowParam(2), Ref.rowParam(3) });
    return switchOf(f, try connectiveOf(f, .and_, a, &.{ Ref.rowParam(1), lte }), Ref.rowParam(2), Ref.rowParam(3), try f.types.intTy(.i64));
}

fn switchOnNotOfAnd(f: *Fixture) Allocator.Error!Ref {
    const n = try f.b.call(.bool_, .not, &.{try connectiveOf(f, .and_, Ref.rowParam(0), &.{Ref.rowParam(1)})});
    return switchOf(f, n, Ref.rowParam(2), Ref.rowParam(3), try f.types.intTy(.i64));
}

test "N13s: a switch flips to the scrutinee whose negation has fewer negated leaves, then fewer is_lte leaves, and an Or ties to an And" {
    try expectRewrite(&.{ .bool_, .bool_, .i64, .i64 }, .i64, switchOnNegatedOr, &.{},
        \\row r0 (Bool, Bool, I64, I64) -> I64
        \\  n0 = Bool.not(p0) : Bool
        \\  n1 = Bool.not(p1) : Bool
        \\  n2 = or(n0) : Bool
        \\    operand
        \\      value n1
        \\  n3 = and(p0) : Bool
        \\    operand
        \\      value p1
        \\  n4 = switch n3 : I64
        \\    arm 0
        \\      value p3
        \\    arm 1
        \\      value p2
        \\  value n4
        \\
    );
    try expectRewrite(&.{ .bool_, .bool_, .i64, .i64 }, .i64, switchOnMixedOr, &.{},
        \\row r0 (Bool, Bool, I64, I64) -> I64
        \\  n0 = Bool.not(p0) : Bool
        \\  n1 = or(n0) : Bool
        \\    operand
        \\      value p1
        \\  n3 = and(p0) : Bool
        \\    operand
        \\      n2 = Bool.not(p1) : Bool
        \\      value n2
        \\  n4 = switch n3 : I64
        \\    arm 0
        \\      value p3
        \\    arm 1
        \\      value p2
        \\  value n4
        \\
    );
    try expectRewrite(&.{ .bool_, .bool_, .i64, .i64 }, .i64, switchOnAndWithLte, &.{},
        \\row r0 (Bool, Bool, I64, I64) -> I64
        \\  n0 = Bool.not(p0) : Bool
        \\  n1 = Num.I64.is_lte(p2, p3) : Bool
        \\  n2 = and(n0) : Bool
        \\    operand
        \\      value p1
        \\    operand
        \\      value n1
        \\  n5 = or(p0) : Bool
        \\    operand
        \\      n3 = Bool.not(p1) : Bool
        \\      value n3
        \\    operand
        \\      n4 = Num.I64.is_lt(p3, p2) : Bool
        \\      value n4
        \\  n6 = switch n5 : I64
        \\    arm 0
        \\      value p3
        \\    arm 1
        \\      value p2
        \\  value n6
        \\
    );
    try expectRewrite(&.{ .bool_, .bool_, .i64, .i64 }, .i64, switchOnNegatedOr, &.{ruleIndex("N13s", .switch_)},
        \\row r0 (Bool, Bool, I64, I64) -> I64
        \\  n0 = Bool.not(p0) : Bool
        \\  n1 = Bool.not(p1) : Bool
        \\  n2 = or(n0) : Bool
        \\    operand
        \\      value n1
        \\  n3 = switch n2 : I64
        \\    arm 0
        \\      value p2
        \\    arm 1
        \\      value p3
        \\  value n3
        \\
    );
}

test "N13s terminates on a negated And with N13t, N13q, and N13i knocked out" {
    try expectRewrite(&.{ .bool_, .bool_, .i64, .i64 }, .i64, switchOnNotOfAnd, &.{
        ruleIndexArgs("N13t", .prim, 0),
        ruleIndexArgs("N13t", .prim, 1),
        ruleIndexArgs("N13t", .prim, 2),
        ruleIndex("N13q", .switch_),
        ruleIndex("N13i", .switch_),
    },
        \\row r0 (Bool, Bool, I64, I64) -> I64
        \\  n0 = and(p0) : Bool
        \\    operand
        \\      value p1
        \\  n1 = Bool.not(n0) : Bool
        \\  n2 = switch n0 : I64
        \\    arm 0
        \\      value p3
        \\    arm 1
        \\      value p2
        \\  value n2
        \\
    );
}

// `if p0 { p1 or p2 } else { p2 }`.
fn switchOverOr(f: *Fixture) Allocator.Error!Ref {
    const t = try connectiveOf(f, .or_, Ref.rowParam(1), &.{Ref.rowParam(2)});
    return switchOf(f, Ref.rowParam(0), Ref.rowParam(2), t, try f.types.boolTy());
}

// `if p0 { p1 and p3 } else { p2 and p3 }`.
fn switchOverAnds(f: *Fixture) Allocator.Error!Ref {
    const e = try connectiveOf(f, .and_, Ref.rowParam(2), &.{Ref.rowParam(3)});
    const t = try connectiveOf(f, .and_, Ref.rowParam(1), &.{Ref.rowParam(3)});
    return switchOf(f, Ref.rowParam(0), e, t, try f.types.boolTy());
}

test "N7d: a switch whose arm is an Or or And ending in the other arm is a connective" {
    try expectRewrite(&.{ .bool_, .bool_, .bool_ }, .bool_, switchOverOr, &.{},
        \\row r0 (Bool, Bool, Bool) -> Bool
        \\  n0 = or(p1) : Bool
        \\    operand
        \\      value p2
        \\  n1 = and(p0) : Bool
        \\    operand
        \\      value p1
        \\  n2 = or(n1) : Bool
        \\    operand
        \\      value p2
        \\  value n2
        \\
    );
    try expectRewrite(&.{ .bool_, .bool_, .bool_, .bool_ }, .bool_, switchOverAnds, &.{},
        \\row r0 (Bool, Bool, Bool, Bool) -> Bool
        \\  n0 = and(p2) : Bool
        \\    operand
        \\      value p3
        \\  n1 = and(p1) : Bool
        \\    operand
        \\      value p3
        \\  n2 = switch p0 : Bool
        \\    arm 0
        \\      value p2
        \\    arm 1
        \\      value p1
        \\  n3 = and(n2) : Bool
        \\    operand
        \\      value p3
        \\  value n3
        \\
    );
}

// `if p0 { if p2 { p3 } else { p4 } } else { if p1 { p3 } else { p4 } }`, and
// with `mirror` the True arm's arms swapped.
fn mergeOf(f: *Fixture, mirror: bool) Allocator.Error!Ref {
    const i64_ty = try f.types.intTy(.i64);
    const a0 = try f.b.openArm(Ref.rowParam(0), 0);
    try f.b.close(.{ .value = &.{try switchOf(f, Ref.rowParam(1), Ref.rowParam(3), Ref.rowParam(4), i64_ty)} });
    const a1 = try f.b.openArm(Ref.rowParam(0), 1);
    const t = if (mirror)
        try switchOf(f, Ref.rowParam(2), Ref.rowParam(4), Ref.rowParam(3), i64_ty)
    else
        try switchOf(f, Ref.rowParam(2), Ref.rowParam(3), Ref.rowParam(4), i64_ty);
    try f.b.close(.{ .value = &.{t} });
    return f.b.switchOn(Ref.rowParam(0), &.{ a0, a1 }, &.{}, &.{i64_ty}, &.{});
}

fn merge(f: *Fixture) Allocator.Error!Ref {
    return mergeOf(f, false);
}

fn mirrorMerge(f: *Fixture) Allocator.Error!Ref {
    return mergeOf(f, true);
}

test "N7d: two switches on the arms of a switch over the same arms merge into one switch on a switch" {
    try expectRewrite(&.{ .bool_, .bool_, .bool_, .i64, .i64 }, .i64, merge, &.{},
        \\row r0 (Bool, Bool, Bool, I64, I64) -> I64
        \\  n2 = switch p0 : Bool
        \\    arm 0
        \\      value p1
        \\    arm 1
        \\      value p2
        \\  n3 = switch n2 : I64
        \\    arm 0
        \\      value p3
        \\    arm 1
        \\      value p4
        \\  value n3
        \\
    );
    try expectRewrite(&.{ .bool_, .bool_, .bool_, .i64, .i64 }, .i64, mirrorMerge, &.{},
        \\row r0 (Bool, Bool, Bool, I64, I64) -> I64
        \\  n3 = switch p0 : Bool
        \\    arm 0
        \\      n2 = Bool.not(p1) : Bool
        \\      value n2
        \\    arm 1
        \\      value p2
        \\  n6 = switch p0 : Bool
        \\    arm 0
        \\      n4 = Bool.not(p1) : Bool
        \\      value p1
        \\    arm 1
        \\      n5 = Bool.not(p2) : Bool
        \\      value n5
        \\  n7 = switch n6 : I64
        \\    arm 0
        \\      value p3
        \\    arm 1
        \\      value p4
        \\  value n7
        \\
    );
}

// The N15a row of `method` whose second argument pattern is `kind`: `prim`
// for the flattening row, `identity` or `absorbing` for the others.
fn n15aIndex(method: prims.Method, kind: std.meta.Tag(table.Pat)) usize {
    for (table.rules, 0..) |r, i| {
        if (!std.mem.eql(u8, r.step, "N15a") or r.root_prim.?.method != method) continue;
        if (r.args[1] == kind) return i;
    }
    unreachable; // the table holds an N15a row for every method and kind asked
}

test "N15a: a chain is one Prim over its operands in order, whatever its grouping, and the knockout stops it" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    _ = try f.b.beginRow(&.{ i64_ty, i64_ty, i64_ty, i64_ty }, i64_ty);
    const p = [_]Ref{ Ref.rowParam(0), Ref.rowParam(1), Ref.rowParam(2), Ref.rowParam(3) };
    // (a ^ b) ^ (c ^ d) and a ^ ((b ^ c) ^ d) are one node over a, b, c, d.
    const left = try f.b.call(.i64, .bitwise_xor, &.{ try f.b.call(.i64, .bitwise_xor, &.{ p[0], p[1] }), try f.b.call(.i64, .bitwise_xor, &.{ p[2], p[3] }) });
    const right = try f.b.call(.i64, .bitwise_xor, &.{ p[0], try f.b.call(.i64, .bitwise_xor, &.{ try f.b.call(.i64, .bitwise_xor, &.{ p[1], p[2] }), p[3] }) });
    try testing.expectEqual(left, right);
    try testing.expectEqualSlices(Ref, &p, f.store.refSlice(f.store.node(left.nodeId()).args));
    // A chain of another builtin stays an operand.
    const mixed = try f.b.call(.i64, .bitwise_xor, &.{ p[0], try f.b.call(.i64, .bitwise_and, &.{ p[1], p[2] }) });
    try testing.expectEqual(@as(usize, 2), f.store.refSlice(f.store.node(mixed.nodeId()).args).len);
    try f.b.endRow(.{ .value = &.{left} });
    try verifyOk(&f);

    var g: Fixture = undefined;
    g.init();
    defer g.deinit();
    g.b.hooks.knocked_out[n15aIndex(.bitwise_xor, .prim)] = true;
    const g_ty = try g.types.intTy(.i64);
    _ = try g.b.beginRow(&.{ g_ty, g_ty, g_ty }, g_ty);
    const nested = try g.b.call(.i64, .bitwise_xor, &.{ Ref.rowParam(0), try g.b.call(.i64, .bitwise_xor, &.{ Ref.rowParam(1), Ref.rowParam(2) }) });
    try testing.expectEqual(@as(usize, 2), g.store.refSlice(g.store.node(nested.nodeId()).args).len);
    try g.b.endRow(.{ .value = &.{nested} });
}

test "N15a: an identity drops out of a chain, a chain of one operand is it, and all ones is the identity of bitwise_and at its own type" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const u8_ty = try f.types.intTy(.u8);
    const i8_ty = try f.types.intTy(.i8);
    _ = try f.b.beginRow(&.{ u8_ty, u8_ty, i8_ty }, u8_ty);
    const x = Ref.rowParam(0);
    const y = Ref.rowParam(1);
    // 255 is all ones in `U8`, -1 in `I8`; 127 is neither.
    try testing.expectEqual(x, try f.b.call(.u8, .bitwise_and, &.{ x, try f.b.litInt(u8_ty, 255) }));
    try testing.expectEqual(Ref.rowParam(2), try f.b.call(.i8, .bitwise_and, &.{ try f.b.litInt(i8_ty, -1), Ref.rowParam(2) }));
    try testing.expect(try f.b.call(.u8, .bitwise_and, &.{ x, try f.b.litInt(u8_ty, 127) }) != x);
    // x + 0 + y is x + y.
    const chain = try f.b.call(.u8, .plus_wrap, &.{ x, try f.b.call(.u8, .plus_wrap, &.{ try f.b.litInt(u8_ty, 0), y }) });
    try testing.expectEqualSlices(Ref, &.{ x, y }, f.store.refSlice(f.store.node(chain.nodeId()).args));
    try f.b.endRow(.{ .value = &.{chain} });
    try verifyOk(&f);

    var g: Fixture = undefined;
    g.init();
    defer g.deinit();
    g.b.hooks.knocked_out[n15aIndex(.times_wrap, .identity)] = true;
    const g_ty = try g.types.intTy(.i64);
    _ = try g.b.beginRow(&.{g_ty}, g_ty);
    const kept = try g.b.call(.i64, .times_wrap, &.{ Ref.rowParam(0), try g.b.litInt(g_ty, 1) });
    try testing.expect(kept != Ref.rowParam(0));
    try g.b.endRow(.{ .value = &.{kept} });
}

test "N15a: an absorbing operand is the chain at any position, all ones absorbs bitwise_or at its own type, and a dropped operand that can fail keeps it" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const u8_ty = try f.types.intTy(.u8);
    _ = try f.b.beginRow(&.{ u8_ty, u8_ty, u8_ty }, u8_ty);
    const x = Ref.rowParam(0);
    const y = Ref.rowParam(1);
    const zero = try f.b.litInt(u8_ty, 0);
    const ones = try f.b.litInt(u8_ty, 255);
    try testing.expectEqual(zero, try f.b.call(.u8, .bitwise_and, &.{ x, zero, y }));
    try testing.expectEqual(zero, try f.b.call(.u8, .times_wrap, &.{ x, try f.b.call(.u8, .times_wrap, &.{ y, zero }) }));
    try testing.expectEqual(ones, try f.b.call(.u8, .bitwise_or, &.{ ones, x }));
    // 127 is not all ones in `U8`.
    try testing.expect(try f.b.call(.u8, .bitwise_or, &.{ try f.b.litInt(u8_ty, 127), x }) != try f.b.litInt(u8_ty, 127));
    // `div_trunc` fails on a zero divisor, so dropping it would drop the failure.
    const fails = try f.b.call(.u8, .div_trunc, &.{ x, Ref.rowParam(2) });
    const kept = try f.b.call(.u8, .bitwise_and, &.{ y, fails, zero });
    try testing.expect(kept != zero);
    try f.b.endRow(.{ .value = &.{kept} });
    try verifyOk(&f);

    var g: Fixture = undefined;
    g.init();
    defer g.deinit();
    g.b.hooks.knocked_out[n15aIndex(.bitwise_and, .absorbing)] = true;
    const g_ty = try g.types.intTy(.i64);
    _ = try g.b.beginRow(&.{g_ty}, g_ty);
    const g_zero = try g.b.litInt(g_ty, 0);
    const stays = try g.b.call(.i64, .bitwise_and, &.{ Ref.rowParam(0), g_zero });
    try testing.expect(stays != g_zero);
    try g.b.endRow(.{ .value = &.{stays} });
}

// A literal switch on `x` over the `I64` literals `keys`, whose arm `i` ends
// in `values[i]` and whose default arm ends in `values[keys.len]`; an arm
// value of null is built by `inner`, which reads the arm's index.
// The errors of the test helpers that build switches: allocation, and a
// check an inner arm makes.
const HelperError = Allocator.Error || error{TestExpectedEqual};

fn litSwitchOf(b: *Builder, x: Ref, keys: []const i128, values: []const ?Ref, inner: anytype) HelperError!Ref {
    const i64_ty = try b.types.intTy(.i64);
    var ids: [8]u32 = undefined;
    for (keys, ids[0..keys.len]) |k, *id| id.* = (try b.internLit(i64_ty, .{ .int = @bitCast(k) })).index();
    var arms: [9]RegionId = undefined;
    for (values, 0..) |v, i| {
        arms[i] = try b.openLitArm(x, ids[0..keys.len], @intCast(i));
        const value = v orelse try inner.build(b, i);
        try b.close(.{ .value = &.{value} });
    }
    const out_ty = if (values[0]) |v| b.store.refTy(b.row, v) else i64_ty;
    return b.switchOn(x, arms[0..values.len], &.{}, &.{out_ty}, ids[0..keys.len]);
}

const NoInner = struct {
    fn build(_: NoInner, _: *Builder, _: usize) HelperError!Ref {
        unreachable; // NoInner is only used where no inner builder is ever invoked
    }
};

// The keys of the literal switch `ref`, as integers.
fn litKeys(b: *const Builder, ref: Ref, out: []i128) []i128 {
    const keys = b.store.wordSlice(b.store.node(ref.nodeId()).aux);
    for (keys, out[0..keys.len]) |k, *o| o.* = @intCast(Builder.litIntValue(b.types, b.store.lit(LitId.of(k))).?);
    return out[0..keys.len];
}

fn armOf(b: *const Builder, ref: Ref, i: usize) Ref {
    return b.armValue(b.store.regionSlice(b.store.node(ref.nodeId()).regions)[i]).?;
}

test "N7: a literal switch has its keyed arms in ascending order and keeps the first arm of a repeated key" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    _ = try f.b.beginRow(&.{ i64_ty, i64_ty, i64_ty, i64_ty, i64_ty }, i64_ty);
    const p = Ref.rowParam;
    const sw = try litSwitchOf(&f.b, p(0), &.{ 2, 1, 2 }, &.{ p(1), p(2), p(3), p(4) }, NoInner{});
    var buf: [8]i128 = undefined;
    try testing.expectEqualSlices(i128, &.{ 1, 2 }, litKeys(&f.b, sw, &buf));
    try testing.expectEqual(p(2), armOf(&f.b, sw, 0));
    try testing.expectEqual(p(1), armOf(&f.b, sw, 1));
    try testing.expectEqual(p(4), armOf(&f.b, sw, 2));
    try f.b.endRow(.{ .value = &.{sw} });
    var report = try @import("verify.zig").verifyAll(testing.allocator, &f.store, &f.types);
    defer report.deinit();
    try testing.expect(report.ok());
}

test "N13c and N13d on literals: a known literal takes its arm, an arm's key decides a nested switch, and a default arm drops the keys it excludes" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    _ = try f.b.beginRow(&.{ i64_ty, i64_ty, i64_ty, i64_ty }, i64_ty);
    const p = Ref.rowParam;
    const three = try f.b.litInt(i64_ty, 3);
    try testing.expectEqual(p(2), try litSwitchOf(&f.b, three, &.{ 1, 3 }, &.{ p(1), p(2), p(3) }, NoInner{}));
    try testing.expectEqual(p(3), try litSwitchOf(&f.b, three, &.{ 1, 2 }, &.{ p(1), p(2), p(3) }, NoInner{}));

    // switch x { 1: switch x { 1: p1, _: p2 }, _: switch x { 1: p1, 2: p2, _: p3 } }
    const Inner = struct {
        fn build(_: @This(), b: *Builder, arm: usize) HelperError!Ref {
            if (arm == 0) return litSwitchOf(b, p(0), &.{1}, &.{ p(1), p(2) }, NoInner{});
            const sw = try litSwitchOf(b, p(0), &.{ 1, 2 }, &.{ p(1), p(2), p(3) }, NoInner{});
            var buf: [8]i128 = undefined;
            try testing.expectEqualSlices(i128, &.{2}, litKeys(b, sw, &buf));
            return sw;
        }
    };
    const outer = try litSwitchOf(&f.b, p(0), &.{1}, &.{ null, null }, Inner{});
    try testing.expectEqual(p(1), armOf(&f.b, outer, 0));
    try f.b.endRow(.{ .value = &.{outer} });
}

test "N7c: nested literal switches on one scrutinee are one switch, in whichever order they were written" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    _ = try f.b.beginRow(&.{ i64_ty, i64_ty, i64_ty, i64_ty }, i64_ty);
    const p = Ref.rowParam;
    // if x == 1 a else if x == 2 b else c, as the walk writes it, and with the tests swapped.
    const Chain = struct {
        first: i128,
        second: i128,
        values: [3]Ref,
        fn build(self: @This(), b: *Builder, _: usize) HelperError!Ref {
            return litSwitchOf(b, p(0), &.{self.second}, &.{ self.values[1], self.values[2] }, NoInner{});
        }
    };
    const one: Chain = .{ .first = 1, .second = 2, .values = .{ p(1), p(2), p(3) } };
    const two: Chain = .{ .first = 2, .second = 1, .values = .{ p(2), p(1), p(3) } };
    const a = try litSwitchOf(&f.b, p(0), &.{one.first}, &.{ one.values[0], null }, one);
    const b = try litSwitchOf(&f.b, p(0), &.{two.first}, &.{ two.values[0], null }, two);
    var buf: [8]i128 = undefined;
    try testing.expectEqualSlices(i128, &.{ 1, 2 }, litKeys(&f.b, a, &buf));
    var cmp: equal.Comparison = .{ .gpa = testing.allocator, .store = &f.store };
    defer cmp.deinit();
    try testing.expect(try cmp.values(a, b));
    // Other arms for the keys are another switch.
    const other: Chain = .{ .first = 1, .second = 2, .values = .{ p(2), p(1), p(3) } };
    const c = try litSwitchOf(&f.b, p(0), &.{other.first}, &.{ other.values[0], null }, other);
    try testing.expect(!try cmp.values(a, c));
    try f.b.endRow(.{ .value = &.{a} });
    var report = try @import("verify.zig").verifyAll(testing.allocator, &f.store, &f.types);
    defer report.deinit();
    try testing.expect(report.ok());
}

test "N15c: a literal operand of integer is_eq, plus and times goes last, and two literals stay as written" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    _ = try f.b.beginRow(&.{i64_ty}, i64_ty);
    const p = Ref.rowParam;
    const three = try f.b.litInt(i64_ty, 3);
    for ([_]prims.Method{ .is_eq, .plus, .times }) |m| {
        const swapped = try f.b.call(.i64, m, &.{ three, p(0) });
        const n = f.store.node(swapped.nodeId());
        try testing.expectEqualSlices(Ref, &.{ p(0), three }, f.store.refSlice(n.args));
    }
    // Over two literals `not_lit` fails; `minus` is not commutative.
    for (table.rules, 0..) |r, i| f.b.hooks.knocked_out[i] = r.tier == .evaluation;
    const four = try f.b.litInt(i64_ty, 4);
    const both = f.store.node((try f.b.call(.i64, .plus, &.{ three, four })).nodeId());
    try testing.expectEqualSlices(Ref, &.{ three, four }, f.store.refSlice(both.args));
    const minus = f.store.node((try f.b.call(.i64, .minus, &.{ three, p(0) })).nodeId());
    try testing.expectEqualSlices(Ref, &.{ three, p(0) }, f.store.refSlice(minus.args));
    for (table.rules, 0..) |r, i| f.b.hooks.knocked_out[i] = std.mem.eql(u8, r.step, "N15c");
    const off = f.store.node((try f.b.call(.i64, .plus, &.{ three, p(0) })).nodeId());
    try testing.expectEqualSlices(Ref, &.{ three, p(0) }, f.store.refSlice(off.args));
    try f.b.endRow(.{ .value = &.{p(0)} });
}

test "N15c, parameter half: two root parameters of integer plus, times and is_eq, and of Str is_eq, go in parameter order; other operands and other rows stay, and the knockout stops it" {
    for ([_]bool{ false, true }) |knocked| {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        if (knocked) f.b.hooks.algorithms_off.insert(.param_order);
        const i64_ty = try f.types.intTy(.i64);
        const str_ty = try f.types.strTy();
        const row = try f.b.beginRow(&.{ i64_ty, i64_ty, str_ty, str_ty }, i64_ty);
        f.store.rows.items[row.index()].fixed_params = true;
        const p = Ref.rowParam;
        const args = struct {
            fn of(fx: *Fixture, r: Ref) []const Ref {
                return fx.store.refSlice(fx.store.node(r.nodeId()).args);
            }
        }.of;
        const want: [2]Ref = if (knocked) .{ p(1), p(0) } else .{ p(0), p(1) };
        for ([_]prims.Method{ .plus, .times, .is_eq }) |m| try testing.expectEqualSlices(Ref, &want, args(&f, try f.b.call(.i64, m, &.{ p(1), p(0) })));
        const str_want: [2]Ref = if (knocked) .{ p(3), p(2) } else .{ p(2), p(3) };
        try testing.expectEqualSlices(Ref, &str_want, args(&f, try f.b.call(.str, .is_eq, &.{ p(3), p(2) })));
        // `minus` is not commutative, and a parameter beside a node keeps its place.
        try testing.expectEqualSlices(Ref, &.{ p(1), p(0) }, args(&f, try f.b.call(.i64, .minus, &.{ p(1), p(0) })));
        const node = try f.b.call(.i64, .minus, &.{ p(0), p(1) });
        try testing.expectEqualSlices(Ref, &.{ node, p(0) }, args(&f, try f.b.call(.i64, .plus, &.{ node, p(0) })));
        // A region parameter is no root parameter.
        const lb = try f.b.openRegion(.loop_body, &.{ i64_ty, i64_ty });
        const s1 = Ref.regionParam(lb, 1);
        try testing.expectEqualSlices(Ref, &.{ s1, p(0) }, args(&f, try f.b.call(.i64, .plus, &.{ s1, p(0) })));
        try f.b.close(.{ .continue_ = &.{s1} });
        try f.b.endRow(.{ .value = &.{p(0)} });
        // A row whose parameters are numbered in first-read order keeps them as written.
        const helper = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
        _ = helper;
        try testing.expectEqualSlices(Ref, &.{ p(1), p(0) }, args(&f, try f.b.call(.i64, .plus, &.{ p(1), p(0) })));
        try f.b.endRow(.{ .value = &.{p(0)} });
    }
}

test "T1.11 and the other speculatable conditions read the operand cone: a field of a loop output keeps x - x and x * 0" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const rec_ty = try f.types.recordTy(&.{ .{ .name = "spare", .ty = i64_ty }, .{ .name = "total", .ty = i64_ty } });
    _ = try f.b.beginRow(&.{i64_ty}, i64_ty);
    const zero = try f.b.litInt(i64_ty, 0);
    const lb = try f.b.openRegion(.loop_body, &.{ i64_ty, rec_ty });
    const acc = Ref.regionParam(lb, 1);
    const next = try f.b.record(rec_ty, &.{
        try f.b.field(acc, 0),
        try f.b.call(.i64, .plus, &.{ try f.b.field(acc, 1), Ref.regionParam(lb, 0) }),
    });
    try f.b.close(.{ .continue_ = &.{next} });
    const init = try f.b.record(rec_ty, &.{ zero, zero });
    const loop = try f.b.loopOf(.for_range, &.{ zero, Ref.rowParam(0), init }, lb, &.{rec_ty});
    // The Field node is flagged speculatable, the loop it reads is not.
    const total = try f.b.field(loop, 1);
    try testing.expect(f.store.node(total.nodeId()).flags.speculatable);
    try testing.expect(!f.store.node(loop.nodeId()).flags.speculatable);
    const minus = try f.b.call(.i64, .minus, &.{ total, total });
    try testing.expectEqual(Op.prim, f.store.node(minus.nodeId()).op);
    const times = try f.b.call(.i64, .times, &.{ total, zero });
    try testing.expectEqual(Op.prim, f.store.node(times.nodeId()).op);
    // The same rules still fire over an operand whose cone is speculatable.
    try testing.expectEqual(zero, try f.b.call(.i64, .minus, &.{ Ref.rowParam(0), Ref.rowParam(0) }));
    try testing.expectEqual(zero, try f.b.call(.i64, .times, &.{ Ref.rowParam(0), zero }));
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus, &.{ minus, times })} });
    try verifyOk(&f);
}

test "N13j over floats: a fold is the IEEE result of the type, with Roc's one NaN and the bits of a negative zero" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const f64_ty = try f.types.floatTy(.f64);
    const f32_ty = try f.types.floatTy(.f32);
    const bool_ty = try f.types.boolTy();
    _ = try f.b.beginRow(&.{}, bool_ty);
    const lit = struct {
        fn at(x: *Fixture, ty: TyId, bits: u64) Allocator.Error!Ref {
            return x.b.litFloatBits(ty, bits);
        }
    }.at;
    // 1.5 + 2.25 = 3.75
    try testing.expectEqual(try lit(&f, f64_ty, 0x400e000000000000), try f.b.call(.f64, .plus, &.{ try lit(&f, f64_ty, 0x3ff8000000000000), try lit(&f, f64_ty, 0x4002000000000000) }));
    // 0.1 + 0.2 is not 0.3 in F64, and is 0.3 rounded in F32.
    try testing.expectEqual(try lit(&f, f64_ty, 0x3fd3333333333334), try f.b.call(.f64, .plus, &.{ try lit(&f, f64_ty, 0x3fb999999999999a), try lit(&f, f64_ty, 0x3fc999999999999a) }));
    try testing.expectEqual(try lit(&f, f32_ty, 0x3e99999a), try f.b.call(.f32, .plus, &.{ try lit(&f, f32_ty, 0x3dcccccd), try lit(&f, f32_ty, 0x3e4ccccd) }));
    // inf - inf is the canonical NaN of the type.
    try testing.expectEqual(try lit(&f, f64_ty, 0x7ff8000000000000), try f.b.call(.f64, .minus, &.{ try lit(&f, f64_ty, 0x7ff0000000000000), try lit(&f, f64_ty, 0x7ff0000000000000) }));
    try testing.expectEqual(try lit(&f, f32_ty, 0x7fc00000), try f.b.call(.f32, .minus, &.{ try lit(&f, f32_ty, 0x7f800000), try lit(&f, f32_ty, 0x7f800000) }));
    // -0.0 * 1.0 keeps the sign bit.
    try testing.expectEqual(try lit(&f, f64_ty, 0x8000000000000000), try f.b.call(.f64, .times, &.{ try lit(&f, f64_ty, 0x8000000000000000), try lit(&f, f64_ty, 0x3ff0000000000000) }));
    // Comparisons follow IEEE: NaN equals nothing, and -0.0 equals 0.0.
    const nan = try lit(&f, f64_ty, 0x7ff8000000000000);
    try testing.expectEqual(try f.b.litBool(false), try f.b.call(.f64, .is_eq, &.{ nan, nan }));
    try testing.expectEqual(try f.b.litBool(false), try f.b.call(.f64, .is_lt, &.{ nan, try lit(&f, f64_ty, 0) }));
    try testing.expectEqual(try f.b.litBool(true), try f.b.call(.f64, .is_eq, &.{ try lit(&f, f64_ty, 0x8000000000000000), try lit(&f, f64_ty, 0) }));
    try f.b.endRow(.{ .value = &.{try f.b.litBool(true)} });
}

test "N13j over Str: equality and concatenation of literals fold, and the knockout stops them" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const str_ty = try f.types.strTy();
    const bool_ty = try f.types.boolTy();
    _ = try f.b.beginRow(&.{}, bool_ty);
    try testing.expectEqual(try f.b.litBool(true), try f.b.call(.str, .is_eq, &.{ try f.b.litStr("ab"), try f.b.litStr("ab") }));
    try testing.expectEqual(try f.b.litBool(false), try f.b.call(.str, .is_eq, &.{ try f.b.litStr("ab"), try f.b.litStr("abc") }));
    try testing.expectEqual(try f.b.litStr("abc"), try f.b.call(.str, .concat, &.{ try f.b.litStr("ab"), try f.b.litStr("c") }));
    _ = str_ty;
    f.b.hooks.knocked_out[ruleIndexArgs("N13j", .prim, 0)] = true;
    f.b.hooks.knocked_out[ruleIndexArgs("N13j", .prim, 1)] = true;
    const kept = try f.b.call(.str, .is_eq, &.{ try f.b.litStr("x"), try f.b.litStr("x") });
    try testing.expect(f.store.node(kept.nodeId()).op == .prim);
    try f.b.endRow(.{ .value = &.{try f.b.litBool(true)} });
}

test "N13j in a chain: two adjacent literals fold into one, and a Str literal goes last in an equality" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const u64_ty = try f.types.intTy(.u64);
    const str_ty = try f.types.strTy();
    _ = try f.b.beginRow(&.{ u64_ty, str_ty }, u64_ty);
    const p = Ref.rowParam;
    // p0 +% 1 +% 2 is p0 +% 3, in either grouping.
    const left = try f.b.call(.u64, .plus_wrap, &.{ try f.b.call(.u64, .plus_wrap, &.{ p(0), try f.b.litInt(u64_ty, 1) }), try f.b.litInt(u64_ty, 2) });
    const right = try f.b.call(.u64, .plus_wrap, &.{ p(0), try f.b.litInt(u64_ty, 3) });
    try testing.expectEqual(right, left);
    // "a" == p1 is p1 == "a".
    const lit = try f.b.litStr("a");
    const swapped = try f.b.call(.str, .is_eq, &.{ lit, p(1) });
    try testing.expectEqualSlices(Ref, &.{ p(1), lit }, f.store.refSlice(f.store.node(swapped.nodeId()).args));
    try f.b.endRow(.{ .value = &.{left} });
    try verifyOk(&f);
}

test "N13d on Bool.not: a negation of a Bool an earlier And operand decided is the opposite literal, and the knockout stops it" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const bool_ty = try f.types.boolTy();
    _ = try f.b.beginRow(&.{bool_ty}, bool_ty);
    const p = Ref.rowParam(0);
    // p and !p: the second operand sees p true, so it is False, and False absorbs.
    const r = try f.b.openOperand(&.{p}, .and_);
    const negated = try f.b.call(.bool_, .not, &.{p});
    try testing.expectEqual(try f.b.litBool(false), negated);
    try testing.expectEqual(@as(u32, 1), f.b.hooks.algorithms_fired.get(.decided_not));
    try f.b.close(.{ .value = &.{negated} });
    try f.b.endRow(.{ .value = &.{try f.b.andOf(p, &.{r})} });

    var g: Fixture = undefined;
    g.init();
    defer g.deinit();
    g.b.hooks.algorithms_off.insert(.decided_not);
    const g_bool = try g.types.boolTy();
    _ = try g.b.beginRow(&.{g_bool}, g_bool);
    _ = try g.b.openOperand(&.{Ref.rowParam(0)}, .and_);
    const kept = try g.b.call(.bool_, .not, &.{Ref.rowParam(0)});
    try testing.expect(g.store.node(kept.nodeId()).op == .prim);
    try g.b.close(.{ .value = &.{kept} });
    try g.b.endRow(.{ .value = &.{Ref.rowParam(0)} });
}

// `switch s { Err => crash, Ok(v) => v }` over the `Try` that the chain
// `if p0 Err else if p1 Err else Ok(p2)` gives: N13w's case, with the crash
// built by `crashOf`. The rebuild sets `sole_reader`; the test does it here.
fn rejectedChain(f: *Fixture, comptime crashOf: fn (*Builder, TyId, Ref) Allocator.Error!Ref) Allocator.Error!Ref {
    const i64_ty = try f.types.intTy(.i64);
    const try_ty = try f.types.tagUnionTy(&.{ .{ .name = "Err", .payload = &.{} }, .{ .name = "Ok", .payload = &.{i64_ty} } });
    const err = try f.types.name("Err");
    const ok = try f.types.name("Ok");
    const p = Ref.rowParam;
    var outer: [2]RegionId = undefined;
    outer[0] = try f.b.openArm(p(0), 0);
    var inner: [2]RegionId = undefined;
    inner[0] = try f.b.openArm(p(1), 0);
    try f.b.close(.{ .value = &.{try f.b.tag(try_ty, ok, &.{p(2)})} });
    inner[1] = try f.b.openArm(p(1), 1);
    try f.b.close(.{ .value = &.{try f.b.tag(try_ty, err, &.{})} });
    try f.b.close(.{ .value = &.{try f.b.switchOn(p(1), &inner, &.{}, &.{try_ty}, &.{})} });
    outer[1] = try f.b.openArm(p(0), 1);
    try f.b.close(.{ .value = &.{try f.b.tag(try_ty, err, &.{})} });
    const s = try f.b.switchOn(p(0), &outer, &.{}, &.{try_ty}, &.{});
    var arms: [2]RegionId = undefined;
    arms[0] = try f.b.openTagArm(s, err);
    try f.b.close(.{ .value = &.{try crashOf(&f.b, i64_ty, try f.b.litStr("rejected"))} });
    arms[1] = try f.b.openTagArm(s, ok);
    try f.b.close(.{ .value = &.{try f.b.payload(s, ok, 0)} });
    f.b.sole_reader = s;
    defer f.b.sole_reader = null;
    return f.b.tagSwitchOn(s, &.{ err, ok }, &arms, &.{}, &.{i64_ty});
}

test "N13w: a switch on a chain of tests whose every other value reaches a rejected literal is the one value, and the knockout and an author's crash stop it" {
    const Case = enum { fires, knocked, written };
    inline for (comptime std.enums.values(Case)) |case| {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        if (case == .knocked) f.b.hooks.algorithms_off.insert(.rejected_arm);
        const bool_ty = try f.types.boolTy();
        const i64_ty = try f.types.intTy(.i64);
        const row = try f.b.beginRow(&.{ bool_ty, bool_ty, i64_ty }, i64_ty);
        const out = try rejectedChain(&f, if (case == .written) Builder.crash else Builder.rejectedLiteral);
        try f.b.endRow(.{ .value = &.{out} });
        try verifyOk(&f);
        switch (case) {
            // Both tests go: the value is the `Ok` payload.
            .fires => {
                try testing.expectEqual(Ref.rowParam(2), out);
                try testing.expectEqual(@as(u32, 1), f.b.hooks.algorithms_fired.get(.rejected_arm));
            },
            .knocked, .written => try testing.expectEqual(Op.switch_, f.store.node(out.nodeId()).op),
        }
        // Where the chain reaches no crash, the result is the payload.
        var arena = std.heap.ArenaAllocator.init(testing.allocator);
        defer arena.deinit();
        const eval = @import("eval.zig");
        var e = try eval.Evaluator.init(arena.allocator(), &f.store, &f.types, .strict);
        try testing.expect((try e.run(row, &.{ .{ .bool_ = false }, .{ .bool_ = false }, .{ .int = 7 } })).eql(.{ .int = 7 }));
    }
}

test "N13n mirrors: a match on x == k meets the And an if on x == k is, and the nested if N7d merges, and their knockout stops them" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const bool_ty = try f.types.boolTy();
    _ = try f.b.beginRow(&.{ i64_ty, bool_ty, i64_ty, i64_ty }, bool_ty);
    const p = Ref.rowParam;
    var cmp: equal.Comparison = .{ .gpa = testing.allocator, .store = &f.store };
    defer cmp.deinit();
    // `x == 3 and b`, as `and_` builds it.
    const Conj = struct {
        fn build(b: *Builder, x: Ref, y: Ref) HelperError!Ref {
            const first = try b.call(.i64, .is_eq, &.{ x, try b.litInt(try b.types.intTy(.i64), 3) });
            const r = try b.openOperand(&.{first}, .and_);
            try b.close(.{ .value = &.{y} });
            return b.andOf(first, &.{r});
        }
    };
    // match x { 3 => b, _ => False } is N13o's `x == 3 and b`.
    const conj = try Conj.build(&f.b, p(0), p(1));
    try testing.expect(try cmp.values(conj, try litSwitchOf(&f.b, p(0), &.{3}, &.{ p(1), try f.b.litBool(false) }, NoInner{})));
    // match x { 3 => if b y else z, _ => z } is N7d's `if x == 3 and b y else z`.
    const Inner = struct {
        fn build(_: @This(), b: *Builder, i: usize) HelperError!Ref {
            std.debug.assert(i == 0);
            var arms: [2]RegionId = undefined;
            arms[0] = try b.openArm(Ref.rowParam(1), 0);
            try b.close(.{ .value = &.{Ref.rowParam(3)} });
            arms[1] = try b.openArm(Ref.rowParam(1), 1);
            try b.close(.{ .value = &.{Ref.rowParam(2)} });
            return b.switchOn(Ref.rowParam(1), &arms, &.{}, &.{try b.types.intTy(.i64)}, &.{});
        }
    };
    const nested = try litSwitchOf(&f.b, p(0), &.{3}, &.{ null, p(3) }, Inner{});
    var merged_arms: [2]RegionId = undefined;
    const c = try Conj.build(&f.b, p(0), p(1));
    merged_arms[0] = try f.b.openArm(c, 0);
    try f.b.close(.{ .value = &.{p(3)} });
    merged_arms[1] = try f.b.openArm(c, 1);
    try f.b.close(.{ .value = &.{p(2)} });
    const merged = try f.b.switchOn(c, &merged_arms, &.{}, &.{i64_ty}, &.{});
    try testing.expect(try cmp.values(nested, merged));
    for (table.rules, 0..) |r, i| f.b.hooks.knocked_out[i] = std.mem.endsWith(u8, r.step, "/N13n");
    try testing.expect(!try cmp.values(conj, try litSwitchOf(&f.b, p(0), &.{3}, &.{ p(1), try f.b.litBool(false) }, NoInner{})));
    try testing.expect(!try cmp.values(merged, try litSwitchOf(&f.b, p(0), &.{3}, &.{ null, p(3) }, Inner{})));
    try f.b.endRow(.{ .value = &.{conj} });
}

// `if x == first a else if second == x b else c`, as the walk builds it.
fn ifChain(b: *Builder, x: Ref, first: i128, second: i128, values: [3]Ref) HelperError!Ref {
    const i64_ty = try b.types.intTy(.i64);
    const t1 = try b.call(.i64, .is_eq, &.{ x, try b.litInt(i64_ty, first) });
    const else1 = try b.openArm(t1, 0);
    const t2 = try b.call(.i64, .is_eq, &.{ try b.litInt(i64_ty, second), x });
    var inner: [2]RegionId = undefined;
    inner[0] = try b.openArm(t2, 0);
    try b.close(.{ .value = &.{values[2]} });
    inner[1] = try b.openArm(t2, 1);
    try b.close(.{ .value = &.{values[1]} });
    const v2 = try b.switchOn(t2, &inner, &.{}, &.{i64_ty}, &.{});
    try b.close(.{ .value = &.{v2} });
    const then1 = try b.openArm(t1, 1);
    try b.close(.{ .value = &.{values[0]} });
    return b.switchOn(t1, &.{ else1, then1 }, &.{}, &.{i64_ty}, &.{});
}

test "N13n with N7c: an if chain of integer equality tests is the literal switch, with the literal on either side, and the knockout stops it" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    _ = try f.b.beginRow(&.{ i64_ty, i64_ty, i64_ty, i64_ty }, i64_ty);
    const p = Ref.rowParam;
    var cmp: equal.Comparison = .{ .gpa = testing.allocator, .store = &f.store };
    defer cmp.deinit();
    const match_ = try litSwitchOf(&f.b, p(0), &.{ 2, 1 }, &.{ p(2), p(1), p(3) }, NoInner{});
    const chain = try ifChain(&f.b, p(0), 1, 2, .{ p(1), p(2), p(3) });
    try testing.expect(try cmp.values(match_, chain));
    const swapped = try ifChain(&f.b, p(0), 2, 1, .{ p(2), p(1), p(3) });
    try testing.expect(try cmp.values(match_, swapped));
    for (table.rules, 0..) |r, i| f.b.hooks.knocked_out[i] = std.mem.eql(u8, r.step, "N13n");
    const off = try ifChain(&f.b, p(0), 1, 2, .{ p(1), p(2), p(3) });
    try testing.expect(!try cmp.values(match_, off));
    try f.b.endRow(.{ .value = &.{chain} });
}

test "N13e, N13f and N13t over literal switches: a match on x == k is the comparison, and a negation passes into the arms" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const bool_ty = try f.types.boolTy();
    _ = try f.b.beginRow(&.{ i64_ty, bool_ty, bool_ty }, bool_ty);
    const p = Ref.rowParam;
    const t = try f.b.litBool(true);
    const fl = try f.b.litBool(false);
    const eq = try f.b.call(.i64, .is_eq, &.{ p(0), try f.b.litInt(i64_ty, 3) });
    // match x { 3 => True, _ => False } and its mirror.
    try testing.expectEqual(eq, try litSwitchOf(&f.b, p(0), &.{3}, &.{ t, fl }, NoInner{}));
    try testing.expectEqual(try f.b.call(.bool_, .not, &.{eq}), try litSwitchOf(&f.b, p(0), &.{3}, &.{ fl, t }, NoInner{}));
    // not(match x { 1 => a, 2 => b, _ => a }) is the match of the negations.
    const sw = try litSwitchOf(&f.b, p(0), &.{ 1, 2 }, &.{ p(1), p(2), p(1) }, NoInner{});
    const neg = try f.b.call(.bool_, .not, &.{sw});
    const na = try f.b.call(.bool_, .not, &.{p(1)});
    const nb = try f.b.call(.bool_, .not, &.{p(2)});
    const direct = try litSwitchOf(&f.b, p(0), &.{ 1, 2 }, &.{ na, nb, na }, NoInner{});
    var cmp: equal.Comparison = .{ .gpa = testing.allocator, .store = &f.store };
    defer cmp.deinit();
    try testing.expect(try cmp.values(neg, direct));
    try f.b.endRow(.{ .value = &.{neg} });
}

// Build one exit shape with `off` knocked out, verify it, and check that it
// computes `want` on each argument list.
const ExitCase = struct {
    f: Fixture = undefined,
    row: RowId = RowId.of(0),

    fn start(self: *ExitCase, off: ?ExitRule) void {
        self.f.init();
        if (off) |rule| self.f.b.hooks.exits_off.insert(rule);
    }

    fn body(self: *ExitCase) ir.Region {
        return self.f.store.region(self.f.store.row(self.row).body);
    }

    fn fired(self: *ExitCase, rule: ExitRule) u32 {
        return self.f.b.hooks.exits_fired.get(rule);
    }

    // The switch the body's `Value` end reads, whose arms all end in `Value`.
    fn valueSwitch(self: *ExitCase, end: ir.End) ?ir.Node {
        if (end.refs.len != 1) return null;
        const r = self.f.store.refSlice(end.refs)[0];
        if (r.kind != .node) return null;
        const nd = self.f.store.node(r.nodeId());
        if (nd.op != .switch_) return null;
        for (self.f.store.regionSlice(nd.regions)) |a| {
            if (self.f.store.region(a).end.kind != .value) return null;
        }
        return nd;
    }

    fn check(self: *ExitCase, cases: []const []const @import("eval.zig").Value, want: []const @import("eval.zig").Value) (@import("eval.zig").Error || error{TestUnexpectedResult})!void {
        try verifyOk(&self.f);
        const eval = @import("eval.zig");
        var arena = std.heap.ArenaAllocator.init(testing.allocator);
        defer arena.deinit();
        var e = try eval.Evaluator.init(arena.allocator(), &self.f.store, &self.f.types, .strict);
        for (cases, want) |args, w| try testing.expect((try e.run(self.row, args)).eql(w));
    }
};

test "T6: a row body that ends in Return ends in Value, and the knockout stops it" {
    for ([_]?ExitRule{ null, .t6 }) |off| {
        var x: ExitCase = .{};
        x.start(off);
        defer x.f.deinit();
        const i64_ty = try x.f.types.intTy(.i64);
        x.row = try x.f.b.beginRow(&.{i64_ty}, i64_ty);
        try x.f.b.endRow(.{ .return_ = Ref.rowParam(0) });
        try testing.expectEqual(if (off == null) ir.EndKind.value else .return_, x.body().end.kind);
        try x.check(&.{&.{.{ .int = 4 }}}, &.{.{ .int = 4 }});
    }
}

test "T3: an exiting switch whose arms all return is a value switch the row returns, and the knockout stops it" {
    for ([_]?ExitRule{ null, .t3 }) |off| {
        var x: ExitCase = .{};
        x.start(off);
        defer x.f.deinit();
        const bool_ty = try x.f.types.boolTy();
        const i64_ty = try x.f.types.intTy(.i64);
        x.row = try x.f.b.beginRow(&.{ bool_ty, i64_ty, i64_ty }, i64_ty);
        const p = Ref.rowParam;
        const arm0 = try x.f.b.openArm(p(0), 0);
        try x.f.b.close(.{ .return_ = p(1) });
        const arm1 = try x.f.b.openArm(p(0), 1);
        try x.f.b.close(.{ .return_ = p(2) });
        const sw = try x.f.b.exitingSwitch(p(0), &.{ arm0, arm1 }, &.{}, &.{});
        try x.f.b.endRow(.{ .branch = sw });
        if (off == null) {
            try testing.expect(x.valueSwitch(x.body().end) != null);
            try testing.expectEqual(@as(u32, 1), x.fired(.t6));
        } else try testing.expectEqual(ir.EndKind.branch, x.body().end.kind);
        try x.check(&.{ &.{ .{ .bool_ = false }, .{ .int = 1 }, .{ .int = 2 } }, &.{ .{ .bool_ = true }, .{ .int = 1 }, .{ .int = 2 } } }, &.{ .{ .int = 1 }, .{ .int = 2 } });
    }
}

test "T4: a join with no nodes is substituted into its jumps, so the arms return, and the knockout stops it" {
    for ([_]?ExitRule{ null, .t4 }) |off| {
        var x: ExitCase = .{};
        x.start(off);
        defer x.f.deinit();
        const i64_ty = try x.f.types.intTy(.i64);
        const union_ty = try x.f.types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{} }, .{ .name = "C", .payload = &.{} } });
        x.row = try x.f.b.beginRow(&.{ union_ty, i64_ty, i64_ty, i64_ty }, i64_ty);
        const p = Ref.rowParam;
        // match u { A => a, B => b, C => return z } then return what the match gave.
        const join = try x.f.b.reserveJoin(&.{i64_ty});
        const arm_a = try x.f.b.openTagArm(p(0), try x.f.types.name("A"));
        try x.f.b.close(.{ .jump = .{ .join = join, .args = &.{p(1)} } });
        const arm_b = try x.f.b.openTagArm(p(0), try x.f.types.name("B"));
        try x.f.b.close(.{ .jump = .{ .join = join, .args = &.{p(2)} } });
        const arm_c = try x.f.b.openTagArm(p(0), try x.f.types.name("C"));
        try x.f.b.close(.{ .return_ = p(3) });
        const sw = try x.f.b.exitingSwitch(p(0), &.{ arm_a, arm_b, arm_c }, &.{join}, &.{});
        try x.f.b.continueIn(sw, join);
        try x.f.b.endRow(.{ .return_ = Ref.regionParam(join, 0) });
        if (off == null) {
            try testing.expectEqual(@as(u32, 1), x.fired(.t4));
            try testing.expectEqual(@as(u32, 1), x.fired(.t3));
            const v = x.valueSwitch(x.body().end).?;
            try testing.expectEqual(@as(usize, 3), v.regions.len);
        } else try testing.expectEqual(ir.EndKind.branch, x.body().end.kind);
        var cases: [3][4]@import("eval.zig").Value = undefined;
        const tag_names = [_][]const u8{ "A", "B", "C" };
        for (&cases, tag_names) |*c, text| c.* = .{ .{ .tag = .{ .name = try x.f.types.name(text), .payload = &.{} } }, .{ .int = 1 }, .{ .int = 2 }, .{ .int = 3 } };
        try x.check(&.{ &cases[0], &cases[1], &cases[2] }, &.{ .{ .int = 1 }, .{ .int = 2 }, .{ .int = 3 } });
    }
}

test "T2: a join one path jumps to is inlined at the jump, and the knockout stops it" {
    for ([_]?ExitRule{ null, .t2 }) |off| {
        var x: ExitCase = .{};
        x.start(off);
        defer x.f.deinit();
        const bool_ty = try x.f.types.boolTy();
        const i64_ty = try x.f.types.intTy(.i64);
        x.row = try x.f.b.beginRow(&.{ bool_ty, i64_ty, i64_ty }, i64_ty);
        const p = Ref.rowParam;
        // if c { y = a } else { return b }; return y * y
        const join = try x.f.b.reserveJoin(&.{i64_ty});
        const arm0 = try x.f.b.openArm(p(0), 0);
        try x.f.b.close(.{ .return_ = p(2) });
        const arm1 = try x.f.b.openArm(p(0), 1);
        try x.f.b.close(.{ .jump = .{ .join = join, .args = &.{p(1)} } });
        const sw = try x.f.b.exitingSwitch(p(0), &.{ arm0, arm1 }, &.{join}, &.{});
        try x.f.b.continueIn(sw, join);
        const y = Ref.regionParam(join, 0);
        try x.f.b.endRow(.{ .return_ = try x.f.b.call(.i64, .times, &.{ y, y }) });
        if (off == null) {
            try testing.expectEqual(@as(u32, 1), x.fired(.t2));
            try testing.expect(x.valueSwitch(x.body().end) != null);
        } else try testing.expectEqual(ir.EndKind.branch, x.body().end.kind);
        try x.check(&.{ &.{ .{ .bool_ = false }, .{ .int = 3 }, .{ .int = 5 } }, &.{ .{ .bool_ = true }, .{ .int = 3 }, .{ .int = 5 } } }, &.{ .{ .int = 5 }, .{ .int = 9 } });
    }
}

test "a row value after an exiting switch leaves from its join, so the arms end in terminators" {
    var x: ExitCase = .{};
    x.start(null);
    defer x.f.deinit();
    const bool_ty = try x.f.types.boolTy();
    const i64_ty = try x.f.types.intTy(.i64);
    x.row = try x.f.b.beginRow(&.{ bool_ty, i64_ty, i64_ty }, i64_ty);
    const p = Ref.rowParam;
    // if c { return b }; a * a, with the row's value given as a value.
    const join = try x.f.b.reserveJoin(&.{});
    const arm0 = try x.f.b.openArm(p(0), 0);
    try x.f.b.close(.{ .jump = .{ .join = join, .args = &.{} } });
    const arm1 = try x.f.b.openArm(p(0), 1);
    try x.f.b.close(.{ .return_ = p(2) });
    const sw = try x.f.b.exitingSwitch(p(0), &.{ arm0, arm1 }, &.{join}, &.{});
    try x.f.b.continueIn(sw, join);
    try x.f.b.endRow(.{ .value = &.{try x.f.b.call(.i64, .times, &.{ p(1), p(1) })} });
    try verifyOk(&x.f);
    try testing.expectEqual(ir.EndKind.value, x.body().end.kind);
    try x.check(&.{ &.{ .{ .bool_ = false }, .{ .int = 3 }, .{ .int = 5 } }, &.{ .{ .bool_ = true }, .{ .int = 3 }, .{ .int = 5 } } }, &.{ .{ .int = 9 }, .{ .int = 5 } });
}

test "T5: a switch every arm of which jumps to its join is a value switch the join's code follows, and the knockout stops it" {
    for ([_]?ExitRule{ null, .t5 }) |off| {
        var x: ExitCase = .{};
        x.start(off);
        defer x.f.deinit();
        const bool_ty = try x.f.types.boolTy();
        const i64_ty = try x.f.types.intTy(.i64);
        x.row = try x.f.b.beginRow(&.{ bool_ty, i64_ty, i64_ty }, i64_ty);
        const p = Ref.rowParam;
        // y = if c { a } else { b }, written with jumps; return y * y
        const join = try x.f.b.reserveJoin(&.{i64_ty});
        const arm0 = try x.f.b.openArm(p(0), 0);
        try x.f.b.close(.{ .jump = .{ .join = join, .args = &.{p(2)} } });
        const arm1 = try x.f.b.openArm(p(0), 1);
        try x.f.b.close(.{ .jump = .{ .join = join, .args = &.{p(1)} } });
        const sw = try x.f.b.exitingSwitch(p(0), &.{ arm0, arm1 }, &.{join}, &.{});
        try x.f.b.continueIn(sw, join);
        const y = Ref.regionParam(join, 0);
        try x.f.b.endRow(.{ .return_ = try x.f.b.call(.i64, .times, &.{ y, y }) });
        if (off == null) {
            try testing.expectEqual(@as(u32, 1), x.fired(.t5));
            const end = x.body().end;
            try testing.expectEqual(ir.EndKind.value, end.kind);
            const product = x.f.store.node(x.f.store.refSlice(end.refs)[0].nodeId());
            try testing.expectEqual(Op.prim, product.op);
            const factor = x.f.store.refSlice(product.args)[0];
            try testing.expectEqual(Op.switch_, x.f.store.node(factor.nodeId()).op);
        } else try testing.expectEqual(ir.EndKind.branch, x.body().end.kind);
        try x.check(&.{ &.{ .{ .bool_ = false }, .{ .int = 3 }, .{ .int = 5 } }, &.{ .{ .bool_ = true }, .{ .int = 3 }, .{ .int = 5 } } }, &.{ .{ .int = 25 }, .{ .int = 9 } });
    }
}

test "T2 and T3: if c { continue(a) }; continue(b) is Continue(Switch c) whichever arm exits, as the written else is" {
    // Sums, over i in 0..n, i where i < k and 1 otherwise.
    const Shape = enum { joined_true, joined_false, written_else };
    const eval = @import("eval.zig");
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var outs: [3][4]eval.Value = undefined;
    for (std.enums.values(Shape), &outs) |shape, *out| {
        var x: ExitCase = .{};
        x.start(null);
        defer x.f.deinit();
        const i64_ty = try x.f.types.intTy(.i64);
        x.row = try x.f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
        const zero = try x.f.b.litInt(i64_ty, 0);
        const lb = try x.f.b.openRegion(.loop_body, &.{ i64_ty, i64_ty });
        const i = Ref.regionParam(lb, 0);
        const acc = Ref.regionParam(lb, 1);
        const lt = try x.f.b.call(.i64, .is_lt, &.{ i, Ref.rowParam(1) });
        // The test either way round: c is i < k, or its negation i >= k.
        const c = if (shape == .joined_false) try x.f.b.call(.i64, .is_gte, &.{ i, Ref.rowParam(1) }) else lt;
        const exit_key: u32 = if (shape == .joined_false) 0 else 1;
        var arms: [2]RegionId = undefined;
        const join = if (shape == .written_else) RegionId.none else try x.f.b.reserveJoin(&.{});
        for (&arms, 0..) |*a, key| {
            a.* = try x.f.b.openArm(c, @intCast(key));
            if (key == exit_key) {
                try x.f.b.close(.{ .continue_ = &.{try x.f.b.call(.i64, .plus, &.{ acc, i })} });
            } else if (shape == .written_else) {
                try x.f.b.close(.{ .continue_ = &.{try x.f.b.call(.i64, .plus, &.{ acc, try x.f.b.litInt(i64_ty, 1) })} });
            } else try x.f.b.close(.{ .jump = .{ .join = join, .args = &.{} } });
        }
        if (shape == .written_else) {
            const sw = try x.f.b.exitingSwitch(c, &arms, &.{}, &.{});
            try x.f.b.close(.{ .branch = sw });
        } else {
            const sw = try x.f.b.exitingSwitch(c, &arms, &.{join}, &.{});
            try x.f.b.continueIn(sw, join);
            try x.f.b.close(.{ .continue_ = &.{try x.f.b.call(.i64, .plus, &.{ acc, try x.f.b.litInt(i64_ty, 1) })} });
            try testing.expectEqual(@as(u32, 1), x.fired(.t2));
        }
        try testing.expectEqual(@as(u32, 1), x.fired(.t3));
        const end = x.f.store.region(lb).end;
        try testing.expectEqual(ir.EndKind.continue_, end.kind);
        try testing.expect(x.valueSwitch(end) != null);
        const loop = try x.f.b.loopOf(.for_range, &.{ zero, Ref.rowParam(0), zero }, lb, &.{i64_ty});
        try x.f.b.endRow(.{ .value = &.{loop} });
        try verifyOk(&x.f);
        var e = try eval.Evaluator.init(arena.allocator(), &x.f.store, &x.f.types, .strict);
        for (out, [_]i256{ 0, 2, 5, 9 }) |*o, k| o.* = try e.run(x.row, &.{ .{ .int = 6 }, .{ .int = k } });
    }
    for (outs[1..]) |o| for (o, outs[0]) |a, b| try testing.expect(a.eql(b));
    try testing.expect(outs[0][1].eql(.{ .int = 0 + 1 + 4 }));
}

test "a row built while another is suspended is callable from it, and the suspended row's facts come back" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const bool_ty = try f.types.boolTy();
    const i64_ty = try f.types.intTy(.i64);
    const outer = try f.b.beginRow(&.{ bool_ty, i64_ty }, i64_ty);
    const arm0 = try f.b.openArm(Ref.rowParam(0), 0);
    try f.b.close(.{ .value = &.{Ref.rowParam(1)} });
    const arm1 = try f.b.openArm(Ref.rowParam(0), 1);
    const s = f.b.suspendRow();
    const inner = try f.b.beginRow(&.{i64_ty}, i64_ty);
    try testing.expectEqual(@as(?u32, null), f.b.knownKey(Ref.rowParam(0)));
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .times, &.{ Ref.rowParam(0), Ref.rowParam(0) })} });
    f.b.resumeRow(s);
    try testing.expectEqual(@as(?u32, 1), f.b.knownKey(Ref.rowParam(0)));
    const sq = try f.b.callRow(inner, &.{Ref.rowParam(1)});
    try f.b.close(.{ .value = &.{sq} });
    const sw = try f.b.switchOn(Ref.rowParam(0), &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{});
    try f.b.endRow(.{ .value = &.{sw} });
    try testing.expectEqual(outer, f.b.row);
    try verifyOk(&f);
    const eval = @import("eval.zig");
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var e = try eval.Evaluator.init(arena.allocator(), &f.store, &f.types, .strict);
    try testing.expect((try e.run(outer, &.{ .{ .bool_ = true }, .{ .int = 7 } })).eql(.{ .int = 49 }));
    try testing.expect((try e.run(outer, &.{ .{ .bool_ = false }, .{ .int = 7 } })).eql(.{ .int = 7 }));
}

test "N8c: a closure of a row that only calls another with its parameters is a closure of that one, and rules off keep it" {
    for ([_]bool{ false, true }) |off| {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        f.b.hooks.rules_off = off;
        const i64_ty = try f.types.intTy(.i64);
        const fn_ty = try f.types.funcTy(&.{ i64_ty, i64_ty }, i64_ty);
        const g = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
        try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .minus, &.{ Ref.rowParam(0), Ref.rowParam(1) })} });
        // |a, b| g(a, b)
        const eta = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
        try f.b.endRow(.{ .value = &.{try f.b.callRow(g, &.{ Ref.rowParam(0), Ref.rowParam(1) })} });
        // |a, b| g(b, a) calls g with its parameters out of order.
        const swapped = try f.b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
        try f.b.endRow(.{ .value = &.{try f.b.callRow(g, &.{ Ref.rowParam(1), Ref.rowParam(0) })} });
        _ = try f.b.beginRow(&.{}, fn_ty);
        const c = try f.b.closure(eta, &.{}, fn_ty);
        const d = try f.b.closure(swapped, &.{}, fn_ty);
        try f.b.endRow(.{ .value = &.{c} });
        const want = if (off) eta else g;
        try testing.expectEqual(want.index(), f.store.node(c.nodeId()).payload);
        try testing.expectEqual(swapped.index(), f.store.node(d.nodeId()).payload);
        try verifyOk(&f);
    }
}

test "N18b: a field of an input slot is a slot, and one projection written twice is one slot" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const bool_ty = try f.types.boolTy();
    const rec_ty = try f.types.recordTy(&.{ .{ .name = "x", .ty = i64_ty }, .{ .name = "y", .ty = bool_ty } });
    _ = try f.b.beginRow(&.{}, i64_ty);
    const whole = try f.b.input(rec_ty, 0);
    const x = try f.b.field(whole, 0);
    const x_again = try f.b.field(try f.b.input(rec_ty, 0), 0);
    try testing.expectEqual(Ref.Kind.input, x.kind);
    try testing.expectEqual(x, x_again);
    try testing.expect(x != whole);
    // The whole record and its field `x`: no node reads either.
    try testing.expectEqual(@as(usize, 2), f.store.slots.items.len);
    try testing.expectEqual(i64_ty, f.store.slots.items[x.slotId().index()].ty);
    try f.b.endRow(.{ .value = &.{x} });
}
