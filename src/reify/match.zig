//! N7a: decision trees, phase 1 (normal-form 3.7, plan 3.4).
//!
//! Phase 1 covers a `match` whose patterns are each one tag or literal at
//! the top, `if`, and `?`. The walk builds each of them as a first-match
//! cascade of switches on one scrutinee (`code_reifier.zig`, `matchFrom`).
//! The canonical tree of that cascade is made by the smart constructors,
//! during every rebuild, so a tree that appears only after inlining or
//! another rule is made canonical in the round that makes it:
//!
//! | Part of the canonical flat tree | Made by | Where |
//! |---|---|---|
//! | a tag switch has one arm per member of the union, in name order | the walk's `openTagArm`, one arm per member | `builder.zig`, `Builder.openTagArm` |
//! | a `Bool` switch has the arm of `False`, then the arm of `True`; `if` and a `match` on `Bool` are the same switch | the walk's `boolTest` | `code_reifier.zig` |
//! | a literal switch has its keys ascending, an integer by value and a string by its bytes, one arm per key, and one default arm | `Builder.litSwitch` sorts with `keyLess` and keeps the first arm of a repeated key | `builder.zig` |
//! | a default arm that is a literal switch on the same scrutinee merges into its parent (N7c) | `Builder.mergeDefault` | `builder.zig` |
//! | a switch on a position a dominating arm decided is that arm (N13c, N13d) | `Builder.decidedSwitch`, `Builder.litSwitch`, the `tag_arm` row | `builder.zig`, `rules/table.zig` |
//! | an equality test of a literal is a literal switch (N13n) | the `N13n` row over integers and `Str` | `rules/table.zig` |
//!
//! Two matches with the same mapping from inputs to arms therefore reach one
//! tree whatever the order of their arms: the order of the arms of a tag
//! switch is the union's, and the order of the keys of a literal switch is
//! `keyLess`. A `Try` is a two-member tag union, so `?` and the `match` it
//! means are one tree.
//!
//! This module holds what the other parts of phase 1 are checked against:
//!
//! | Check | Plan | Fails when |
//! |---|---|---|
//! | `check` | 5.2, "no smart-constructor rule applies" | a flat tree is not canonical: keys not ascending, a key twice, a key a dominating default arm excluded, or a switch that a dominating arm or a known tag decided |
//! | `check`, tree bound | 5.2, "no decision tree larger than the multiplier bound" | the arms of a cascade of switches outnumber `tree_multiplier` times its distinct tests plus `tree_base`, which is what a subtree copied into every arm does |
//!
//! Nested and overlapping patterns and guards are phase 2 (N7b), which is
//! not built.

const std = @import("std");
const ir = @import("ir.zig");
const types_mod = @import("types.zig");
const live_mod = @import("live.zig");
const polarity = @import("polarity.zig");
const verify = @import("verify.zig");

const Allocator = std.mem.Allocator;
const Ref = ir.Ref;
const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const LitId = ir.LitId;

/// The most arms a cascade of switches has per distinct test it makes, and
/// the arms it may have beyond that. A flat tree has one arm per test, and a
/// chain of `if`s one more arm than tests, so the bound leaves room for both
/// and fails a subtree copied into the arms of another switch.
pub const tree_multiplier: u32 = 2;
pub const tree_base: u32 = 2;

/// The integer value of an integer literal, by the signedness of its type.
/// `-1` at `I128` and the highest `U128` are one `u128` of bits; only the type
/// tells them apart.
pub fn litIntValue(types: *const types_mod.Types, lit: ir.Lit) ?i256 {
    const bits = switch (lit.value) {
        .int => |bits| bits,
        .bool_, .float, .str, .dec, .bytes => return null,
    };
    return if (types.get(lit.ty).int.signed()) @as(i128, @bitCast(bits)) else bits;
}

/// The order of the keys of a literal switch: integers by value, strings by
/// their bytes. Only integer and string literals key a switch.
pub fn keyLess(store: *const ir.Store, types: *const types_mod.Types, a: u32, b: u32) bool {
    const x = store.lit(LitId.of(a));
    const y = store.lit(LitId.of(b));
    return switch (x.value) {
        .int => litIntValue(types, x).? < litIntValue(types, y).?,
        .str => |sx| std.mem.order(u8, store.byteSlice(sx), store.byteSlice(y.value.str)) == .lt,
        .bool_, .float, .dec, .bytes => unreachable, // literal switch keys are integers or strings
    };
}

/// One step from a scrutinee's root toward the position a switch tests.
pub const Step = union(enum) {
    /// The backing of a nominal.
    unwrap,
    /// A record field or a tuple element, by its index in the type's order.
    field: u32,
    /// Payload `k` of the tag `name`.
    payload: struct { name: types_mod.NameId, k: u32 },
};

/// The root of the position `ref` reads and the steps from it: `ref` is
/// followed through `Field`, `Index`, `Payload` and `Unwrap` nodes, and the
/// first value it reaches that is none of them is the root. The steps are
/// appended outermost first.
pub fn positionOf(gpa: Allocator, store: *const ir.Store, ref: Ref, steps: *std.ArrayList(Step)) Allocator.Error!Ref {
    var at = ref;
    while (at.kind == .node) {
        const n = store.node(at.nodeId());
        const step: Step = switch (n.op) {
            .field, .index => .{ .field = n.payload },
            .payload => .{ .payload = .{ .name = types_mod.NameId.of(n.payload), .k = store.wordSlice(n.aux)[0] } },
            .unwrap => .unwrap,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .elem, .opt_field, .prim, .call, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => break,
        };
        try steps.append(gpa, step);
        at = store.refSlice(n.args)[0];
    }
    std.mem.reverse(Step, steps.items);
    return at;
}

fn stepOrder(types: *const types_mod.Types, a: Step, b: Step) std.math.Order {
    const rank = struct {
        fn of(x: Step) u8 {
            return switch (x) {
                .unwrap => 0,
                .field => 1,
                .payload => 2,
            };
        }
    };
    if (rank.of(a) != rank.of(b)) return std.math.order(rank.of(a), rank.of(b));
    return switch (a) {
        .unwrap => .eq,
        .field => |x| std.math.order(x, b.field),
        .payload => |x| switch (std.mem.order(u8, types.nameText(x.name), types.nameText(b.payload.name))) {
            .eq => std.math.order(x.k, b.payload.k),
            else => |o| o,
        },
    };
}

/// Whether the position `a` comes before `b` in the order of the canonical
/// tree (normal-form 3.7, rule 2): the outermost position first, and two
/// positions of one level by field index, then by tag name and payload index.
/// Both are paths from one root.
pub fn before(types: *const types_mod.Types, a: []const Step, b: []const Step) bool {
    for (a[0..@min(a.len, b.len)], b) |x, y| switch (stepOrder(types, x, y)) {
        .lt => return true,
        .gt => return false,
        .eq => {},
    };
    return a.len < b.len;
}

/// Whether two paths are the same position.
pub fn samePosition(types: *const types_mod.Types, a: []const Step, b: []const Step) bool {
    if (a.len != b.len) return false;
    for (a, b) |x, y| if (stepOrder(types, x, y) != .eq) return false;
    return true;
}

/// A tree a rule could still make canonical, or one that is too large.
pub const Kind = enum {
    /// The keys of a literal switch are not strictly ascending.
    keys_unordered,
    /// A key of a literal switch is one that a dominating default arm on the
    /// same scrutinee excluded.
    key_excluded,
    /// A dominating arm, or a known tag, decided the switch, and the arm it
    /// selects ends in a value.
    decided,
    /// The arms of a cascade outnumber the bound.
    too_large,
    /// An arm of a switch ends in a switch on an earlier position of the same
    /// root, which N7b would put first.
    not_hoisted,
    /// A switch on the output of a value switch whose arms all give a known
    /// tag or literal, and that nothing else reads, which N13r would move into
    /// the arms.
    not_case_of_case,

    fn text(self: Kind) []const u8 {
        return switch (self) {
            .keys_unordered => "the keys of a literal switch are not strictly ascending",
            .key_excluded => "a key of a literal switch is one a dominating default arm excluded",
            .decided => "a dominating arm or a known tag decided this switch",
            .too_large => "a decision tree is larger than the multiplier bound",
            .not_hoisted => "an arm ends in a switch on a position that comes before this switch's own",
            .not_case_of_case => "a switch tests a known tag or literal that only a value switch's arms give",
        };
    }
};

/// Check every live switch of `store`, which is in normal form: the rules
/// are on, and no rule applies to a flat tree (N7a). Every violation is a
/// compiler bug.
pub fn check(gpa: Allocator, store: *const ir.Store, types: *const types_mod.Types) Allocator.Error!verify.Report {
    var report: verify.Report = .{ .gpa = gpa };
    errdefer report.deinit();
    var live = try live_mod.ofStore(gpa, store);
    defer live.deinit(gpa);
    var c: Checker = .{ .gpa = gpa, .store = store, .types = types, .report = &report, .live = live };
    defer c.deinit();
    for (store.nodes.items(.op), 0..) |op, i| {
        if (op != .switch_ or !live.nodes[i]) continue;
        const id = NodeId.of(@intCast(i));
        try c.flat(id);
        try c.hoisted(id);
        try c.caseOfCase(id);
        if (!c.continues(id)) try c.bound(id);
    }
    return report;
}

/// The switch an arm ends in, when the arm ends in exactly its one output,
/// the switch has no joins, and its arms all end in a value (N7b).
fn topSwitch(store: *const ir.Store, arm: RegionId) ?NodeId {
    const end = store.region(arm).end;
    if (end.kind != .value) return null;
    const refs = store.refSlice(end.refs);
    if (refs.len != 1 or refs[0].kind != .node or refs[0].output != 0) return null;
    const id = refs[0].nodeId();
    const node = store.node(id);
    if (node.op != .switch_ or node.region != arm or node.tys.len != 1) return null;
    const regions = store.regionSlice(node.regions);
    if (regions.len != node.payload) return null;
    for (regions) |r| if (store.region(r).end.kind != .value) return null;
    return id;
}

// Whether the arms around `n` decided that `x` is the tag `name`.
fn tagKnown(store: *const ir.Store, types: *const types_mod.Types, n: NodeId, x: Ref, name: types_mod.NameId) bool {
    var r = store.node(n).region;
    while (true) {
        const region = store.region(r);
        if (region.owner == NodeId.none) return false;
        const owner = store.node(region.owner);
        if (owner.op == .switch_ and owner.aux.len == 0 and store.refSlice(owner.args)[0] == x) {
            const regions = store.regionSlice(owner.regions);
            if (std.mem.findScalar(RegionId, regions[0..owner.payload], r)) |i| {
                const ty = store.refTy(store.region(r).row, x);
                if (types.get(ty) == .tag_union and types.memberSlice(types.get(ty).tag_union)[i].name == name) return true;
            }
        }
        r = region.parent;
    }
}

// Whether the position `q` can be read where `n` stands: its root is visible
// there, and every payload on the way is of a tag the arms around `n` decided.
fn readable(store: *const ir.Store, types: *const types_mod.Types, n: NodeId, q: Ref) bool {
    var at = q;
    while (at.kind == .node) {
        const node = store.node(at.nodeId());
        const arg = store.refSlice(node.args);
        switch (node.op) {
            .field, .index, .unwrap => {},
            .payload => if (!tagKnown(store, types, n, arg[0], types_mod.NameId.of(node.payload))) return false,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .elem, .opt_field, .prim, .call, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => break,
        }
        at = arg[0];
    }
    const here = store.node(n).region;
    return switch (at.kind) {
        .row_param, .input => true,
        .region_param => store.encloses(at.regionId(), here),
        .node => store.encloses(store.node(at.nodeId()).region, here),
    };
}

/// Whether the arm `arm` holds no loop, `Apply`, `Lambda` or `Closure`: N7b
/// copies arms, and the measure counts those nodes before it counts the
/// switches a copy adds, so an arm with one is never copied.
pub fn copyable(store: *const ir.Store, live: ?[]const bool, arm: RegionId) bool {
    const ops = store.nodes.items(.op);
    const regions = store.nodes.items(.region);
    for (ops, regions, 0..) |op, at, i| {
        if (live) |l| if (!l[i]) continue;
        if (!store.encloses(arm, at)) continue;
        if (op.isLoop() or op == .apply or op == .lambda or op == .closure) return false;
    }
    return true;
}

/// How many arms of the single-output value switch `n` end in a switch on a
/// position of the same root that comes before its own, which N7b hoists
/// (normal-form 3.7). Two `Bool` switches are not counted: N7d and N13o own
/// their order.
pub fn inversions(gpa: Allocator, store: *const ir.Store, types: *const types_mod.Types, live: ?[]const bool, n: NodeId) Allocator.Error!u32 {
    const node = store.node(n);
    if (node.op != .switch_) return 0;
    const arms = store.regionSlice(node.regions);
    if (node.tys.len != 1 or arms.len != node.payload) return 0;
    for (arms) |a| if (store.region(a).end.kind != .value) return 0;
    for (arms) |a| if (!copyable(store, live, a)) return 0;
    const row = store.region(node.region).row;
    const p = store.refSlice(node.args)[0];
    var p_steps: std.ArrayList(Step) = .empty;
    defer p_steps.deinit(gpa);
    const p_root = try positionOf(gpa, store, p, &p_steps);
    const p_is_bool = types.get(store.refTy(row, p)) == .bool_;
    var steps: std.ArrayList(Step) = .empty;
    defer steps.deinit(gpa);
    var count: u32 = 0;
    for (arms) |a| {
        const inner = topSwitch(store, a) orelse continue;
        const q = store.refSlice(store.node(inner).args)[0];
        steps.clearRetainingCapacity();
        const root = try positionOf(gpa, store, q, &steps);
        const q_is_bool = types.get(store.refTy(row, q)) == .bool_;
        if (root != p_root or !before(types, steps.items, p_steps.items) or (p_is_bool and q_is_bool)) continue;
        if (readable(store, types, n, q)) count += 1;
    }
    return count;
}

const Checker = struct {
    gpa: Allocator,
    store: *const ir.Store,
    types: *const types_mod.Types,
    report: *verify.Report,
    live: live_mod.Live,
    pairs: std.AutoHashMapUnmanaged(Pair, void) = .empty,

    const Pair = struct { scrutinee: Ref, arm: u32 };

    fn deinit(self: *Checker) void {
        self.pairs.deinit(self.gpa);
    }

    fn fail(self: *Checker, node: NodeId, kind: Kind) Allocator.Error!void {
        try self.report.add("n{d}: {s}", .{ node.index(), kind.text() });
    }

    // What the arms around `n` decided about its scrutinee: the arm of a
    // tag or `Bool` switch on it, the key of a literal switch on it, and the
    // keys the default arms of literal switches on it excluded.
    const Known = struct {
        arm: ?u32 = null,
        lit_arm: ?u32 = null,
        excluded: std.ArrayList(u32) = .empty,

        fn deinit(self: *Known, gpa: Allocator) void {
            self.excluded.deinit(gpa);
        }
    };

    fn known(self: *Checker, n: NodeId) Allocator.Error!Known {
        const node = self.store.node(n);
        const x = self.store.refSlice(node.args)[0];
        var out: Known = .{};
        errdefer out.deinit(self.gpa);
        var r = node.region;
        while (true) {
            const region = self.store.region(r);
            if (region.owner == NodeId.none) break;
            const owner = self.store.node(region.owner);
            if (owner.op == .switch_ and self.store.refSlice(owner.args)[0] == x) {
                const regions = self.store.regionSlice(owner.regions);
                const at = std.mem.findScalar(RegionId, regions[0..owner.payload], r);
                if (at) |i| {
                    const keys = self.store.wordSlice(owner.aux);
                    if (keys.len == 0) {
                        if (out.arm == null) out.arm = @intCast(i);
                    } else if (i < keys.len) {
                        if (out.lit_arm == null) out.lit_arm = keys[i];
                    } else try out.excluded.appendSlice(self.gpa, keys);
                }
            }
            r = region.parent;
        }
        return out;
    }

    // A switch whose arms are all values, one output, and no joins is the
    // switch the decided rules read.
    fn selectsValue(self: *Checker, node: ir.Node, arm: u32) bool {
        if (node.tys.len != 1) return false;
        const regions = self.store.regionSlice(node.regions);
        if (regions.len != node.payload or arm >= regions.len) return false;
        return polarity.armValue(self.store, regions[arm]) != null;
    }

    fn flat(self: *Checker, n: NodeId) Allocator.Error!void {
        const node = self.store.node(n);
        const keys = self.store.wordSlice(node.aux);
        var k = try self.known(n);
        defer k.deinit(self.gpa);
        if (keys.len > 0) {
            for (keys[1..], keys[0 .. keys.len - 1]) |b, a| {
                if (!keyLess(self.store, self.types, a, b)) {
                    try self.fail(n, .keys_unordered);
                    break;
                }
            }
            for (keys) |key| {
                if (std.mem.findScalar(u32, k.excluded.items, key) != null) {
                    try self.fail(n, .key_excluded);
                    break;
                }
            }
            if (k.lit_arm) |l| {
                const i = std.mem.findScalar(u32, keys, l) orelse keys.len;
                if (self.selectsValue(node, @intCast(i))) try self.fail(n, .decided);
            }
            return;
        }
        if (k.arm) |a| {
            if (self.selectsValue(node, a)) try self.fail(n, .decided);
            return;
        }
        // A tag the code just built selects its arm when every arm is a value.
        const x = self.store.refSlice(node.args)[0];
        if (x.kind != .node) return;
        const scrutinee = self.store.node(x.nodeId());
        if (scrutinee.op != .tag) return;
        const ty = self.store.tySlice(scrutinee.tys)[0];
        const arm = self.types.memberIndex(ty, types_mod.NameId.of(scrutinee.payload)) orelse return;
        if (self.selectsValue(node, arm)) try self.fail(n, .decided);
    }

    // Whether `n` is the switch that an arm of another switch ends in, as the
    // cascade of an `if` chain or a `match` is built.
    fn continues(self: *Checker, n: NodeId) bool {
        const node = self.store.node(n);
        const region = self.store.region(node.region);
        if (region.owner == NodeId.none) return false;
        const owner = self.store.node(region.owner);
        if (owner.op != .switch_) return false;
        const regions = self.store.regionSlice(owner.regions);
        if (std.mem.findScalar(RegionId, regions[0..owner.payload], node.region) == null) return false;
        return self.endsIn(node.region, n);
    }

    // Whether region `r` ends in the outputs of switch `n`.
    fn endsIn(self: *Checker, r: RegionId, n: NodeId) bool {
        const end = self.store.region(r).end;
        if (end.kind != .value) return false;
        const refs = self.store.refSlice(end.refs);
        if (refs.len == 0) return false;
        for (refs, 0..) |ref, k| {
            if (ref.kind != .node or ref.nodeId() != n or @as(usize, ref.output) != k) return false;
        }
        return true;
    }

    // N7b: no arm of a single-output value switch ends in a switch on a
    // position that comes before its own, unless both switch on a `Bool`.
    fn hoisted(self: *Checker, n: NodeId) Allocator.Error!void {
        if (try inversions(self.gpa, self.store, self.types, self.live.nodes, n) > 0) try self.fail(n, .not_hoisted);
    }

    // N13r: a switch on the output of a value switch in its region, whose
    // arms each give a different known tag or literal, and which only this
    // switch and its arms read, is that value switch with the outer arms in
    // its arms.
    fn caseOfCase(self: *Checker, n: NodeId) Allocator.Error!void {
        const node = self.store.node(n);
        const outer_t = self.store.refSlice(node.args)[0];
        var t = outer_t;
        var depth: u32 = 0;
        while (t.kind == .node) {
            const t_node = self.store.node(t.nodeId());
            if (t_node.op != .unwrap) break;
            t = self.store.refSlice(t_node.args)[0];
            depth += 1;
        }
        if (t.kind != .node or t.output != 0) return;
        const inner_id = t.nodeId();
        const inner = self.store.node(inner_id);
        if (inner.op != .switch_ or inner.region != node.region or inner.tys.len != 1) return;
        const inner_arms = self.store.regionSlice(inner.regions);
        if (inner_arms.len != inner.payload) return;
        const joins = self.store.regionSlice(node.regions)[node.payload..];
        if (node.tys.len > 0 and joins.len != 0) return;
        if (node.tys.len == 0 and joins.len > 1) return;
        const t_ty = self.store.refTy(self.store.region(node.region).row, outer_t);
        var selected: std.ArrayList(u32) = .empty;
        defer selected.deinit(self.gpa);
        for (inner_arms) |arm| {
            var v = polarity.armValue(self.store, arm) orelse return;
            for (0..depth) |_| {
                if (v.kind != .node) return;
                const w = self.store.node(v.nodeId());
                if (w.op != .wrap) return;
                v = self.store.refSlice(w.args)[0];
            }
            if (v.kind != .node) return;
            const known_node = self.store.node(v.nodeId());
            const at: u32 = switch (known_node.op) {
                .tag => self.types.memberIndex(t_ty, types_mod.NameId.of(known_node.payload)) orelse return,
                .lit => switch (self.store.lit(LitId.of(known_node.payload)).value) {
                    .bool_ => |b| @intFromBool(b),
                    .int, .str => @intCast(std.mem.findScalar(u32, self.store.wordSlice(node.aux), known_node.payload) orelse node.aux.len),
                    .float, .dec, .bytes => return,
                },
                .crash, .derived, .record, .tuple, .list, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => return,
            };
            if (std.mem.findScalar(u32, selected.items, at) != null) return;
            try selected.append(self.gpa, at);
        }
        if (node.tys.len > 0) {
            for (self.store.regionSlice(node.regions)[0..node.payload]) |r| if (polarity.armValue(self.store, r) == null) return;
        }
        // Nothing else reads the value switch or the unwraps after it.
        if (!try self.soleReader(n, outer_t)) return;
        try self.fail(n, .not_case_of_case);
    }

    // Whether every live reader of the chain of `Unwrap`s that leads from
    // `outer_t` to a switch output is `n`, a node inside `n`'s regions, or the
    // next `Unwrap` of the chain.
    fn soleReader(self: *Checker, n: NodeId, outer_t: Ref) Allocator.Error!bool {
        const arms = self.store.regionSlice(self.store.node(n).regions);
        var t = outer_t;
        var next = n;
        while (t.kind == .node) {
            const target = t.nodeId();
            for (self.store.nodes.items(.args), 0..) |args, i| {
                const reader = NodeId.of(@intCast(i));
                if (!self.live.nodes[i] or reader == next or reader == n) continue;
                for (self.store.refSlice(args)) |a| {
                    if (a.kind != .node or a.nodeId() != target) continue;
                    if (!self.within(arms, self.store.node(reader).region)) return false;
                }
            }
            for (self.store.regions.items(.end), 0..) |end, i| {
                if (!self.live.regions[i]) continue;
                for (self.store.refSlice(end.refs)) |a| {
                    if (a.kind != .node or a.nodeId() != target) continue;
                    if (!self.within(arms, RegionId.of(@intCast(i)))) return false;
                }
            }
            const node = self.store.node(target);
            if (node.op != .unwrap) return true;
            next = target;
            t = self.store.refSlice(node.args)[0];
        }
        return true;
    }

    fn within(self: *Checker, arms: []const RegionId, r: RegionId) bool {
        for (arms) |arm| if (self.store.encloses(arm, r)) return true;
        return false;
    }

    // The arms of the cascade rooted at `root` against its distinct tests.
    fn bound(self: *Checker, root: NodeId) Allocator.Error!void {
        self.pairs.clearRetainingCapacity();
        var arms: u32 = 0;
        try self.walk(root, &arms);
        const tests: u32 = @intCast(self.pairs.count());
        if (arms > tree_multiplier * tests + tree_base) try self.fail(root, .too_large);
    }

    fn walk(self: *Checker, n: NodeId, arms: *u32) Allocator.Error!void {
        const node = self.store.node(n);
        const x = self.store.refSlice(node.args)[0];
        const regions = self.store.regionSlice(node.regions)[0..node.payload];
        arms.* += node.payload;
        for (regions, 0..) |r, i| {
            try self.pairs.put(self.gpa, .{ .scrutinee = x, .arm = @intCast(i) }, {});
            const end = self.store.region(r).end;
            if (end.kind != .value) continue;
            const refs = self.store.refSlice(end.refs);
            if (refs.len == 0 or refs[0].kind != .node) continue;
            const inner = refs[0].nodeId();
            const inner_node = self.store.node(inner);
            if (inner_node.op != .switch_ or inner_node.region != r or !self.endsIn(r, inner)) continue;
            try self.walk(inner, arms);
        }
    }
};

const testing = std.testing;
const builder_mod = @import("builder.zig");
const Builder = builder_mod.Builder;

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

    // A literal switch on `x` over `keys` with the `values` for its arms, the
    // default last. With the rules off the switch is built as written.
    fn litSwitch(self: *Fixture, x: Ref, keys: []const i128, values: []const Ref) !Ref {
        const ty = try self.types.intTy(.i64);
        var ids: [8]u32 = undefined;
        for (keys, ids[0..keys.len]) |k, *id| id.* = (try self.b.internLit(ty, .{ .int = @bitCast(k) })).index();
        var arms: [9]RegionId = undefined;
        for (values, 0..) |v, i| {
            arms[i] = try self.b.openLitArm(x, ids[0..keys.len], @intCast(i));
            try self.b.close(.{ .value = &.{v} });
        }
        return self.b.switchOn(x, arms[0..values.len], &.{}, &.{ty}, ids[0..keys.len]);
    }

    fn boolSwitch(self: *Fixture, x: Ref, f: Ref, t: Ref) !Ref {
        const ty = try self.types.intTy(.i64);
        const a0 = try self.b.openArm(x, 0);
        try self.b.close(.{ .value = &.{f} });
        const a1 = try self.b.openArm(x, 1);
        try self.b.close(.{ .value = &.{t} });
        return self.b.switchOn(x, &.{ a0, a1 }, &.{}, &.{ty}, &.{});
    }

    fn violations(self: *Fixture) !usize {
        var report = try check(testing.allocator, &self.store, &self.types);
        defer report.deinit();
        return report.messages.items.len;
    }
};

test "N7a: a literal switch built as written has unordered keys, and the builder's smart constructor makes them canonical" {
    inline for (.{ true, false }) |off| {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        const i64_ty = try f.types.intTy(.i64);
        _ = try f.b.beginRow(&.{ i64_ty, i64_ty, i64_ty, i64_ty, i64_ty }, i64_ty);
        f.b.hooks.rules_off = off;
        const p = Ref.rowParam;
        const sw = try f.litSwitch(p(0), &.{ 3, 1, 2 }, &.{ p(1), p(2), p(3), p(4) });
        try f.b.endRow(.{ .value = &.{sw} });
        // The knockout: with the rules off the keys stay as written.
        try testing.expectEqual(@as(usize, if (off) 1 else 0), try f.violations());
    }
}

test "N7a: a repeated key is not canonical" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    _ = try f.b.beginRow(&.{ i64_ty, i64_ty, i64_ty, i64_ty }, i64_ty);
    f.b.hooks.rules_off = true;
    const p = Ref.rowParam;
    const twice = try f.litSwitch(p(0), &.{ 1, 1 }, &.{ p(1), p(2), p(3) });
    try f.b.endRow(.{ .value = &.{twice} });
    try testing.expectEqual(@as(usize, 1), try f.violations());
}

test "N7a: a key a dominating default arm excluded is not canonical, and with the rules on the key is dropped" {
    inline for (.{ true, false }) |off| {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        const i64_ty = try f.types.intTy(.i64);
        _ = try f.b.beginRow(&.{ i64_ty, i64_ty, i64_ty, i64_ty }, i64_ty);
        f.b.hooks.rules_off = off;
        const p = Ref.rowParam;
        // switch x { 1: p1, _: switch x { 1: p2, 2: p3, _: p1 } }
        const one = (try f.b.internLit(i64_ty, .{ .int = 1 })).index();
        const two = (try f.b.internLit(i64_ty, .{ .int = 2 })).index();
        const a0 = try f.b.openLitArm(p(0), &.{one}, 0);
        try f.b.close(.{ .value = &.{p(1)} });
        const a1 = try f.b.openLitArm(p(0), &.{one}, 1);
        const b0 = try f.b.openLitArm(p(0), &.{ one, two }, 0);
        try f.b.close(.{ .value = &.{p(2)} });
        const b1 = try f.b.openLitArm(p(0), &.{ one, two }, 1);
        try f.b.close(.{ .value = &.{p(3)} });
        const b2 = try f.b.openLitArm(p(0), &.{ one, two }, 2);
        try f.b.close(.{ .value = &.{p(1)} });
        const inner = try f.b.switchOn(p(0), &.{ b0, b1, b2 }, &.{}, &.{i64_ty}, &.{ one, two });
        try f.b.close(.{ .value = &.{inner} });
        const outer = try f.b.switchOn(p(0), &.{ a0, a1 }, &.{}, &.{i64_ty}, &.{one});
        try f.b.endRow(.{ .value = &.{outer} });
        try testing.expect(off == ((try f.violations()) > 0));
    }
}

test "N7a: a switch a dominating arm decided is not canonical, and with the rules on it is the arm" {
    inline for (.{ true, false }) |off| {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        const i64_ty = try f.types.intTy(.i64);
        const bool_ty = try f.types.boolTy();
        _ = try f.b.beginRow(&.{ bool_ty, i64_ty, i64_ty }, i64_ty);
        f.b.hooks.rules_off = off;
        const p = Ref.rowParam;
        // if c { if c p1 else p2 } else p2
        const a0 = try f.b.openArm(p(0), 0);
        try f.b.close(.{ .value = &.{p(2)} });
        const a1 = try f.b.openArm(p(0), 1);
        const inner = try f.boolSwitch(p(0), p(2), p(1));
        try f.b.close(.{ .value = &.{inner} });
        const outer = try f.b.switchOn(p(0), &.{ a0, a1 }, &.{}, &.{i64_ty}, &.{});
        try f.b.endRow(.{ .value = &.{outer} });
        try testing.expectEqual(@as(usize, if (off) 1 else 0), try f.violations());
    }
}

test "N7a: the tree bound passes a small tree and fails a subtree copied into every arm" {
    // A complete tree over distinct positions with a distinct leaf on each
    // path: depth d has 2^(d+1) - 2 arms and 2d distinct tests.
    const Tree = struct {
        fn build(fx: *Fixture, depth: u32, max: u32, leaf: *i128) !Ref {
            const ty = try fx.types.intTy(.i64);
            if (depth == max) {
                leaf.* += 1;
                return fx.b.litInt(ty, leaf.*);
            }
            const a0 = try fx.b.openArm(Ref.rowParam(@intCast(depth)), 0);
            const l = try build(fx, depth + 1, max, leaf);
            try fx.b.close(.{ .value = &.{l} });
            const a1 = try fx.b.openArm(Ref.rowParam(@intCast(depth)), 1);
            const r = try build(fx, depth + 1, max, leaf);
            try fx.b.close(.{ .value = &.{r} });
            return fx.b.switchOn(Ref.rowParam(@intCast(depth)), &.{ a0, a1 }, &.{}, &.{ty}, &.{});
        }
    };
    for ([_]struct { depth: u32, bad: usize }{ .{ .depth = 1, .bad = 0 }, .{ .depth = 2, .bad = 0 }, .{ .depth = 3, .bad = 0 }, .{ .depth = 4, .bad = 1 }, .{ .depth = 5, .bad = 1 } }) |c| {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        const i64_ty = try f.types.intTy(.i64);
        const bool_ty = try f.types.boolTy();
        _ = try f.b.beginRow(&.{ bool_ty, bool_ty, bool_ty, bool_ty, bool_ty }, i64_ty);
        f.b.hooks.rules_off = true;
        var leaf: i128 = 0;
        const tree = try Tree.build(&f, 0, c.depth, &leaf);
        try f.b.endRow(.{ .value = &.{tree} });
        try testing.expectEqual(c.bad, try f.violations());
    }
}
