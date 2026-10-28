//! Layer L (normal-form 3.16; plan 3.4): the laws of the builtin library, in
//! force only at a site that opts in by its declared type, `Code.Lawful(f)`.
//!
//! | Step | From | To | Here |
//! |---|---|---|---|
//! | N16a | `ForList(xs, [])` whose every turn is `Continue(List.append(s, v))` | `List.map(xs, Closure(g))`, `g` the row of `v` | `raise`, applied by `rebuild.zig` |
//! | N16b | `ForList(xs, [])` whose every turn is `Continue` of a `Bool` switch with `s` in one arm and `List.append(s, x)` in the other | `List.keep_if(xs, Closure(p))`, `p` the row of the test | `raise`, applied by `rebuild.zig` |
//! | N16c | `List.fold(xs, init, Closure(f))` | `ForList(xs, init)` whose turn is `Continue` of `f`'s body over `captures ++ [s, x]` | `prim` |
//! | N16d | `List.map(List.map(xs, Closure(f)), Closure(g))`, the inner list read nowhere else | `List.map(xs, Closure(h))`, `h` a row of `g`'s body over `f`'s body | `prim` |
//! | N16e | `Iter.collect(Iter.map(List.iter(xs), f))` into a `List` | `List.map(xs, f)` | `prim` |
//! | N16f | `is_eq(List.len(xs), 0)`, `is_lte(List.len(xs), 0)`, `is_lt(0, List.len(xs))`; `switch List.len(xs) { 0 => t, _ => f }` | `List.is_empty(xs)`, `Bool.not(List.is_empty(xs))`; `switch List.is_empty(xs) { False => f, True => t }` | `prim`, `lenSwitchToEmpty` |
//!
//! Each law is an equation about a builtin's semantics in `Builtin.roc`, exact
//! under Roc's strict evaluation and C2 (normal-form 1.1). Its side
//! conditions are stated where it is matched. A loop or a call that matches
//! is rewritten every time, and one that does not is never rewritten.
//!
//! The row a law builds is simplified and finalized on the spot, before the
//! closure that names it, as a specialization is (N8i): the driver does it
//! through `Builder.laws`. A row a closure names takes its captured values
//! first and the function's own parameters after them, so where finalize
//! orders the row's parameters otherwise, the closure names a row that keeps
//! that convention (`rows.Finalizer.conventionRow`), as the walk's lambdas do.

const std = @import("std");
const ir = @import("ir.zig");
const prims = @import("prims.zig");
const types_mod = @import("types.zig");
const place = @import("place.zig");
const builder_mod = @import("builder.zig");

const Allocator = std.mem.Allocator;
const Ref = ir.Ref;
const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const RowId = ir.RowId;
const TyId = ir.TyId;
const Types = types_mod.Types;
const Builder = builder_mod.Builder;
const NodeSpec = builder_mod.NodeSpec;

/// The steps of layer L, for the normal-form fingerprint.
pub const steps = [_][]const u8{
    "N16a: ForList over [] appending one value per turn is List.map",
    "N16b: ForList over [] appending its element under a Bool test is List.keep_if",
    "N16c: List.fold with a known function is ForList calling it",
    "N16d: List.map of List.map read once is one List.map of a row calling both",
    "N16e: Iter.collect into a List of Iter.map of List.iter is List.map",
    "N16f: is_eq(List.len(xs), 0) and is_lte(List.len(xs), 0) are List.is_empty(xs), is_lt(0, List.len(xs)) its negation, and a literal switch on List.len(xs) with the one key 0 a Bool switch on List.is_empty(xs)",
    "rows of layer L: the cone of the loop body, with constants and the speculatable nodes only it reads",
};

/// Which raising law a loop matches.
pub const Law = enum { map, keep_if };

/// A loop that N16a or N16b raises: what the row of its function computes,
/// and from what. Every ref is in the old row; the rebuild maps them.
pub const Raise = struct {
    law: Law,
    /// The list the loop runs over.
    list: Ref,
    /// The body parameter that is the element.
    elem: Ref,
    /// The value the row gives: the appended value (N16a) or the test (N16b).
    value: Ref,
    /// N16b: the append stands in the `False` arm, so the row gives the
    /// negation of the test.
    negate: bool,
    /// The nodes of the loop body the value reads, which the row copies.
    cone: std.AutoHashMapUnmanaged(NodeId, void),
    /// The nodes outside the loop that the row copies, in the plan's order:
    /// constants, and speculatable nodes only the row reads.
    pre: []const NodeId,
    /// The values outside the loop the row reads, in the order the cone
    /// meets them: the closure's captures, and the row's first parameters.
    holes: []const Ref,
    /// The element type, the row's own parameter.
    elem_ty: TyId,
    /// The row's result: the mapped element's type, or `Bool`.
    result_ty: TyId,
    /// The type of the closure, `elem -> result`.
    fn_ty: TyId,
    /// The loop's one output, which the builtin call gives.
    out_ty: TyId,
};

/// N16a and N16b: whether the `ForList` `n` of `p`'s row raises, and how.
///
/// The conditions, all exact:
/// - one slot, starting at `[]`, and one output: the loop's value is the list it builds;
/// - the body ends in `Continue` with no exiting switch, so every turn runs to
///   its end, and no turn ends the loop or the row;
/// - N16a: the next value is `List.append(s, v)`, and the slot `s` is read by
///   that append alone, so each turn appends `v` once to the list so far;
/// - N16b: the next value is a single-output `Bool` switch without joins, one
///   arm giving `s` and computing nothing, the other giving
///   `List.append(s, x)` of the element `x` and computing nothing else, and
///   `s` read by these two alone;
/// - neither the value nor the test reads the index or the slot, so it is a
///   function of the element and of values defined before the loop.
///
/// Under these the loop calls the function once per element, first to last,
/// as `List.map` and `List.keep_if` do (`Builtin.roc`), so a crash in it
/// happens at the same element on both sides.
pub fn raise(a: Allocator, p: *const place.Plan, types: *Types, n: NodeId) Allocator.Error!?Raise {
    const store = p.store;
    const nd = store.node(n);
    if (nd.op != .for_list) return null;
    const args = store.refSlice(nd.args);
    if (args.len != 2 or nd.tys.len != 1) return null;
    const row = store.region(nd.region).row;
    if (!isEmptyList(store, args[1])) return null;
    const body = store.regionSlice(nd.regions)[0];
    const end = store.region(body).end;
    if (end.kind != .continue_ or end.refs.len != 1) return null;
    const next = store.refSlice(end.refs)[0];
    const index = Ref.regionParam(body, 0);
    const elem = Ref.regionParam(body, 1);
    const slot = Ref.regionParam(body, 2);
    const list_ty = store.refTy(row, args[0]);
    const elem_ty = switch (types.get(list_ty)) {
        .list => |e| e,
        .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .nominal, .func, .opaque_, .recursive => return null,
    };
    const out_ty = store.tySlice(nd.tys)[0];
    const out_elem = switch (types.get(out_ty)) {
        .list => |e| e,
        .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .nominal, .func, .opaque_, .recursive => return null,
    };
    if (readsOf(p, index) != 0) return null;
    if (next.kind != .node) return null;
    const m = next.nodeId();
    if (!own(p, m) or !inLoop(p, p.info.get(m).?.place, body)) return null;
    const mn = store.node(m);
    if (isAppend(mn)) {
        // N16a.
        const append_args = store.refSlice(mn.args);
        if (append_args[0] != slot or readsOf(p, slot) != 1) return null;
        const value = append_args[1];
        var cone = (try Cone.of(a, p, body, value)) orelse return null;
        return .{
            .law = .map,
            .list = args[0],
            .elem = elem,
            .value = value,
            .negate = false,
            .cone = cone.nodes,
            .pre = try cone.preInOrder(),
            .holes = cone.holes.items,
            .elem_ty = elem_ty,
            .result_ty = out_elem,
            .fn_ty = try types.funcTy(&.{elem_ty}, out_elem),
            .out_ty = out_ty,
        };
    }
    // N16b.
    if (mn.op != .switch_ or mn.tys.len != 1 or mn.aux.len != 0 or mn.payload != 2) return null;
    const arms = store.regionSlice(mn.regions);
    if (arms.len != 2 or next.output != 0) return null;
    const scrutinee = store.refSlice(mn.args)[0];
    const bool_ty = try types.boolTy();
    if (store.refTy(row, scrutinee) != bool_ty) return null;
    if (out_ty != list_ty) return null;
    const kept_at: usize = for (arms, 0..) |arm, i| {
        if (keepsElement(p, arm, slot, elem)) break i;
    } else return null;
    const other = arms[1 - kept_at];
    const other_end = store.region(other).end;
    if (other_end.kind != .value or store.refSlice(other_end.refs)[0] != slot or p.membersOf(other).len != 0) return null;
    if (readsOf(p, slot) != 2) return null;
    var cone = (try Cone.of(a, p, body, scrutinee)) orelse return null;
    return .{
        .law = .keep_if,
        .list = args[0],
        .elem = elem,
        .value = scrutinee,
        // The arms are in name order, `False` first.
        .negate = kept_at == 0,
        .cone = cone.nodes,
        .pre = try cone.preInOrder(),
        .holes = cone.holes.items,
        .elem_ty = elem_ty,
        .result_ty = bool_ty,
        .fn_ty = try types.funcTy(&.{elem_ty}, bool_ty),
        .out_ty = out_ty,
    };
}

// Whether `arm` gives `List.append(slot, elem)` and computes nothing else.
fn keepsElement(p: *const place.Plan, arm: RegionId, slot: Ref, elem: Ref) bool {
    const store = p.store;
    const end = store.region(arm).end;
    if (end.kind != .value or end.refs.len != 1) return false;
    const v = store.refSlice(end.refs)[0];
    if (v.kind != .node) return false;
    const members = p.membersOf(arm);
    if (members.len != 1 or members[0] != v.nodeId() or !own(p, v.nodeId())) return false;
    const nd = store.node(v.nodeId());
    if (!isAppend(nd)) return false;
    const args = store.refSlice(nd.args);
    return args[0] == slot and args[1] == elem;
}

fn isAppend(nd: ir.Node) bool {
    if (nd.op != .prim) return false;
    const p = prims.lookup(ir.PrimId.of(nd.payload)) orelse return false;
    return p.owner == .list and p.method == .append;
}

// Whether `ref` is the empty list `[]`.
fn isEmptyList(store: *const ir.Store, ref: Ref) bool {
    if (ref.kind != .node) return false;
    const nd = store.node(ref.nodeId());
    return nd.op == .list and nd.args.len == 0;
}

// Whether node `n` is built as itself: no other node merges into it and it
// merges into no other (N5c), so its uses are the ones the plan lists.
fn own(p: *const place.Plan, n: NodeId) bool {
    const info = p.info.get(n) orelse return false;
    if (info.alias != n or info.merged) return false;
    var it = p.info.constIterator();
    while (it.next()) |e| if (e.key_ptr.* != n and e.value_ptr.alias == n) return false;
    return true;
}

// Whether region `r`, as the plan places it, is `body` or inside it.
fn inLoop(p: *const place.Plan, r: RegionId, body: RegionId) bool {
    var at = r;
    while (at != RegionId.none) {
        if (at == body) return true;
        at = p.parentOf(at);
    }
    return false;
}

// How many times the nodes the plan reaches, and the ends of its regions,
// read `ref`.
fn readsOf(p: *const place.Plan, ref: Ref) u32 {
    const store = p.store;
    var count: u32 = 0;
    var nodes = p.info.constKeyIterator();
    while (nodes.next()) |n| {
        for (store.refSlice(store.node(n).args)) |arg| {
            if (arg == ref) count += 1;
        }
    }
    for (p.regions.items) |r| {
        for (store.refSlice(store.region(r).end.refs)) |arg| {
            if (arg == ref) count += 1;
        }
    }
    return count;
}

// The cone of a value in a loop body: the nodes inside the loop it reads,
// the nodes outside it the row copies, and the values outside it the row
// reads as parameters.
const Cone = struct {
    a: Allocator,
    p: *const place.Plan,
    body: RegionId,
    nodes: std.AutoHashMapUnmanaged(NodeId, void) = .empty,
    pre: std.AutoHashMapUnmanaged(NodeId, void) = .empty,
    holes: std.ArrayList(Ref) = .empty,
    /// Outside nodes met, in the order met, before deciding what each is.
    outside: std.ArrayList(NodeId) = .empty,

    // The cone of `value`, or null where it reads the index or the slot.
    fn of(a: Allocator, p: *const place.Plan, body: RegionId, value: Ref) Allocator.Error!?Cone {
        var c: Cone = .{ .a = a, .p = p, .body = body };
        if (!try c.reach(value)) return null;
        try c.settle();
        return c;
    }

    // Walk what `ref` reads. Returns false where the cone reads the index or
    // the slot of the loop.
    fn reach(c: *Cone, ref: Ref) Allocator.Error!bool {
        var stack: std.ArrayList(Ref) = .empty;
        try stack.append(c.a, ref);
        while (stack.pop()) |r| switch (r.kind) {
            .row_param, .input => try c.hole(r),
            .region_param => {
                const region = r.regionId();
                if (region == c.body) {
                    // The element is the row's own parameter; the index and the slot are not read.
                    if (r.output != 1) return false;
                } else if (!c.inside(region)) try c.hole(r);
            },
            .node => {
                const n = r.nodeId();
                if (c.nodes.contains(n) or c.pre.contains(n)) continue;
                const info = c.p.info.get(n) orelse return false;
                if (inLoop(c.p, info.place, c.body)) {
                    if (!own(c.p, n)) return false;
                    try c.nodes.put(c.a, n, {});
                    try c.pushReads(&stack, n);
                } else if (std.mem.findScalar(NodeId, c.outside.items, n) == null) {
                    try c.outside.append(c.a, n);
                }
            },
        };
        return true;
    }

    // What node `n` reads, its regions' ends and the nodes in its regions.
    fn pushReads(c: *Cone, stack: *std.ArrayList(Ref), n: NodeId) Allocator.Error!void {
        const store = c.p.store;
        const nd = store.node(n);
        for (store.refSlice(nd.args)) |arg| try stack.append(c.a, arg);
        for (store.regionSlice(nd.regions)) |sub| {
            const end = store.region(sub).end;
            for (store.refSlice(end.refs)) |x| try stack.append(c.a, x);
            if (end.kind == .branch) try stack.append(c.a, Ref.of(NodeId.of(end.target)));
            for (c.p.membersOf(sub)) |m| try stack.append(c.a, Ref.of(m));
        }
    }

    // Whether region `r` is a region of a node in the loop.
    fn inside(c: *const Cone, r: RegionId) bool {
        return inLoop(c.p, r, c.body);
    }

    fn hole(c: *Cone, r: Ref) Allocator.Error!void {
        if (std.mem.findScalar(Ref, c.holes.items, r) == null) try c.holes.append(c.a, r);
    }

    // Decide each outside node the cone reads: a constant is copied; a
    // speculatable node that owns no region and that only the row reads is
    // copied, with what it reads decided the same way; any other is a
    // captured value. A speculatable node evaluated in the row instead of
    // before the loop is evaluated where the body reads it, which C2 allows
    // (normal-form 1.1); a node that can fail stays before the loop.
    fn settle(c: *Cone) Allocator.Error!void {
        const store = c.p.store;
        var changed = true;
        while (changed) {
            changed = false;
            var i: usize = 0;
            while (i < c.outside.items.len) : (i += 1) {
                const n = c.outside.items[i];
                if (c.pre.contains(n)) continue;
                const nd = store.node(n);
                const constant = nd.args.len == 0 and nd.regions.len == 0 and nd.op != .crash;
                // A checked op N13u proved fits only under the facts where it
                // stands is not copied into another row.
                const copied = constant or (nd.regions.len == 0 and nd.flags.speculatable and store.fitFloor(n) == null and own(c.p, n) and c.onlyRead(n));
                if (!copied) continue;
                try c.pre.put(c.a, n, {});
                changed = true;
                for (store.refSlice(nd.args)) |arg| switch (arg.kind) {
                    .node => if (std.mem.findScalar(NodeId, c.outside.items, arg.nodeId()) == null) try c.outside.append(c.a, arg.nodeId()),
                    .row_param, .region_param, .input => {},
                };
            }
        }
        // The holes, in the order the cone and the copied nodes meet them.
        var order: std.ArrayList(Ref) = .empty;
        for (c.holes.items) |h| try order.append(c.a, h);
        for (c.outside.items) |n| {
            if (c.pre.contains(n)) {
                for (store.refSlice(store.node(n).args)) |arg| switch (arg.kind) {
                    .node => {},
                    .row_param, .region_param, .input => if (std.mem.findScalar(Ref, order.items, arg) == null) try order.append(c.a, arg),
                };
            } else if (std.mem.findScalar(Ref, order.items, Ref.of(n)) == null) try order.append(c.a, Ref.of(n));
        }
        c.holes = order;
    }

    // Whether every use of node `n` is in the cone or a copied node.
    fn onlyRead(c: *const Cone, n: NodeId) bool {
        const store = c.p.store;
        const sites = (c.p.uses.get(n) orelse return false).items;
        for (sites) |site| switch (site) {
            .node => |u| if (!c.nodes.contains(u) and !c.pre.contains(u)) return false,
            .region => |r| {
                const owner = store.region(r).owner;
                if (owner == NodeId.none or !c.nodes.contains(owner)) return false;
            },
        };
        return true;
    }

    // The copied outside nodes, each after what it reads.
    fn preInOrder(c: *const Cone) Allocator.Error![]const NodeId {
        var out: std.ArrayList(NodeId) = .empty;
        for (c.p.order.items) |n| if (c.pre.contains(n)) try out.append(c.a, n);
        return out.items;
    }
};

/// N16c to N16f: the value of `spec`, a `Prim` the builder is about to
/// build, under a law, or null where none applies.
pub fn prim(b: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
    const p = prims.lookup(ir.PrimId.of(spec.payload)) orelse return null;
    switch (p.owner) {
        .u64 => return isEmpty(b, p.method, spec),
        .list => switch (p.method) {
            .fold => return fold(b, spec),
            .map => return fused(b, spec),
            .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .keep_if, .collect => return null,
        },
        .iter => return collected(b, spec),
        .bool_, .str, .u8, .i8, .u16, .i16, .u32, .i32, .i64, .u128, .i128, .f32, .f64 => return null,
    }
}

/// What a `Prim` law matches, read without building anything: the L2 check
/// asks it of every node of a finished row (`noneRewritable`).
pub const PrimMatch = enum { fold, fusion, iter_map, is_empty };

/// The law that applies to node `nd` of `row`, if any. `sole` says whether
/// the node is the only reader of its first argument, which N16d needs.
pub fn matchPrim(store: *const ir.Store, types: *const Types, nd: ir.Node, sole: bool) ?PrimMatch {
    if (nd.op != .prim) return null;
    const p = prims.lookup(ir.PrimId.of(nd.payload)) orelse return null;
    const args = store.refSlice(nd.args);
    switch (p.owner) {
        .u64 => if (emptyTest(store, p.method, args) != null) return .is_empty,
        .list => switch (p.method) {
            .fold => if (closureAt(store, args[2]) != null) return .fold,
            .map => if (sole and fusable(store, args) != null) return .fusion,
            .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .keep_if, .collect => {},
        },
        .iter => if (mappedList(store, types, store.tySlice(nd.tys)[0], args[0]) != null) return .iter_map,
        .bool_, .str, .u8, .i8, .u16, .i16, .u32, .i32, .i64, .u128, .i128, .f32, .f64 => {},
    }
    return null;
}

// The `Closure` node `ref` is, if it is one.
fn closureAt(store: *const ir.Store, ref: Ref) ?ir.Node {
    if (ref.kind != .node) return null;
    const nd = store.node(ref.nodeId());
    return if (nd.op == .closure) nd else null;
}

// The node `ref` is when it is a `Prim` of the table's `owner.method`.
fn primAt(store: *const ir.Store, ref: Ref, owner: prims.Owner, method: prims.Method) ?ir.Node {
    if (ref.kind != .node) return null;
    const nd = store.node(ref.nodeId());
    if (nd.op != .prim) return null;
    const p = prims.lookup(ir.PrimId.of(nd.payload)) orelse return null;
    return if (p.owner == owner and p.method == method) nd else null;
}

fn isIntLit(store: *const ir.Store, ref: Ref, value: u128) bool {
    if (ref.kind != .node) return false;
    const nd = store.node(ref.nodeId());
    if (nd.op != .lit) return false;
    return switch (store.lit(ir.LitId.of(nd.payload)).value) {
        .int => |bits| bits == value,
        .float, .bool_, .str, .dec, .bytes => false,
    };
}

/// N16f's two shapes, and whether the result is negated.
const EmptyTest = struct { list: Ref, negated: bool };

// `is_eq(List.len(xs), 0)`, in either operand order, and `is_lt(0,
// List.len(xs))`. `List.len` gives a `U64`, so a length is 0 or above it,
// and a length above 0 is one that is not 0. `List.is_empty(xs)` is
// `List.len(xs) == 0` (`Builtin.roc`). Both sides are speculatable, so the
// rewrite drops and adds no crash.
fn emptyTest(store: *const ir.Store, method: prims.Method, args: []const Ref) ?EmptyTest {
    switch (method) {
        .is_eq => for ([_][2]usize{ .{ 0, 1 }, .{ 1, 0 } }) |at| {
            const len = primAt(store, args[at[0]], .list, .len) orelse continue;
            if (!isIntLit(store, args[at[1]], 0)) continue;
            return .{ .list = store.refSlice(len.args)[0], .negated = false };
        },
        .is_lt => {
            const len = primAt(store, args[1], .list, .len) orelse return null;
            if (!isIntLit(store, args[0], 0)) return null;
            return .{ .list = store.refSlice(len.args)[0], .negated = true };
        },
        // N13 writes `!(0 < len)` as `len <= 0`, which is `len == 0` over a `U64`.
        .is_lte => {
            const len = primAt(store, args[0], .list, .len) orelse return null;
            if (!isIntLit(store, args[1], 0)) return null;
            return .{ .list = store.refSlice(len.args)[0], .negated = false };
        },
        .not, .is_gt, .is_gte, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect => {},
    }
    return null;
}

// N16f over a literal switch: the list whose length a switch with the one
// key 0 tests. N13n makes `switch is_eq(List.len(xs), 0)` that switch, so
// N16f over the comparison and N13n meet here.
fn lenSwitch(store: *const ir.Store, refs: []const Ref, keys: []const u32) ?Ref {
    if (keys.len != 1) return null;
    const len = primAt(store, refs[0], .list, .len) orelse return null;
    switch (store.lit(ir.LitId.of(keys[0])).value) {
        .int => |bits| if (bits != 0) return null,
        .float, .bool_, .str, .dec, .bytes => return null,
    }
    return store.refSlice(len.args)[0];
}

/// N16f over a literal switch: `switch List.len(xs) { 0 => t, _ => f }` is
/// `switch List.is_empty(xs) { False => f, True => t }`. Exact: a length is
/// 0 exactly when the list is empty.
pub fn lenSwitchToEmpty(b: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
    const list = lenSwitch(b.store, spec.args, spec.aux) orelse return null;
    if (!b.algorithmOn(.law_is_empty)) return null;
    b.algorithmFired(.law_is_empty);
    const bool_ty = try b.types.boolTy();
    const empty = try b.primOf(prims.find(.list, .is_empty).?, &.{list}, bool_ty);
    // The arms in name order, `False` first: the default arm, then the arm of 0.
    const regions = try b.gpa.dupe(RegionId, spec.regions);
    defer b.gpa.free(regions);
    regions[0] = spec.regions[1];
    regions[1] = spec.regions[0];
    var out = spec;
    out.args = &.{empty};
    out.aux = &.{};
    out.regions = regions;
    return try b.make(out);
}

// N16f.
fn isEmpty(b: *Builder, method: prims.Method, spec: NodeSpec) Allocator.Error!?Ref {
    const t = emptyTest(b.store, method, spec.args) orelse return null;
    if (!b.algorithmOn(.law_is_empty)) return null;
    b.algorithmFired(.law_is_empty);
    const bool_ty = try b.types.boolTy();
    const empty = try b.primOf(prims.find(.list, .is_empty).?, &.{t.list}, bool_ty);
    if (!t.negated) return empty;
    return try b.primOf(prims.find(.bool_, .not).?, &.{empty}, bool_ty);
}

// N16c: `List.fold(xs, init, Closure(f, captures))` is the loop of its body
// in `Builtin.roc`, `for item in list { $state = step($state, item) }`, with
// the known function called directly: one `Call` per element, first to
// last, over the state so far. Calling the closure is calling its row over
// its captures and then the state and the element (N8i), and the law
// inlines that row (`Builder.Laws.inline_row`), so the loop meets the loop
// written by hand whatever else calls the row. A row that cannot be inlined,
// a recursive one or one that can end in `Return`, is called.
fn fold(b: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
    const store = b.store;
    const f = closureAt(store, spec.args[2]) orelse return null;
    if (!b.algorithmOn(.law_fold)) return null;
    const elem_ty = switch (b.types.get(store.refTy(b.row, spec.args[0]))) {
        .list => |e| e,
        .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .nominal, .func, .opaque_, .recursive => unreachable, // List.fold's first operand is a list by the typing of the body
    };
    b.algorithmFired(.law_fold);
    const state_ty = spec.tys[0];
    const xs = spec.args[0];
    const init = spec.args[1];
    const fn_row = RowId.of(f.payload);
    const captures = try b.gpa.dupe(Ref, store.refSlice(f.args));
    defer b.gpa.free(captures);
    const u64_ty = try b.types.intTy(.u64);
    const body = try b.openRegion(.loop_body, &.{ u64_ty, elem_ty, state_ty });
    try b.noteListLoop(body, xs);
    const call_args = try std.mem.concat(b.gpa, Ref, &.{ captures, &.{ Ref.regionParam(body, 2), Ref.regionParam(body, 1) } });
    defer b.gpa.free(call_args);
    const hook = b.laws.?;
    const next = (try hook.inline_row(hook.ctx, b, fn_row, call_args, state_ty)) orelse try b.callRowAt(fn_row, call_args, state_ty);
    try b.close(.{ .continue_ = &.{next} });
    return try b.loopOf(.for_list, &.{ xs, init }, body, &.{state_ty});
}

/// N16d's operands: the inner map's list and the two closures.
const Fusable = struct { xs: Ref, f: ir.Node, g: ir.Node, mid_ty: TyId };

fn fusable(store: *const ir.Store, args: []const Ref) ?Fusable {
    const inner = primAt(store, args[0], .list, .map) orelse return null;
    const inner_args = store.refSlice(inner.args);
    const f = closureAt(store, inner_args[1]) orelse return null;
    const g = closureAt(store, args[1]) orelse return null;
    return .{ .xs = inner_args[0], .f = f, .g = g, .mid_ty = store.tySlice(inner.tys)[0] };
}

// N16d: `List.map(List.map(xs, f), g)`, where the inner list is read
// nowhere else, is `List.map(xs, h)` with `h(x) = g(f(x))`. Both sides call
// `f` and `g` once on each element, so where neither crashes they give one
// list. They call them in another order, `f` on every element before `g` on
// any against `f` then `g` per element, so where both can crash they can
// crash at different calls, which C2 allows (normal-form 3.16). The functions
// are pure, so the order changes nothing else. The rebuild says when the
// outer map is the inner list's only reader (`Builder.sole_reader`).
// The row `h` holds the bodies of `f` and `g`, inlined as N16c inlines.
fn fused(b: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
    const store = b.store;
    if (b.sole_reader != spec.args[0]) return null;
    const m = fusable(store, spec.args) orelse return null;
    if (!b.algorithmOn(.law_fusion)) return null;
    const hook = b.laws orelse return null;
    const xs_ty = store.refTy(b.row, m.xs);
    const elem_ty = switch (b.types.get(xs_ty)) {
        .list => |e| e,
        .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .nominal, .func, .opaque_, .recursive => unreachable, // List.map's first operand is a list by the typing of the body
    };
    const mid_elem = listElem(b.types, m.mid_ty);
    const out_elem = listElem(b.types, spec.tys[0]);
    const f_row = RowId.of(m.f.payload);
    const g_row = RowId.of(m.g.payload);
    const f_caps = try b.gpa.dupe(Ref, store.refSlice(m.f.args));
    defer b.gpa.free(f_caps);
    const g_caps = try b.gpa.dupe(Ref, store.refSlice(m.g.args));
    defer b.gpa.free(g_caps);
    const captures = try std.mem.concat(b.gpa, Ref, &.{ f_caps, g_caps });
    defer b.gpa.free(captures);
    const params = try b.gpa.alloc(TyId, captures.len + 1);
    defer b.gpa.free(params);
    for (captures, params[0..captures.len]) |c, *t| t.* = store.refTy(b.row, c);
    params[captures.len] = elem_ty;
    const xs = m.xs;
    const fn_ty = try b.types.funcTy(&.{elem_ty}, out_elem);

    const held = b.suspendRow();
    const row = try b.beginRow(params, out_elem);
    {
        const f_args = try b.gpa.alloc(Ref, f_caps.len + 1);
        defer b.gpa.free(f_args);
        for (f_args[0..f_caps.len], 0..) |*r, k| r.* = Ref.rowParam(@intCast(k));
        f_args[f_caps.len] = Ref.rowParam(@intCast(captures.len));
        const mid = (try hook.inline_row(hook.ctx, b, f_row, f_args, mid_elem)) orelse try b.callRowAt(f_row, f_args, mid_elem);
        const g_args = try b.gpa.alloc(Ref, g_caps.len + 1);
        defer b.gpa.free(g_args);
        for (g_args[0..g_caps.len], 0..) |*r, k| r.* = Ref.rowParam(@intCast(f_caps.len + k));
        g_args[g_caps.len] = mid;
        const out = (try hook.inline_row(hook.ctx, b, g_row, g_args, out_elem)) orelse try b.callRowAt(g_row, g_args, out_elem);
        try b.endRow(.{ .value = &.{out} });
    }
    const target = hook.close(hook.ctx, b, row, @intCast(captures.len)) catch |err| switch (err) {
        error.OutOfMemory => |e| {
            b.resumeRow(held);
            return e;
        },
        // The driver keeps the reason and stops after the caller's round.
        error.MeasureDidNotFall, error.RoundBoundExceeded, error.InvariantBroken => null,
    };
    b.resumeRow(held);
    const made = target orelse return null;
    b.algorithmFired(.law_fusion);
    const kept = try b.gpa.alloc(Ref, made.kept.len);
    defer b.gpa.free(kept);
    for (made.kept, kept) |k, *r| r.* = captures[k];
    const clo = try b.closure(made.row, kept, fn_ty);
    return try b.primOf(prims.find(.list, .map).?, &.{ xs, clo }, spec.tys[0]);
}

fn listElem(types: *const Types, ty: TyId) TyId {
    return switch (types.get(ty)) {
        .list => |e| e,
        .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .nominal, .func, .opaque_, .recursive => unreachable, // List.map gives a list by the typing of the body
    };
}

/// N16e's operands: the list and the function.
const MappedList = struct { xs: Ref, f: Ref };

// `Iter.collect(Iter.map(List.iter(xs), f))` whose result `out_ty` is a
// `List`, with any `Iter.iter` between, which is the identity on an
// iterator. The roles are the checker's (N11k): `List.iter` yields every
// element in index order and never skips, and `Iter.map` yields `f` of each
// item it maps, in order, and skips where its source skips. `Iter.collect`
// into a `List` is `List.from_iter`, which appends every item in order
// (`Builtin.roc`). So the list holds `f(x)` for each `x` of `xs` in order,
// with `f` called once per element, first to last, as `List.map` does.
fn mappedList(store: *const ir.Store, types: *const Types, out_ty: TyId, iterator: Ref) ?MappedList {
    switch (types.get(out_ty)) {
        .list => {},
        .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .nominal, .func, .opaque_, .recursive => return null,
    }
    const map = roleAt(store, iterator, .map) orelse return null;
    const map_args = store.refSlice(map.args);
    var source = map_args[0];
    while (roleAt(store, source, .identity)) |known| source = store.refSlice(known.args)[0];
    const iter = roleAt(store, source, .list_iter) orelse return null;
    return .{ .xs = store.refSlice(iter.args)[0], .f = map_args[1] };
}

// The node `ref` is when it is a `Prim` the walk gave `role`.
fn roleAt(store: *const ir.Store, ref: Ref, role: ir.IteratorRole) ?ir.Node {
    if (ref.kind != .node) return null;
    const nd = store.node(ref.nodeId());
    if (nd.op != .prim) return null;
    return if (store.primName(ir.PrimId.of(nd.payload)).role == role) nd else null;
}

// N16e.
fn collected(b: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
    const m = mappedList(b.store, b.types, spec.tys[0], spec.args[0]) orelse return null;
    if (!b.algorithmOn(.law_iter_map)) return null;
    b.algorithmFired(.law_iter_map);
    return try b.primOf(prims.find(.list, .map).?, &.{ m.xs, m.f }, spec.tys[0]);
}

/// L2 over a finished row of a site that opts in: no loop raises and no
/// `Prim` matches a law that is on.
pub fn noneRewritable(a: Allocator, p: *const place.Plan, b: *const Builder) Allocator.Error!bool {
    const store = p.store;
    var it = p.info.constKeyIterator();
    while (it.next()) |n| {
        const nd = store.node(n);
        if (nd.op == .for_list) {
            const found = (try raise(a, p, b.types, n)) orelse continue;
            const law: builder_mod.Algorithm = switch (found.law) {
                .map => .law_map,
                .keep_if => .law_keep_if,
            };
            if (b.algorithmOn(law)) return false;
            continue;
        }
        if (nd.op == .switch_) {
            if (lenSwitch(store, store.refSlice(nd.args), store.wordSlice(nd.aux)) != null and b.algorithmOn(.law_is_empty)) return false;
            continue;
        }
        const found = matchPrim(store, b.types, nd, soleFirst(p, n, nd)) orelse continue;
        const law: builder_mod.Algorithm = switch (found) {
            .fold => .law_fold,
            .fusion => .law_fusion,
            .iter_map => .law_iter_map,
            .is_empty => .law_is_empty,
        };
        if (b.algorithmOn(law)) return false;
    }
    return true;
}

/// Whether node `n`, which `p` places, is the only reader of its first
/// argument, read once.
pub fn soleFirst(p: *const place.Plan, n: NodeId, nd: ir.Node) bool {
    const args = p.store.refSlice(nd.args);
    if (args.len == 0 or args[0].kind != .node) return false;
    const first = args[0].nodeId();
    if (!own(p, first)) return false;
    const sites = (p.uses.get(first) orelse return false).items;
    if (sites.len != 1) return false;
    return switch (sites[0]) {
        .node => |u| u == n,
        .region => false,
    };
}

/// Whether node `nd` of the row is a `Prim` of the table's `List.map`.
pub fn isMap(nd: ir.Node) bool {
    if (nd.op != .prim) return false;
    const p = prims.lookup(ir.PrimId.of(nd.payload)) orelse return false;
    return p.owner == .list and p.method == .map;
}

/// Whether node `nd` counts in the measure's `law_redexes`: a `List.fold` of
/// a known function, which N16c rewrites to a loop, or a literal switch that
/// N16f rewrites to a `Bool` switch.
pub fn isLawRedex(store: *const ir.Store, nd: ir.Node) bool {
    if (nd.op == .switch_) return lenSwitch(store, store.refSlice(nd.args), store.wordSlice(nd.aux)) != null;
    if (nd.op != .prim) return false;
    const p = prims.lookup(ir.PrimId.of(nd.payload)) orelse return false;
    if (p.owner != .list or p.method != .fold) return false;
    return closureAt(store, store.refSlice(nd.args)[2]) != null;
}

const testing = std.testing;
const driver = @import("driver.zig");
const dump = @import("dump.zig");
const eval = @import("eval.zig");
const verify = @import("verify.zig");

const Fixture = struct {
    store: ir.Store,
    types: Types,
    b: Builder,
    u64_ty: TyId = undefined,
    list_ty: TyId = undefined,

    fn init(self: *Fixture) !void {
        self.store = ir.Store.init(testing.allocator);
        self.types = Types.init(testing.allocator);
        self.b = Builder.init(testing.allocator, &self.store, &self.types);
        self.u64_ty = try self.types.intTy(.u64);
        self.list_ty = try self.types.listTy(self.u64_ty);
    }

    fn deinit(self: *Fixture) void {
        self.b.deinit();
        self.types.deinit();
        self.store.deinit();
    }

    // The `graph` view of the site of `root`, with or without layer L, dumped.
    fn site(self: *Fixture, root: RowId, with_laws: bool) ![]u8 {
        _ = try driver.runToWith(testing.allocator, &self.b, root, &.{}, .graph, .{ .laws = with_laws });
        var report = try verify.verifyAll(testing.allocator, &self.store, &self.types);
        defer report.deinit();
        try testing.expect(report.ok());
        var out: std.Io.Writer.Allocating = .init(testing.allocator);
        errdefer out.deinit();
        try dump.dumpSite(&out.writer, testing.allocator, &self.store, &self.types, root);
        return out.toOwnedSlice();
    }

    fn prim(self: *Fixture, method: prims.Method, args: []const Ref, ty: TyId) !Ref {
        const owner: prims.Owner = switch (method) {
            .collect => .iter,
            .not => .bool_,
            else => .list,
        };
        return self.b.primOf(prims.find(owner, method).?, args, ty);
    }

    fn fnTy(self: *Fixture, params: []const TyId, result: TyId) !TyId {
        return self.types.funcTy(params, result);
    }

    // `|x| x + 1`, `|x| x * 3`, `|x| 3 < x`, `|s, x| s + x * 2`, `|k, x| x + k`.
    fn inc(self: *Fixture) !RowId {
        const r = try self.b.beginRow(&.{self.u64_ty}, self.u64_ty);
        try self.b.endRow(.{ .value = &.{try self.b.call(.u64, .plus, &.{ Ref.rowParam(0), try self.b.litInt(self.u64_ty, 1) })} });
        return r;
    }

    fn triple(self: *Fixture) !RowId {
        const r = try self.b.beginRow(&.{self.u64_ty}, self.u64_ty);
        try self.b.endRow(.{ .value = &.{try self.b.call(.u64, .times, &.{ Ref.rowParam(0), try self.b.litInt(self.u64_ty, 3) })} });
        return r;
    }

    fn big(self: *Fixture) !RowId {
        const r = try self.b.beginRow(&.{self.u64_ty}, try self.types.boolTy());
        try self.b.endRow(.{ .value = &.{try self.b.call(.u64, .is_lt, &.{ try self.b.litInt(self.u64_ty, 3), Ref.rowParam(0) })} });
        return r;
    }

    fn step(self: *Fixture) !RowId {
        const r = try self.b.beginRow(&.{ self.u64_ty, self.u64_ty }, self.u64_ty);
        const twice = try self.b.call(.u64, .times, &.{ Ref.rowParam(1), try self.b.litInt(self.u64_ty, 2) });
        try self.b.endRow(.{ .value = &.{try self.b.call(.u64, .plus, &.{ Ref.rowParam(0), twice })} });
        return r;
    }

    fn addK(self: *Fixture) !RowId {
        const r = try self.b.beginRow(&.{ self.u64_ty, self.u64_ty }, self.u64_ty);
        try self.b.endRow(.{ .value = &.{try self.b.call(.u64, .plus, &.{ Ref.rowParam(1), Ref.rowParam(0) })} });
        return r;
    }

    // `|xs, k| { var $out = []; for x in xs { $out = $out.append(value(x, k)) }; $out }`.
    fn loopMap(self: *Fixture, comptime value: fn (*Fixture, Ref, Ref) anyerror!Ref) !RowId {
        const root = try self.b.beginRow(&.{ self.list_ty, self.u64_ty }, self.list_ty);
        const empty = try self.b.listOf(self.list_ty, &.{});
        const lb = try self.b.openRegion(.loop_body, &.{ self.u64_ty, self.u64_ty, self.list_ty });
        try self.b.noteListLoop(lb, Ref.rowParam(0));
        const v = try value(self, Ref.regionParam(lb, 1), Ref.rowParam(1));
        const next = try self.prim(.append, &.{ Ref.regionParam(lb, 2), v }, self.list_ty);
        try self.b.close(.{ .continue_ = &.{next} });
        const loop = try self.b.loopOf(.for_list, &.{ Ref.rowParam(0), empty }, lb, &.{self.list_ty});
        try self.b.endRow(.{ .value = &.{loop} });
        return root;
    }

    // `|xs, k| { var $out = []; for x in xs { if 3 < x { $out = $out.append(x) } }; $out }`,
    // with the append in the `True` arm, or with the test negated and the
    // append in the `False` arm.
    fn loopKeep(self: *Fixture, negated: bool) !RowId {
        const root = try self.b.beginRow(&.{ self.list_ty, self.u64_ty }, self.list_ty);
        const empty = try self.b.listOf(self.list_ty, &.{});
        const lb = try self.b.openRegion(.loop_body, &.{ self.u64_ty, self.u64_ty, self.list_ty });
        try self.b.noteListLoop(lb, Ref.rowParam(0));
        const x = Ref.regionParam(lb, 1);
        const s = Ref.regionParam(lb, 2);
        const t = if (negated)
            try self.b.call(.u64, .is_lte, &.{ x, try self.b.litInt(self.u64_ty, 3) })
        else
            try self.b.call(.u64, .is_lt, &.{ try self.b.litInt(self.u64_ty, 3), x });
        var arms: [2]RegionId = undefined;
        for (&arms, 0..) |*a, key| {
            a.* = try self.b.openArm(t, @intCast(key));
            const keeps = (key == 1) != negated;
            if (keeps) {
                try self.b.close(.{ .value = &.{try self.prim(.append, &.{ s, x }, self.list_ty)} });
            } else try self.b.close(.{ .value = &.{s} });
        }
        const next = try self.b.switchOn(t, &arms, &.{}, &.{self.list_ty}, &.{});
        try self.b.close(.{ .continue_ = &.{next} });
        const loop = try self.b.loopOf(.for_list, &.{ Ref.rowParam(0), empty }, lb, &.{self.list_ty});
        try self.b.endRow(.{ .value = &.{loop} });
        return root;
    }

    // `|xs, k| xs.map(f)` over a closure of `f` capturing `caps`.
    fn builtinMap(self: *Fixture, f: RowId, caps: []const Ref) !RowId {
        const root = try self.b.beginRow(&.{ self.list_ty, self.u64_ty }, self.list_ty);
        const clo = try self.b.closure(f, caps, try self.fnTy(&.{self.u64_ty}, self.u64_ty));
        try self.b.endRow(.{ .value = &.{try self.prim(.map, &.{ Ref.rowParam(0), clo }, self.list_ty)} });
        return root;
    }
};

fn plusOne(f: *Fixture, x: Ref, _: Ref) anyerror!Ref {
    return f.b.call(.u64, .plus, &.{ x, try f.b.litInt(f.u64_ty, 1) });
}

fn plusK(f: *Fixture, x: Ref, k: Ref) anyerror!Ref {
    return f.b.call(.u64, .plus, &.{ x, k });
}

fn expectHas(got: []const u8, want: []const u8, unwanted: []const u8) !void {
    if (std.mem.find(u8, got, want) == null or std.mem.find(u8, got, unwanted) != null) {
        std.debug.print("expected {s} and not {s} in:\n{s}\n", .{ want, unwanted, got });
        return error.TestUnexpectedResult;
    }
}

// The lists every law test runs both sides on: empty, small, and one whose
// `+ 1` overflows at its second element.
fn inputLists(arena: Allocator) ![4]eval.Value {
    const max = std.math.maxInt(u64);
    const mk = struct {
        fn of(a: Allocator, xs: []const i256) !eval.Value {
            const out = try a.alloc(eval.Value, xs.len);
            for (xs, out) |x, *o| o.* = .{ .int = x };
            return .{ .list = out };
        }
    };
    return .{ try mk.of(arena, &.{}), try mk.of(arena, &.{ 1, 5, 2, 9 }), try mk.of(arena, &.{ 4, max, 7 }), try mk.of(arena, &.{3}) };
}

const Outcome = union(enum) { value: eval.Value, crash };

fn runAll(arena: Allocator, f: *Fixture, root: RowId, args: []const []const eval.Value) ![]Outcome {
    const out = try arena.alloc(Outcome, args.len);
    for (args, out) |a, *o| {
        var e = try eval.Evaluator.init(arena, &f.store, &f.types, .strict);
        o.* = if (e.run(root, a)) |v| .{ .value = v } else |err| switch (err) {
            error.Crash => .crash,
            else => |other| return other,
        };
    }
    return out;
}

// Laws hold (normal-form 9): the row before the laws and after them gives
// one value on every input, and crashes where it did.
fn expectSameOutcomes(arena: Allocator, before: []const Outcome, after: []const Outcome) !void {
    for (before, after) |x, y| switch (x) {
        .value => |v| try testing.expect(y == .value and v.eql(y.value)),
        .crash => try testing.expect(y == .crash),
    };
    _ = arena;
}

fn argsFor(arena: Allocator, lists: []const eval.Value) ![]const []const eval.Value {
    const out = try arena.alloc([]const eval.Value, lists.len);
    for (lists, out) |l, *o| o.* = try arena.dupe(eval.Value, &.{ l, .{ .int = 2 } });
    return out;
}

test "N16a: a ForList that appends one value per turn to [] is List.map, and the laws hold" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const lists = try inputLists(arena.allocator());
    const args = try argsFor(arena.allocator(), &lists);
    var f: Fixture = undefined;
    try f.init();
    defer f.deinit();
    const root = try f.loopMap(plusOne);
    const before = try runAll(arena.allocator(), &f, root, args);
    const got = try f.site(root, true);
    defer testing.allocator.free(got);
    try expectHas(got, "List.map(", "for_list(");
    try expectSameOutcomes(arena.allocator(), before, try runAll(arena.allocator(), &f, root, args));
}

test "N16a: the loop meets the List.map written with a lambda, with and without a captured value" {
    inline for (.{ false, true }) |captured| {
        var loop: Fixture = undefined;
        try loop.init();
        defer loop.deinit();
        var written: Fixture = undefined;
        try written.init();
        defer written.deinit();
        const a = try loop.loopMap(if (captured) plusK else plusOne);
        const g = if (captured) try written.addK() else try written.inc();
        const b = try written.builtinMap(g, if (captured) &.{Ref.rowParam(1)} else &.{});
        const x = try loop.site(a, true);
        defer testing.allocator.free(x);
        const y = try written.site(b, true);
        defer testing.allocator.free(y);
        try testing.expectEqualStrings(y, x);
    }
}

test "N16a: without the opt-in, and with the law knocked out, the loop stays a ForList" {
    inline for (.{ false, true }) |knocked| {
        var f: Fixture = undefined;
        try f.init();
        defer f.deinit();
        if (knocked) f.b.hooks.algorithms_off.insert(.law_map);
        const root = try f.loopMap(plusOne);
        const got = try f.site(root, knocked);
        defer testing.allocator.free(got);
        try expectHas(got, "for_list(", "List.map(");
    }
}

test "N16a: a loop whose value reads the index, or that starts from a list that is not empty, stays a ForList" {
    var f: Fixture = undefined;
    try f.init();
    defer f.deinit();
    const index = struct {
        fn v(fx: *Fixture, x: Ref, _: Ref) anyerror!Ref {
            // `x + i`: the index is the body's parameter 0.
            return fx.b.call(.u64, .plus, &.{ x, Ref.regionParam(x.regionId(), 0) });
        }
    }.v;
    const root = try f.loopMap(index);
    const got = try f.site(root, true);
    defer testing.allocator.free(got);
    try expectHas(got, "for_list(", "List.map(");

    var g: Fixture = undefined;
    try g.init();
    defer g.deinit();
    const r = try g.b.beginRow(&.{ g.list_ty, g.u64_ty }, g.list_ty);
    const lb = try g.b.openRegion(.loop_body, &.{ g.u64_ty, g.u64_ty, g.list_ty });
    try g.b.noteListLoop(lb, Ref.rowParam(0));
    try g.b.close(.{ .continue_ = &.{try g.prim(.append, &.{ Ref.regionParam(lb, 2), Ref.regionParam(lb, 1) }, g.list_ty)} });
    const loop = try g.b.loopOf(.for_list, &.{ Ref.rowParam(0), Ref.rowParam(0) }, lb, &.{g.list_ty});
    try g.b.endRow(.{ .value = &.{loop} });
    const other = try g.site(r, true);
    defer testing.allocator.free(other);
    try expectHas(other, "for_list(", "List.map(");
}

test "N16b: a ForList that appends its element under a test is List.keep_if, in either arm, and the laws hold" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const lists = try inputLists(arena.allocator());
    const args = try argsFor(arena.allocator(), &lists);
    var prints: [2][]u8 = undefined;
    inline for (.{ false, true }, 0..) |negated, i| {
        var f: Fixture = undefined;
        try f.init();
        defer f.deinit();
        const root = try f.loopKeep(negated);
        const before = try runAll(arena.allocator(), &f, root, args);
        prints[i] = try f.site(root, true);
        try expectHas(prints[i], "List.keep_if(", "for_list(");
        try expectSameOutcomes(arena.allocator(), before, try runAll(arena.allocator(), &f, root, args));
    }
    defer for (prints) |p| testing.allocator.free(p);
    try testing.expectEqualStrings(prints[0], prints[1]);
    // The written `List.keep_if(xs, |x| 3 < x)` is the same.
    var w: Fixture = undefined;
    try w.init();
    defer w.deinit();
    const pred = try w.big();
    const root = try w.b.beginRow(&.{ w.list_ty, w.u64_ty }, w.list_ty);
    const clo = try w.b.closure(pred, &.{}, try w.fnTy(&.{w.u64_ty}, try w.types.boolTy()));
    try w.b.endRow(.{ .value = &.{try w.prim(.keep_if, &.{ Ref.rowParam(0), clo }, w.list_ty)} });
    const written = try w.site(root, true);
    defer testing.allocator.free(written);
    try testing.expectEqualStrings(written, prints[0]);
}

test "N16b: knocked out, the loop stays a ForList" {
    var f: Fixture = undefined;
    try f.init();
    defer f.deinit();
    f.b.hooks.algorithms_off.insert(.law_keep_if);
    const root = try f.loopKeep(false);
    const got = try f.site(root, true);
    defer testing.allocator.free(got);
    try expectHas(got, "for_list(", "List.keep_if(");
}

// `|xs, k| xs.fold(0, step)`.
fn foldRow(f: *Fixture) !RowId {
    const st = try f.step();
    const root = try f.b.beginRow(&.{ f.list_ty, f.u64_ty }, f.u64_ty);
    const clo = try f.b.closure(st, &.{}, try f.fnTy(&.{ f.u64_ty, f.u64_ty }, f.u64_ty));
    try f.b.endRow(.{ .value = &.{try f.prim(.fold, &.{ Ref.rowParam(0), try f.b.litInt(f.u64_ty, 0), clo }, f.u64_ty)} });
    return root;
}

test "N16c: List.fold with a known function is the ForList that calls it, the hand-written loop, and the laws hold" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const lists = try inputLists(arena.allocator());
    const args = try argsFor(arena.allocator(), &lists);
    var f: Fixture = undefined;
    try f.init();
    defer f.deinit();
    const root = try foldRow(&f);
    const before = try runAll(arena.allocator(), &f, root, args);
    const got = try f.site(root, true);
    defer testing.allocator.free(got);
    try expectHas(got, "for_list(", "List.fold(");
    try expectSameOutcomes(arena.allocator(), before, try runAll(arena.allocator(), &f, root, args));

    // `|xs, k| { var $s = 0; for x in xs { $s = $s + x * 2 }; $s }`.
    var h: Fixture = undefined;
    try h.init();
    defer h.deinit();
    const r = try h.b.beginRow(&.{ h.list_ty, h.u64_ty }, h.u64_ty);
    const zero = try h.b.litInt(h.u64_ty, 0);
    const lb = try h.b.openRegion(.loop_body, &.{ h.u64_ty, h.u64_ty, h.u64_ty });
    try h.b.noteListLoop(lb, Ref.rowParam(0));
    const twice = try h.b.call(.u64, .times, &.{ Ref.regionParam(lb, 1), try h.b.litInt(h.u64_ty, 2) });
    try h.b.close(.{ .continue_ = &.{try h.b.call(.u64, .plus, &.{ Ref.regionParam(lb, 2), twice })} });
    const loop = try h.b.loopOf(.for_list, &.{ Ref.rowParam(0), zero }, lb, &.{h.u64_ty});
    try h.b.endRow(.{ .value = &.{loop} });
    const hand = try h.site(r, true);
    defer testing.allocator.free(hand);
    try testing.expectEqualStrings(hand, got);
}

test "N16c: without the opt-in, and knocked out, the fold stays" {
    inline for (.{ false, true }) |knocked| {
        var f: Fixture = undefined;
        try f.init();
        defer f.deinit();
        if (knocked) f.b.hooks.algorithms_off.insert(.law_fold);
        const root = try foldRow(&f);
        const got = try f.site(root, knocked);
        defer testing.allocator.free(got);
        try expectHas(got, "List.fold(", "for_list(");
    }
}

// `|xs, k| xs.map(inc).map(triple)`, the inner list read `reads` times.
fn twoMaps(f: *Fixture, reads: u32) !RowId {
    const i = try f.inc();
    const t = try f.triple();
    const fn_ty = try f.fnTy(&.{f.u64_ty}, f.u64_ty);
    const root = try f.b.beginRow(&.{ f.list_ty, f.u64_ty }, f.list_ty);
    const inner = try f.prim(.map, &.{ Ref.rowParam(0), try f.b.closure(i, &.{}, fn_ty) }, f.list_ty);
    const outer = try f.prim(.map, &.{ inner, try f.b.closure(t, &.{}, fn_ty) }, f.list_ty);
    const value = if (reads == 1) outer else try f.prim(.append, &.{ outer, try f.b.call(.list, .len, &.{inner}) }, f.list_ty);
    try f.b.endRow(.{ .value = &.{value} });
    return root;
}

test "N16d: a map of a map read nowhere else is one map of a row calling both, the map of the composed lambda, and the laws hold" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const lists = try inputLists(arena.allocator());
    const args = try argsFor(arena.allocator(), &lists);
    var f: Fixture = undefined;
    try f.init();
    defer f.deinit();
    const root = try twoMaps(&f, 1);
    const before = try runAll(arena.allocator(), &f, root, args);
    const got = try f.site(root, true);
    defer testing.allocator.free(got);
    try testing.expectEqual(@as(usize, 1), std.mem.count(u8, got, "List.map("));
    // Where both can crash, C2 allows either crash; these inputs crash only in `+ 1`.
    try expectSameOutcomes(arena.allocator(), before, try runAll(arena.allocator(), &f, root, args));

    // `|xs, k| xs.map(|x| (x + 1) * 3)`.
    var w: Fixture = undefined;
    try w.init();
    defer w.deinit();
    const h = try w.b.beginRow(&.{w.u64_ty}, w.u64_ty);
    const plus = try w.b.call(.u64, .plus, &.{ Ref.rowParam(0), try w.b.litInt(w.u64_ty, 1) });
    try w.b.endRow(.{ .value = &.{try w.b.call(.u64, .times, &.{ plus, try w.b.litInt(w.u64_ty, 3) })} });
    const one = try w.builtinMap(h, &.{});
    const written = try w.site(one, true);
    defer testing.allocator.free(written);
    try testing.expectEqualStrings(written, got);
}

test "N16d: an inner list read twice, no opt-in, or the law knocked out keeps both maps" {
    inline for (.{ .{ 2, true, false }, .{ 1, false, false }, .{ 1, true, true } }) |c| {
        var f: Fixture = undefined;
        try f.init();
        defer f.deinit();
        if (c[2]) f.b.hooks.algorithms_off.insert(.law_fusion);
        const root = try twoMaps(&f, c[0]);
        const got = try f.site(root, c[1]);
        defer testing.allocator.free(got);
        try testing.expectEqual(@as(usize, 2), std.mem.count(u8, got, "List.map("));
    }
}

// `|xs, k| xs.iter().map(inc).collect()`, through the checker's roles.
fn iterMap(f: *Fixture, list_role: ir.IteratorRole) !RowId {
    const i = try f.inc();
    const iter_ty = try f.types.opaqueTy("Iter", &.{f.u64_ty});
    const root = try f.b.beginRow(&.{ f.list_ty, f.u64_ty }, f.list_ty);
    const it = try f.b.primOf(try f.b.namedPrimWithRole("List", "iter", list_role), &.{Ref.rowParam(0)}, iter_ty);
    const mapped = try f.b.primOf(try f.b.namedPrimWithRole("Iter", "map", .map), &.{ it, try f.b.closure(i, &.{}, try f.fnTy(&.{f.u64_ty}, f.u64_ty)) }, iter_ty);
    try f.b.endRow(.{ .value = &.{try f.prim(.collect, &.{mapped}, f.list_ty)} });
    return root;
}

test "N16e: collecting an Iter.map of List.iter into a List is List.map, by the checker's roles" {
    var f: Fixture = undefined;
    try f.init();
    defer f.deinit();
    const root = try iterMap(&f, .list_iter);
    const got = try f.site(root, true);
    defer testing.allocator.free(got);
    var w: Fixture = undefined;
    try w.init();
    defer w.deinit();
    const written = try w.site(try w.builtinMap(try w.inc(), &.{}), true);
    defer testing.allocator.free(written);
    try testing.expectEqualStrings(written, got);
}

test "N16e: a source without the List.iter role, no opt-in, or the law knocked out keeps the collect" {
    inline for (.{ .{ ir.IteratorRole.none, true, false }, .{ ir.IteratorRole.list_iter, false, false }, .{ ir.IteratorRole.list_iter, true, true } }) |c| {
        var f: Fixture = undefined;
        try f.init();
        defer f.deinit();
        if (c[2]) f.b.hooks.algorithms_off.insert(.law_iter_map);
        const root = try iterMap(&f, c[0]);
        const got = try f.site(root, c[1]);
        defer testing.allocator.free(got);
        try expectHas(got, "Iter.collect(", "List.map(");
    }
}

// `|xs| xs.len() == 0` in either operand order, `0 < xs.len()`, and the
// `is_empty` forms they meet.
const LenForm = enum { eq_zero, zero_eq, zero_lt, empty, not_empty, len_lte };

fn lenRow(f: *Fixture, form: LenForm) !RowId {
    const bool_ty = try f.types.boolTy();
    const root = try f.b.beginRow(&.{f.list_ty}, bool_ty);
    const zero = try f.b.litInt(f.u64_ty, 0);
    const len = try f.b.call(.list, .len, &.{Ref.rowParam(0)});
    const value = switch (form) {
        .eq_zero => try f.b.call(.u64, .is_eq, &.{ len, zero }),
        .zero_eq => try f.b.call(.u64, .is_eq, &.{ zero, len }),
        .zero_lt => try f.b.call(.u64, .is_lt, &.{ zero, len }),
        .empty => try f.prim(.is_empty, &.{Ref.rowParam(0)}, bool_ty),
        .not_empty => try f.prim(.not, &.{try f.prim(.is_empty, &.{Ref.rowParam(0)}, bool_ty)}, bool_ty),
        .len_lte => try f.b.call(.u64, .is_lte, &.{ len, zero }),
    };
    try f.b.endRow(.{ .value = &.{value} });
    return root;
}

test "N16f: a length compared with 0 is List.is_empty or its negation, and without the opt-in it is not" {
    var prints: [6][]u8 = undefined;
    inline for (std.meta.tags(LenForm), 0..) |form, i| {
        var f: Fixture = undefined;
        try f.init();
        defer f.deinit();
        prints[i] = try f.site(try lenRow(&f, form), true);
    }
    defer for (prints) |p| testing.allocator.free(p);
    try testing.expectEqualStrings(prints[3], prints[0]);
    try testing.expectEqualStrings(prints[3], prints[1]);
    try testing.expectEqualStrings(prints[4], prints[2]);
    try testing.expectEqualStrings(prints[3], prints[5]);
    inline for (.{ false, true }) |knocked| {
        var f: Fixture = undefined;
        try f.init();
        defer f.deinit();
        if (knocked) f.b.hooks.algorithms_off.insert(.law_is_empty);
        const got = try f.site(try lenRow(&f, .zero_lt), knocked);
        defer testing.allocator.free(got);
        try expectHas(got, "List.len(", "List.is_empty(");
    }
}

// `|xs, a, b|` choosing `a` where `xs` is empty, by a literal switch on its
// length (the form N13n gives `if xs.len() == 0`) or by `List.is_empty`.
fn lenSwitchRow(f: *Fixture, literal: bool) !RowId {
    const root = try f.b.beginRow(&.{ f.list_ty, f.u64_ty, f.u64_ty }, f.u64_ty);
    if (literal) {
        const len = try f.b.call(.list, .len, &.{Ref.rowParam(0)});
        const keys = [_]u32{(try f.b.internLit(f.u64_ty, .{ .int = 0 })).index()};
        var arms: [2]RegionId = undefined;
        for (&arms, [_]u30{ 1, 2 }, 0..) |*arm, param, i| {
            arm.* = try f.b.openLitArm(len, &keys, @intCast(i));
            try f.b.close(.{ .value = &.{Ref.rowParam(param)} });
        }
        try f.b.endRow(.{ .value = &.{try f.b.switchOn(len, &arms, &.{}, &.{f.u64_ty}, &keys)} });
    } else {
        const empty = try f.prim(.is_empty, &.{Ref.rowParam(0)}, try f.types.boolTy());
        var arms: [2]RegionId = undefined;
        // `False` first.
        for (&arms, [_]u30{ 2, 1 }, 0..) |*arm, param, key| {
            arm.* = try f.b.openArm(empty, @intCast(key));
            try f.b.close(.{ .value = &.{Ref.rowParam(param)} });
        }
        try f.b.endRow(.{ .value = &.{try f.b.switchOn(empty, &arms, &.{}, &.{f.u64_ty}, &.{})} });
    }
    return root;
}

test "N16f: a literal switch on a length with the one key 0 is a switch on List.is_empty, and without the opt-in it is not" {
    var w: Fixture = undefined;
    try w.init();
    defer w.deinit();
    const written = try w.site(try lenSwitchRow(&w, false), true);
    defer testing.allocator.free(written);
    {
        var f: Fixture = undefined;
        try f.init();
        defer f.deinit();
        const got = try f.site(try lenSwitchRow(&f, true), true);
        defer testing.allocator.free(got);
        try testing.expectEqualStrings(written, got);
    }
    inline for (.{ false, true }) |knocked| {
        var f: Fixture = undefined;
        try f.init();
        defer f.deinit();
        if (knocked) f.b.hooks.algorithms_off.insert(.law_is_empty);
        const got = try f.site(try lenSwitchRow(&f, true), knocked);
        defer testing.allocator.free(got);
        try expectHas(got, "List.len(", "List.is_empty(");
    }
}

test "law pairs: a fold whose step appends is a loop (N16c) and then a map (N16a); a collected Iter.map of a map fuses (N16e, N16d)" {
    // `|xs, k| xs.fold([], |acc, x| acc.append(x + 1))`.
    var f: Fixture = undefined;
    try f.init();
    defer f.deinit();
    const st = try f.b.beginRow(&.{ f.list_ty, f.u64_ty }, f.list_ty);
    const v = try f.b.call(.u64, .plus, &.{ Ref.rowParam(1), try f.b.litInt(f.u64_ty, 1) });
    try f.b.endRow(.{ .value = &.{try f.prim(.append, &.{ Ref.rowParam(0), v }, f.list_ty)} });
    const root = try f.b.beginRow(&.{ f.list_ty, f.u64_ty }, f.list_ty);
    const clo = try f.b.closure(st, &.{}, try f.fnTy(&.{ f.list_ty, f.u64_ty }, f.list_ty));
    try f.b.endRow(.{ .value = &.{try f.prim(.fold, &.{ Ref.rowParam(0), try f.b.listOf(f.list_ty, &.{}), clo }, f.list_ty)} });
    const got = try f.site(root, true);
    defer testing.allocator.free(got);
    var w: Fixture = undefined;
    try w.init();
    defer w.deinit();
    const written = try w.site(try w.builtinMap(try w.inc(), &.{}), true);
    defer testing.allocator.free(written);
    try testing.expectEqualStrings(written, got);

    // `|xs, k| xs.map(inc).iter().map(triple).collect()` meets `xs.map(|x| (x + 1) * 3)`.
    var g: Fixture = undefined;
    try g.init();
    defer g.deinit();
    const i = try g.inc();
    const t = try g.triple();
    const fn_ty = try g.fnTy(&.{g.u64_ty}, g.u64_ty);
    const iter_ty = try g.types.opaqueTy("Iter", &.{g.u64_ty});
    const r = try g.b.beginRow(&.{ g.list_ty, g.u64_ty }, g.list_ty);
    const inner = try g.prim(.map, &.{ Ref.rowParam(0), try g.b.closure(i, &.{}, fn_ty) }, g.list_ty);
    const it = try g.b.primOf(try g.b.namedPrimWithRole("List", "iter", .list_iter), &.{inner}, iter_ty);
    const mapped = try g.b.primOf(try g.b.namedPrimWithRole("Iter", "map", .map), &.{ it, try g.b.closure(t, &.{}, fn_ty) }, iter_ty);
    try g.b.endRow(.{ .value = &.{try g.prim(.collect, &.{mapped}, g.list_ty)} });
    const fused_print = try g.site(r, true);
    defer testing.allocator.free(fused_print);
    var h: Fixture = undefined;
    try h.init();
    defer h.deinit();
    const comp = try h.b.beginRow(&.{h.u64_ty}, h.u64_ty);
    const plus = try h.b.call(.u64, .plus, &.{ Ref.rowParam(0), try h.b.litInt(h.u64_ty, 1) });
    try h.b.endRow(.{ .value = &.{try h.b.call(.u64, .times, &.{ plus, try h.b.litInt(h.u64_ty, 3) })} });
    const one = try h.site(try h.builtinMap(comp, &.{}), true);
    defer testing.allocator.free(one);
    try testing.expectEqualStrings(one, fused_print);
}
