//! N17: known lists (normal-form 3.17; plan 3.3 and 3.4).
//!
//! A `List` node holds its elements, so its length is known in the graph.
//! Over such a list a list builtin is what its body in `Builtin.roc`
//! computes:
//!
//! | Step | From | To | Here |
//! |---|---|---|---|
//! | N17a | `List.len(List(e..))`, `List.is_empty(List(e..))` | `Lit(n)`, `Lit(n == 0)` | `prim` |
//! | N17b | `List.get(List(e..), Lit(i))`, `List.first`, `List.last` | `Ok(ei)`, or the `Err` tag | `prim` |
//! | N17c | `List.get(List(e..), x)`, `x` not a literal | a literal switch on `x`, arm `k` giving `Ok(ek)`, the default `Err(OutOfBounds)` | `prim` |
//! | N17d | `concat`, `append`, `prepend`, `single`, `with_capacity`, `set` and `drop_first`, `take_first` at a literal, `repeat` at a literal of at most B | the `List` node of the result | `prim` |
//! | N17e | `map`, `map2`, `map_with_index` with a known function; `keep_if` whose every predicate value is a `Bool` literal | the `List` node of the calls; the kept elements | `prim` |
//! | N17f | `fold`, `fold_rev`, `fold_with_index`, `any`, `all` with a known function; `sum` over a builtin number type | the chain of calls; `Or`, `And` of the calls; the `plus` chain from the first element | `prim` |
//! | N17g | `ForList(List(e..))` of at most B elements, whose every path ends in `Continue` | the body once per element, the slots threaded | `unrollable`, applied by `rebuild.zig` |
//!
//! A known function is a `Closure`; N8i makes each `Apply` of it a direct
//! `Call`. A `Lambda` the `inline` view made of a closure is not one, so a
//! list that only that view makes known keeps its builtin.
//!
//! Each row is exact under C2 (normal-form 1.1). A `List` node evaluates every
//! element, and a builtin that calls a function calls it once per element, in
//! element order, so each call of the result runs where the builtin ran it;
//! `any` and `all` stop at the element that decides them, and so do the
//! operands of `Or` and `And`. What a rule drops is dead (normal-form 3.6). An
//! index is a `U64`, so a literal index is never below 0, and a list of known
//! length never has more than B elements more than the author wrote, so no
//! length wraps.

const std = @import("std");
const ir = @import("ir.zig");
const prims = @import("prims.zig");
const types_mod = @import("types.zig");
const live = @import("live.zig");
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

/// B: the most elements `List.repeat` builds (N17d) and the most turns
/// N17g unrolls, a constant of the language version, like K of `outline`.
pub const max_unrolled: u32 = 16;

/// The steps of N17, for the normal-form fingerprint.
pub const steps = [_][]const u8{
    "N17a: List.len and List.is_empty of a List node are literals",
    "N17b: List.get at a literal index, List.first and List.last of a List node are Ok of the element or the Err tag",
    "N17c: List.get of a List node at an index that is not a literal is a literal switch on the index, keys 0 to n - 1",
    "N17d: concat of adjacent List nodes, append, prepend, single, with_capacity, set, drop_first and take_first at a literal, repeat at a literal of at most B, are the List node of the result",
    "N17e: map, map2 and map_with_index of List nodes with a Closure are the List node of the calls; keep_if whose every inlined predicate value is a Bool literal is the kept elements",
    "N17f: fold and fold_rev with a Closure are the chain of calls, any and all the Or and And of the calls, sum over a builtin number type the plus chain from the first element and 0 for []",
    "N17f: fold_with_index with a Closure is the chain of calls, each with its index as a U64 literal",
    "N17g: a ForList over a List node of at most B elements whose body ends in Continue and cannot return is its body once per element, the slots threaded",
};

/// One step of N17, which a knockout turns off by its algorithm.
pub const Step = enum { len, get, lookup, build, map, fold, unroll };

/// The steps that are on: what the measure counts and L2 checks.
pub const Rules = std.EnumSet(Step);

/// The builder's switch for `step`.
pub fn algorithm(step: Step) builder_mod.Algorithm {
    return switch (step) {
        .len => .list_len,
        .get => .list_get,
        .lookup => .list_lookup,
        .build => .list_build,
        .map => .list_map,
        .fold => .list_fold,
        .unroll => .list_unroll,
    };
}

/// The steps that are on in `b`.
pub fn rulesOf(b: *const Builder) Rules {
    var on: Rules = .empty;
    for (std.enums.values(Step)) |s| if (b.algorithmOn(algorithm(s))) on.insert(s);
    return on;
}

/// The elements of the `List` node `ref` is, if it is one. The slice is
/// valid until the next node is built.
pub fn known(store: *const ir.Store, ref: Ref) ?[]const Ref {
    if (ref.kind != .node) return null;
    const nd = store.node(ref.nodeId());
    if (nd.op != .list) return null;
    return store.refSlice(nd.args);
}

// The value of the integer literal `ref` is, if it is one.
fn intLit(store: *const ir.Store, ref: Ref) ?u128 {
    if (ref.kind != .node) return null;
    const nd = store.node(ref.nodeId());
    if (nd.op != .lit) return null;
    return switch (store.lit(ir.LitId.of(nd.payload)).value) {
        .int => |bits| bits,
        .float, .bool_, .str, .dec, .bytes => null,
    };
}

fn isClosure(store: *const ir.Store, ref: Ref) bool {
    if (ref.kind != .node) return false;
    return store.node(ref.nodeId()).op == .closure;
}

// The owner and literal kind of `ty` where `List.sum` over it is a `plus`
// chain: a builtin integer or float type, or `Dec`.
const Num = union(enum) { int: types_mod.IntTy, float: types_mod.FloatTy, dec };

fn numOf(types: *const Types, ty: TyId) ?Num {
    return switch (types.get(ty)) {
        .int => |i| .{ .int = i },
        .float => |f| .{ .float = f },
        .dec => .dec,
        .bool_, .str, .record, .tuple, .tag_union, .list, .nominal, .func, .opaque_, .recursive => null,
    };
}

/// The step of N17 that applies to node `n`, read without building anything:
/// what the measure counts and the L2 check finds. `keep_if` is not here:
/// its condition reads the values of the predicate, which only building them
/// gives.
pub fn redex(store: *const ir.Store, types: *const Types, n: NodeId) ?Step {
    const nd = store.node(n);
    if (nd.op == .for_list) return if (unrollable(store, n)) .unroll else null;
    if (nd.op != .prim) return null;
    const p = prims.lookup(ir.PrimId.of(nd.payload)) orelse return null;
    if (p.owner != .list) return null;
    const args = store.refSlice(nd.args);
    return switch (p.method) {
        .len, .is_empty => if (known(store, args[0]) != null) .len else null,
        .first, .last => if (known(store, args[0]) != null) .get else null,
        .get => if (known(store, args[0]) == null) null else if (intLit(store, args[1]) != null) .get else .lookup,
        .concat => for (args[0 .. args.len - 1], args[1..]) |a, b| {
            if (known(store, a) != null and known(store, b) != null) break .build;
        } else null,
        .append, .prepend => if (known(store, args[0]) != null) .build else null,
        .single, .with_capacity => .build,
        .set, .drop_first, .take_first => if (known(store, args[0]) != null and intLit(store, args[1]) != null) .build else null,
        .repeat => if (intLit(store, args[1])) |k| (if (k <= max_unrolled) .build else null) else null,
        .map, .map_with_index => if (known(store, args[0]) != null and isClosure(store, args[1])) .map else null,
        .map2 => if (known(store, args[0]) != null and known(store, args[1]) != null and isClosure(store, args[2])) .map else null,
        .fold, .fold_rev, .fold_with_index => if (known(store, args[0]) != null and isClosure(store, args[2])) .fold else null,
        .any, .all => if (known(store, args[0]) != null and isClosure(store, args[1])) .fold else null,
        .sum => if (known(store, args[0]) != null and numOf(types, store.tySlice(nd.tys)[0]) != null) .fold else null,
        .keep_if => null,
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .collect, .ok_or => null,
    };
}

/// N17g's condition on the `ForList` `n`, but for the bound on its list's
/// length, which `rebuild.zig` reads on the list the loop is built over: the
/// loop runs over a `List` node of at most B elements, it has an output, and
/// its body ends in `Continue` and holds no node that can end the row in
/// `Return`. Its body then runs to its end once per element, as N17g copies
/// it. A loop that cannot return and has no output is dead.
pub fn unrollable(store: *const ir.Store, n: NodeId) bool {
    const nd = store.node(n);
    if (nd.op != .for_list or nd.tys.len == 0) return false;
    const xs = known(store, store.refSlice(nd.args)[0]) orelse return false;
    if (xs.len > max_unrolled) return false;
    const body = store.regionSlice(nd.regions)[0];
    if (store.region(body).end.kind != .continue_) return false;
    return !live.canReturn(store, n);
}

/// N17a to N17f: the value of `spec`, a `Prim` of a list builtin the builder
/// is about to build, or null where no step applies.
pub fn prim(b: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
    const p = prims.lookup(ir.PrimId.of(spec.payload)) orelse return null;
    if (p.owner != .list) return null;
    const store = b.store;
    const args = spec.args;
    const ty = spec.tys[0];
    switch (p.method) {
        // N17a: `List.len(list) == 0` is `is_empty` (`Builtin.roc`).
        .len, .is_empty => {
            const xs = known(store, args[0]) orelse return null;
            if (!fire(b, .len)) return null;
            return if (p.method == .len) try b.litInt(ty, @intCast(xs.len)) else try b.litBool(xs.len == 0);
        },
        // N17b: `first` is `get(list, 0)` and `last` is `get(list, len - 1)`
        // where the list is not empty, and `Err(ListWasEmpty)` where it is.
        .first, .last => {
            const xs = known(store, args[0]) orelse return null;
            if (!fire(b, .get)) return null;
            if (xs.len == 0) return try errOf(b, ty, "ListWasEmpty");
            const e = if (p.method == .first) xs[0] else xs[xs.len - 1];
            return try okOf(b, ty, e);
        },
        .get => return get(b, args, ty),
        .concat => return concat(b, spec),
        .append, .prepend => {
            const xs = try dupeKnown(b, args[0]) orelse return null;
            defer b.gpa.free(xs);
            if (!fire(b, .build)) return null;
            const out = try b.gpa.alloc(Ref, xs.len + 1);
            defer b.gpa.free(out);
            if (p.method == .append) {
                @memcpy(out[0..xs.len], xs);
                out[xs.len] = args[1];
            } else {
                out[0] = args[1];
                @memcpy(out[1..], xs);
            }
            return try b.listOf(ty, out);
        },
        .single => {
            if (!fire(b, .build)) return null;
            return try b.listOf(ty, args[0..1]);
        },
        // The capacity is not part of the value: the list is `[]`.
        .with_capacity => {
            if (!fire(b, .build)) return null;
            return try b.listOf(ty, &.{});
        },
        .set => {
            const at = intLit(store, args[1]) orelse return null;
            const xs = try dupeKnown(b, args[0]) orelse return null;
            defer b.gpa.free(xs);
            if (!fire(b, .build)) return null;
            if (at >= xs.len) return try errOf(b, ty, "OutOfBounds");
            xs[@intCast(at)] = args[2];
            return try okOf(b, ty, try b.listOf(store.refTy(b.row, args[0]), xs));
        },
        // `sublist` clamps the count to the length.
        .drop_first, .take_first => {
            const count = intLit(store, args[1]) orelse return null;
            const xs = try dupeKnown(b, args[0]) orelse return null;
            defer b.gpa.free(xs);
            if (!fire(b, .build)) return null;
            const k: usize = @intCast(@min(count, xs.len));
            return try b.listOf(ty, if (p.method == .drop_first) xs[k..] else xs[0..k]);
        },
        .repeat => {
            const count = intLit(store, args[1]) orelse return null;
            if (count > max_unrolled) return null;
            if (!fire(b, .build)) return null;
            const out = try b.gpa.alloc(Ref, @intCast(count));
            defer b.gpa.free(out);
            @memset(out, args[0]);
            return try b.listOf(ty, out);
        },
        .map, .map_with_index => {
            if (!isClosure(store, args[1])) return null;
            const xs = try dupeKnown(b, args[0]) orelse return null;
            defer b.gpa.free(xs);
            if (!fire(b, .map)) return null;
            const elem_ty = listElem(b.types, ty);
            const out = try b.gpa.alloc(Ref, xs.len);
            defer b.gpa.free(out);
            const index_ty = try b.types.intTy(.u64);
            for (xs, out, 0..) |x, *o, i| {
                o.* = if (p.method == .map)
                    try b.apply(args[1], &.{x}, elem_ty)
                else
                    try b.apply(args[1], &.{ x, try b.litInt(index_ty, @intCast(i)) }, elem_ty);
            }
            return try b.listOf(ty, out);
        },
        // The result is as long as the shorter list.
        .map2 => {
            if (!isClosure(store, args[2])) return null;
            const xs = try dupeKnown(b, args[0]) orelse return null;
            defer b.gpa.free(xs);
            const ys = try dupeKnown(b, args[1]) orelse return null;
            defer b.gpa.free(ys);
            if (!fire(b, .map)) return null;
            const elem_ty = listElem(b.types, ty);
            const n = @min(xs.len, ys.len);
            const out = try b.gpa.alloc(Ref, n);
            defer b.gpa.free(out);
            for (xs[0..n], ys[0..n], out) |x, y, *o| o.* = try b.apply(args[2], &.{ x, y }, elem_ty);
            return try b.listOf(ty, out);
        },
        .keep_if => return keepIf(b, args, ty),
        .fold, .fold_rev, .fold_with_index => {
            if (!isClosure(store, args[2])) return null;
            const xs = try dupeKnown(b, args[0]) orelse return null;
            defer b.gpa.free(xs);
            if (!fire(b, .fold)) return null;
            var state = args[1];
            if (p.method == .fold) {
                for (xs) |x| state = try b.apply(args[2], &.{ state, x }, ty);
            } else if (p.method == .fold_with_index) {
                const index_ty = try b.types.intTy(.u64);
                for (xs, 0..) |x, i| state = try b.apply(args[2], &.{ state, x, try b.litInt(index_ty, @intCast(i)) }, ty);
            } else {
                var i = xs.len;
                while (i > 0) {
                    i -= 1;
                    state = try b.apply(args[2], &.{ xs[i], state }, ty);
                }
            }
            return state;
        },
        .any, .all => {
            if (!isClosure(store, args[1])) return null;
            const xs = try dupeKnown(b, args[0]) orelse return null;
            defer b.gpa.free(xs);
            if (!fire(b, .fold)) return null;
            const op: ir.Op = if (p.method == .any) .or_ else .and_;
            if (xs.len == 0) return try b.litBool(op == .and_);
            const first = try b.apply(args[1], &.{xs[0]}, ty);
            const operands = try b.gpa.alloc(RegionId, xs.len - 1);
            defer b.gpa.free(operands);
            for (xs[1..], operands) |x, *r| {
                r.* = try b.openOperand(&.{first}, op);
                try b.close(.{ .value = &.{try b.apply(args[1], &.{x}, ty)} });
            }
            return if (op == .or_) try b.orOf(first, operands) else try b.andOf(first, operands);
        },
        // `Iter.sum` starts at the first item and adds each next one with
        // `plus`; `default()` is called only for `[]`, and is 0 for the
        // builtin number types.
        .sum => {
            const num = numOf(b.types, ty) orelse return null;
            const xs = try dupeKnown(b, args[0]) orelse return null;
            defer b.gpa.free(xs);
            if (!fire(b, .fold)) return null;
            if (xs.len == 0) return switch (num) {
                .int => try b.litInt(ty, 0),
                .float => try b.litFloatBits(ty, 0),
                .dec => try b.litDec(0),
            };
            const plus = switch (num) {
                .int => |i| prims.find(prims.intOwner(i), .plus).?,
                .float => |f| prims.find(prims.floatOwner(f), .plus).?,
                .dec => try b.namedPrim("Num.Dec", "plus"),
            };
            var acc = xs[0];
            for (xs[1..]) |x| acc = try b.primOf(plus, &.{ acc, x }, ty);
            return acc;
        },
        .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .collect, .ok_or => return null,
    }
}

// Whether `step` is on, counting it as fired where it is.
fn fire(b: *Builder, step: Step) bool {
    const a = algorithm(step);
    if (!b.algorithmOn(a)) return false;
    b.algorithmFired(a);
    return true;
}

// The elements of the known list `ref`, owned by the caller.
fn dupeKnown(b: *Builder, ref: Ref) Allocator.Error!?[]Ref {
    const xs = known(b.store, ref) orelse return null;
    return try b.gpa.dupe(Ref, xs);
}

fn listElem(types: *const Types, ty: TyId) TyId {
    return switch (types.get(ty)) {
        .list => |e| e,
        .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .nominal, .func, .opaque_, .recursive => @import("base").invariant("reify N17: a list builtin gives a type that is not a list", .{}),
    };
}

// N17b over `get` at a literal index, N17c at any other: `get` is
// `Ok(list_get_unsafe(list, index))` where `index < List.len(list)` and
// `Err(OutOfBounds)` elsewhere (`Builtin.roc`). A literal switch on the index
// decides `index < n` per key: each key below `n` selects its element, and
// every other index the default.
fn get(b: *Builder, args: []const Ref, ty: TyId) Allocator.Error!?Ref {
    const store = b.store;
    const index = args[1];
    if (intLit(store, index)) |at| {
        const xs = known(store, args[0]) orelse return null;
        if (!fire(b, .get)) return null;
        if (at >= xs.len) return try errOf(b, ty, "OutOfBounds");
        return try okOf(b, ty, xs[@intCast(at)]);
    }
    const xs = try dupeKnown(b, args[0]) orelse return null;
    defer b.gpa.free(xs);
    if (!fire(b, .lookup)) return null;
    if (xs.len == 0) return try errOf(b, ty, "OutOfBounds");
    const index_ty = store.refTy(b.row, index);
    const keys = try b.gpa.alloc(u32, xs.len);
    defer b.gpa.free(keys);
    for (keys, 0..) |*k, i| k.* = (try b.internLit(index_ty, .{ .int = i })).index();
    const arms = try b.gpa.alloc(RegionId, xs.len + 1);
    defer b.gpa.free(arms);
    for (arms, 0..) |*arm, i| {
        arm.* = try b.openLitArm(index, keys, @intCast(i));
        const v = if (i < xs.len) try okOf(b, ty, xs[i]) else try errOf(b, ty, "OutOfBounds");
        try b.close(.{ .value = &.{v} });
    }
    return try b.switchOn(index, arms, &.{}, &.{ty}, keys);
}

// N17d over a `concat` chain (N15a flattens one): each run of adjacent known
// lists is one `List` node of their elements in order, which is what
// `concat` of them gives.
fn concat(b: *Builder, spec: NodeSpec) Allocator.Error!?Ref {
    const store = b.store;
    const args = spec.args;
    const adjacent = for (args[0 .. args.len - 1], args[1..]) |x, y| {
        if (known(store, x) != null and known(store, y) != null) break true;
    } else false;
    if (!adjacent or !fire(b, .build)) return null;
    var operands: std.ArrayList(Ref) = .empty;
    defer operands.deinit(b.gpa);
    var run: std.ArrayList(Ref) = .empty;
    defer run.deinit(b.gpa);
    var in_run: u32 = 0;
    var i: usize = 0;
    while (i <= args.len) : (i += 1) {
        const elems = if (i < args.len) known(store, args[i]) else null;
        if (elems) |xs| {
            try run.appendSlice(b.gpa, xs);
            in_run += 1;
            continue;
        }
        if (in_run == 1) {
            try operands.append(b.gpa, args[i - 1]);
        } else if (in_run > 1) {
            try operands.append(b.gpa, try b.listOf(spec.tys[0], run.items));
        }
        run.clearRetainingCapacity();
        in_run = 0;
        if (i < args.len) try operands.append(b.gpa, args[i]);
    }
    if (operands.items.len == 1) return operands.items[0];
    var out = spec;
    out.args = operands.items;
    return try b.make(out);
}

// N17e over `keep_if`: where the predicate's value at every element is a
// `Bool` literal, the result is the elements whose value is `True`, in
// order. The value at an element is the predicate's row inlined over its
// captures and the element; a value that is not a literal leaves the call,
// and what the inlining built is dead.
fn keepIf(b: *Builder, args: []const Ref, ty: TyId) Allocator.Error!?Ref {
    const store = b.store;
    const clo = b.knownClosure(args[1]) orelse return null;
    const inliner = b.inliner orelse return null;
    if (!b.algorithmOn(.list_map)) return null;
    const row = clo.row;
    const captures = try b.gpa.dupe(Ref, clo.captures);
    defer b.gpa.free(captures);
    const xs = try dupeKnown(b, args[0]) orelse return null;
    defer b.gpa.free(xs);
    const bool_ty = try b.types.boolTy();
    var kept: std.ArrayList(Ref) = .empty;
    defer kept.deinit(b.gpa);
    const call_args = try b.gpa.alloc(Ref, captures.len + 1);
    defer b.gpa.free(call_args);
    @memcpy(call_args[0..captures.len], captures);
    for (xs) |x| {
        call_args[captures.len] = x;
        const v = (try inliner.run(inliner.ctx, b, row, call_args, bool_ty)) orelse return null;
        if (v.kind != .node) return null;
        const nd = store.node(v.nodeId());
        if (nd.op != .lit) return null;
        switch (store.lit(ir.LitId.of(nd.payload)).value) {
            .bool_ => |keep| if (keep) try kept.append(b.gpa, x),
            .int, .float, .str, .dec, .bytes => return null,
        }
    }
    b.algorithmFired(.list_map);
    return try b.listOf(ty, kept.items);
}

// `Ok(v)` at the `Try` type `ty`, or the nominal over it.
fn okOf(b: *Builder, ty: TyId, v: Ref) Allocator.Error!Ref {
    return tagAt(b, ty, "Ok", &.{v});
}

// `Err(why)` at the `Try` type `ty`, with `why` the payload-free tag of the
// error union `Builtin.roc` gives.
fn errOf(b: *Builder, ty: TyId, why: []const u8) Allocator.Error!Ref {
    const backing = try backingOf(b, ty);
    const err = b.types.findName("Err") orelse @import("base").invariant("reify N17: a list builtin gives a Try without Err", .{});
    const at = b.types.memberIndex(backing, err) orelse @import("base").invariant("reify N17: a list builtin gives a Try without Err", .{});
    const err_ty = b.types.tySlice(b.types.memberSlice(b.types.get(backing).tag_union)[at].tys)[0];
    const reason = try tagAt(b, err_ty, why, &.{});
    return tagAt(b, ty, "Err", &.{reason});
}

// The tag `name` of the union `ty` is, or of the union a nominal `ty` wraps.
fn tagAt(b: *Builder, ty: TyId, name: []const u8, payload: []const Ref) Allocator.Error!Ref {
    const backing = try backingOf(b, ty);
    const id = b.types.findName(name) orelse @import("base").invariant("reify N17: the union a list builtin gives has no tag {s}", .{name});
    const tagged = try b.tag(backing, id, payload);
    return if (backing == ty) tagged else try b.wrap(ty, tagged);
}

fn backingOf(b: *Builder, ty: TyId) Allocator.Error!TyId {
    return switch (b.types.get(ty)) {
        .nominal => try b.types.unfold(ty),
        .tag_union => ty,
        .bool_, .str, .int, .float, .dec, .record, .tuple, .list, .func, .opaque_, .recursive => @import("base").invariant("reify N17: a list builtin gives a type that is not a tag union", .{}),
    };
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
    bool_ty: TyId = undefined,
    list_ty: TyId = undefined,
    /// `Try(U64, [OutOfBounds])`, `Try(U64, [ListWasEmpty])` and
    /// `Try(List(U64), [OutOfBounds])`, as the builtins give them.
    get_ty: TyId = undefined,
    first_ty: TyId = undefined,
    set_ty: TyId = undefined,

    fn init(self: *Fixture, rules_off: bool) !void {
        self.store = ir.Store.init(testing.allocator);
        self.types = Types.init(testing.allocator);
        self.b = Builder.init(testing.allocator, &self.store, &self.types);
        self.b.hooks.rules_off = rules_off;
        self.u64_ty = try self.types.intTy(.u64);
        self.bool_ty = try self.types.boolTy();
        self.list_ty = try self.types.listTy(self.u64_ty);
        const oob = try self.types.tagUnionTy(&.{.{ .name = "OutOfBounds", .payload = &.{} }});
        const empty = try self.types.tagUnionTy(&.{.{ .name = "ListWasEmpty", .payload = &.{} }});
        self.get_ty = try self.types.tagUnionTy(&.{ .{ .name = "Ok", .payload = &.{self.u64_ty} }, .{ .name = "Err", .payload = &.{oob} } });
        self.first_ty = try self.types.tagUnionTy(&.{ .{ .name = "Ok", .payload = &.{self.u64_ty} }, .{ .name = "Err", .payload = &.{empty} } });
        self.set_ty = try self.types.tagUnionTy(&.{ .{ .name = "Ok", .payload = &.{self.list_ty} }, .{ .name = "Err", .payload = &.{oob} } });
    }

    fn deinit(self: *Fixture) void {
        self.b.deinit();
        self.types.deinit();
        self.store.deinit();
    }

    // The `graph` view of the site of `root`, verified and dumped.
    fn site(self: *Fixture, root: RowId) ![]u8 {
        _ = try driver.runTo(testing.allocator, &self.b, root, &.{}, .graph);
        var report = try verify.verifyAll(testing.allocator, &self.store, &self.types);
        defer report.deinit();
        try testing.expect(report.ok());
        var out: std.Io.Writer.Allocating = .init(testing.allocator);
        errdefer out.deinit();
        try dump.dumpSite(&out.writer, testing.allocator, &self.store, &self.types, root);
        return out.toOwnedSlice();
    }

    fn prim(self: *Fixture, method: prims.Method, args: []const Ref, ty: TyId) !Ref {
        return self.b.primOf(prims.find(.list, method).?, args, ty);
    }

    fn lit(self: *Fixture, v: i128) !Ref {
        return self.b.litInt(self.u64_ty, v);
    }

    fn list(self: *Fixture, items: []const Ref) !Ref {
        return self.b.listOf(self.list_ty, items);
    }

    // `[k, 1, 2]` over the root's parameter `k`.
    fn k12(self: *Fixture) !Ref {
        return self.list(&.{ Ref.rowParam(0), try self.lit(1), try self.lit(2) });
    }

    // A closure, capturing nothing, of a row built aside of the one being
    // built: `body` over the row's parameters `params`.
    fn function(self: *Fixture, params: []const TyId, result: TyId, comptime body: fn (*Fixture) anyerror!Ref) !Ref {
        const held = self.b.suspendRow();
        const r = try self.b.beginRow(params, result);
        try self.b.endRow(.{ .value = &.{try body(self)} });
        self.b.resumeRow(held);
        return self.b.closure(r, &.{}, try self.types.funcTy(params, result));
    }

    // `|x| x + 1`.
    fn inc(self: *Fixture) !Ref {
        return self.function(&.{self.u64_ty}, self.u64_ty, struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.b.call(.u64, .plus, &.{ Ref.rowParam(0), try f.lit(1) });
            }
        }.b);
    }

    // `|a, b| a * 2 + b`, which is not commutative.
    fn mix(self: *Fixture) !Ref {
        return self.function(&.{ self.u64_ty, self.u64_ty }, self.u64_ty, struct {
            fn b(f: *Fixture) anyerror!Ref {
                const twice = try f.b.call(.u64, .times, &.{ Ref.rowParam(0), try f.lit(2) });
                return f.b.call(.u64, .plus, &.{ twice, Ref.rowParam(1) });
            }
        }.b);
    }

    // `|a, b, i| a * 2 + b + i`, which reads the index.
    fn mixIndexed(self: *Fixture) !Ref {
        return self.function(&.{ self.u64_ty, self.u64_ty, self.u64_ty }, self.u64_ty, struct {
            fn b(f: *Fixture) anyerror!Ref {
                const twice = try f.b.call(.u64, .times, &.{ Ref.rowParam(0), try f.lit(2) });
                const sum = try f.b.call(.u64, .plus, &.{ twice, Ref.rowParam(1) });
                return f.b.call(.u64, .plus, &.{ sum, Ref.rowParam(2) });
            }
        }.b);
    }

    // `|x| 3 < x`.
    fn big(self: *Fixture) !Ref {
        return self.function(&.{self.u64_ty}, self.bool_ty, struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.b.call(.u64, .is_lt, &.{ try f.lit(3), Ref.rowParam(0) });
            }
        }.b);
    }

};

const Outcome = union(enum) { value: eval.Value, crash };

fn runAll(arena: Allocator, f: *Fixture, root: RowId, inputs: []const i256) ![]Outcome {
    const out = try arena.alloc(Outcome, inputs.len);
    for (inputs, out) |k, *o| {
        var e = try eval.Evaluator.init(arena, &f.store, &f.types, .strict);
        o.* = if (e.run(root, &.{.{ .int = k }})) |v| .{ .value = v } else |err| switch (err) {
            error.Crash => .crash,
            else => |other| return other,
        };
    }
    return out;
}

/// The `k` every rule test runs both sides on: the elements' own values, one
/// past the end, and the greatest `U64`, at which `k + 1` overflows.
const test_inputs = [_]i256{ 0, 1, 2, 3, std.math.maxInt(u64) };

const Case = struct {
    result: enum { u64_, bool_, list, get, first, set } = .u64_,
    body: *const fn (*Fixture) anyerror!Ref,
};

fn resultTy(f: *Fixture, c: Case) TyId {
    return switch (c.result) {
        .u64_ => f.u64_ty,
        .bool_ => f.bool_ty,
        .list => f.list_ty,
        .get => f.get_ty,
        .first => f.first_ty,
        .set => f.set_ty,
    };
}

fn buildCase(f: *Fixture, c: Case) !RowId {
    // A function value the body passes is a closure of a row built before the root.
    const r = try f.b.beginRow(&.{f.u64_ty}, resultTy(f, c));
    const v = try c.body(f);
    try f.b.endRow(.{ .value = &.{v} });
    return r;
}

/// The case built without rules and evaluated, then built with the rules and
/// `knocked` off, simplified and evaluated: the dump holds every `want` and
/// no `unwanted`, and each input gives what it gave without the rules, a crash
/// where it crashed (normal-form 1.1, C2).
fn expectCase(c: Case, knocked: ?builder_mod.Algorithm, want: []const []const u8, unwanted: []const []const u8) ![]u8 {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var raw: Fixture = undefined;
    try raw.init(true);
    defer raw.deinit();
    const raw_root = try buildCase(&raw, c);
    const before = try runAll(arena.allocator(), &raw, raw_root, &test_inputs);

    var f: Fixture = undefined;
    try f.init(false);
    defer f.deinit();
    if (knocked) |k| f.b.hooks.algorithms_off.insert(k);
    const root = try buildCase(&f, c);
    const got = try f.site(root);
    errdefer testing.allocator.free(got);
    for (want) |w| if (std.mem.find(u8, got, w) == null) {
        std.debug.print("expected {s} in:\n{s}\n", .{ w, got });
        return error.TestUnexpectedResult;
    };
    for (unwanted) |w| if (std.mem.find(u8, got, w) != null) {
        std.debug.print("did not expect {s} in:\n{s}\n", .{ w, got });
        return error.TestUnexpectedResult;
    };
    const after = try runAll(arena.allocator(), &f, root, &test_inputs);
    for (before, after) |x, y| switch (x) {
        .value => |v| if (y != .value or !v.eql(y.value)) {
            std.debug.print("a value changed in:\n{s}\n", .{got});
            return error.TestUnexpectedResult;
        },
        .crash => try testing.expect(y == .crash),
    };
    return got;
}

// Each rule fires, and with its knockout it does not.
fn expectStep(c: Case, alg: builder_mod.Algorithm, prim_name: []const u8, also: []const []const u8) !void {
    const on = try expectCase(c, null, also, &.{prim_name});
    testing.allocator.free(on);
    const off = try expectCase(c, alg, &.{prim_name}, &.{});
    testing.allocator.free(off);
}

test "N17a: List.len and List.is_empty of a known list are literals; knocked out they stay" {
    try expectStep(.{ .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.len, &.{try f.k12()}, f.u64_ty);
        }
    }.b }, .list_len, "List.len(", &.{"value n0"});
    inline for (.{ false, true }) |empty| {
        try expectStep(.{ .result = .bool_, .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.prim(.is_empty, &.{if (empty) try f.list(&.{}) else try f.k12()}, f.bool_ty);
            }
        }.b }, .list_len, "List.is_empty(", &.{if (empty) "True" else "False"});
    }
}

test "N17b: List.get at a literal index, List.first and List.last of a known list are Ok of the element or the Err tag" {
    inline for (.{ 0, 2, 3, 7 }) |at| {
        try expectStep(.{ .result = .get, .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.prim(.get, &.{ try f.k12(), try f.lit(at) }, f.get_ty);
            }
        }.b }, .list_get, "List.get(", &.{if (at < 3) "tag Ok(" else "tag OutOfBounds("});
    }
    inline for (.{ .first, .last }) |m| inline for (.{ false, true }) |empty| {
        try expectStep(.{ .result = .first, .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.prim(m, &.{if (empty) try f.list(&.{}) else try f.k12()}, f.first_ty);
            }
        }.b }, .list_get, "List." ++ @tagName(m) ++ "(", &.{if (empty) "tag ListWasEmpty(" else "tag Ok("});
    };
}

test "N17c: List.get of a known list at an index that is not a literal is a literal switch on the index" {
    try expectStep(.{ .result = .get, .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.get, &.{ try f.list(&.{ try f.lit(10), try f.lit(20), try f.lit(30) }), Ref.rowParam(0) }, f.get_ty);
        }
    }.b }, .list_lookup, "List.get(", &.{ "switch p0", "arm 0", "arm 2", "default", "tag OutOfBounds(" });
    // An empty list has no key: every index is out of bounds.
    try expectStep(.{ .result = .get, .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.get, &.{ try f.list(&.{}), Ref.rowParam(0) }, f.get_ty);
        }
    }.b }, .list_lookup, "List.get(", &.{"tag OutOfBounds("});
}

test "N17d: list builtins over known lists and literals are the List node of the result" {
    const cases = [_]struct { m: []const u8, want: []const u8 = "list(", c: Case }{
        .{ .m = "List.concat(", .c = .{ .result = .list, .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.prim(.concat, &.{ try f.list(&.{Ref.rowParam(0)}), try f.list(&.{ try f.lit(1), try f.lit(2) }) }, f.list_ty);
            }
        }.b } },
        .{ .m = "List.append(", .c = .{ .result = .list, .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.prim(.append, &.{ try f.k12(), try f.lit(9) }, f.list_ty);
            }
        }.b } },
        .{ .m = "List.prepend(", .c = .{ .result = .list, .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.prim(.prepend, &.{ try f.k12(), try f.lit(9) }, f.list_ty);
            }
        }.b } },
        .{ .m = "List.single(", .c = .{ .result = .list, .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.prim(.single, &.{Ref.rowParam(0)}, f.list_ty);
            }
        }.b } },
        .{ .m = "List.with_capacity(", .c = .{ .result = .list, .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.prim(.with_capacity, &.{Ref.rowParam(0)}, f.list_ty);
            }
        }.b } },
        .{ .m = "List.set(", .c = .{ .result = .set, .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.prim(.set, &.{ try f.k12(), try f.lit(1), try f.lit(9) }, f.set_ty);
            }
        }.b } },
        .{ .m = "List.set(", .want = "tag OutOfBounds(", .c = .{ .result = .set, .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.prim(.set, &.{ try f.k12(), try f.lit(3), try f.lit(9) }, f.set_ty);
            }
        }.b } },
        .{ .m = "List.drop_first(", .c = .{ .result = .list, .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.prim(.drop_first, &.{ try f.k12(), try f.lit(1) }, f.list_ty);
            }
        }.b } },
        .{ .m = "List.drop_first(", .c = .{ .result = .list, .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.prim(.drop_first, &.{ try f.k12(), try f.lit(5) }, f.list_ty);
            }
        }.b } },
        .{ .m = "List.take_first(", .c = .{ .result = .list, .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.prim(.take_first, &.{ try f.k12(), try f.lit(2) }, f.list_ty);
            }
        }.b } },
        .{ .m = "List.take_first(", .c = .{ .result = .list, .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.prim(.take_first, &.{ try f.k12(), try f.lit(9) }, f.list_ty);
            }
        }.b } },
    };
    inline for (cases) |c| try expectStep(c.c, .list_build, c.m, &.{c.want});
}

test "N17d: a concat chain merges its adjacent known lists, and meets the chain written merged" {
    // `xs ++ [k] ++ [1]`, with `xs` not known, is `xs ++ [k, 1]`.
    var prints: [2][]u8 = undefined;
    inline for (.{ false, true }, 0..) |merged, i| {
        var f: Fixture = undefined;
        try f.init(false);
        defer f.deinit();
        const r = try f.b.beginRow(&.{ f.u64_ty, f.list_ty }, f.list_ty);
        const v = if (merged)
            try f.prim(.concat, &.{ Ref.rowParam(1), try f.list(&.{ Ref.rowParam(0), try f.lit(1) }) }, f.list_ty)
        else
            try f.prim(.concat, &.{ Ref.rowParam(1), try f.list(&.{Ref.rowParam(0)}), try f.list(&.{try f.lit(1)}) }, f.list_ty);
        try f.b.endRow(.{ .value = &.{v} });
        prints[i] = try f.site(r);
    }
    defer for (prints) |p| testing.allocator.free(p);
    try testing.expectEqualStrings(prints[1], prints[0]);
    try testing.expect(std.mem.find(u8, prints[0], "List.concat(p1, n") != null);
}

test "N17d: List.repeat at a literal length of B is a List node, and of B + 1 stays" {
    try expectStep(.{ .result = .list, .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.repeat, &.{ Ref.rowParam(0), try f.lit(max_unrolled) }, f.list_ty);
        }
    }.b }, .list_build, "List.repeat(", &.{"list("});
    const above = try expectCase(.{ .result = .list, .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.repeat, &.{ Ref.rowParam(0), try f.lit(max_unrolled + 1) }, f.list_ty);
        }
    }.b }, null, &.{"List.repeat("}, &.{});
    testing.allocator.free(above);
}

test "N17e: map, map2 and map_with_index of known lists with a known function are the List node of the calls" {
    try expectStep(.{ .result = .list, .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.map, &.{ try f.k12(), try f.inc() }, f.list_ty);
        }
    }.b }, .list_map, "List.map(", &.{ "list(", "call r" });
    // The result is as long as the shorter list.
    const shorter = try expectCase(.{ .result = .list, .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.map2, &.{ try f.k12(), try f.list(&.{ try f.lit(5), try f.lit(6) }), try f.mix() }, f.list_ty);
        }
    }.b }, null, &.{"list("}, &.{"List.map2("});
    defer testing.allocator.free(shorter);
    try testing.expectEqual(@as(usize, 2), std.mem.count(u8, shorter, "= call r"));
    try expectStep(.{ .result = .list, .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.map_with_index, &.{ try f.k12(), try f.mix() }, f.list_ty);
        }
    }.b }, .list_map, "List.map_with_index(", &.{ "list(", "call r" });
}

test "N17e: keep_if whose every predicate value is a literal is the kept elements; one value that is not a literal keeps the builtin" {
    try expectStep(.{ .result = .list, .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.keep_if, &.{ try f.list(&.{ try f.lit(1), try f.lit(5), try f.lit(2), try f.lit(9) }), try f.big() }, f.list_ty);
        }
    }.b }, .list_map, "List.keep_if(", &.{"list("});
    const stays = try expectCase(.{ .result = .list, .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.keep_if, &.{ try f.list(&.{ try f.lit(5), Ref.rowParam(0) }), try f.big() }, f.list_ty);
        }
    }.b }, null, &.{"List.keep_if("}, &.{});
    testing.allocator.free(stays);
}

test "N17f: fold, fold_rev, sum, any and all over a known list are the chain of calls, plus, Or and And" {
    try expectStep(.{ .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.fold, &.{ try f.k12(), try f.lit(4), try f.mix() }, f.u64_ty);
        }
    }.b }, .list_fold, "List.fold(", &.{"call r"});
    try expectStep(.{ .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.fold_rev, &.{ try f.k12(), try f.lit(4), try f.mix() }, f.u64_ty);
        }
    }.b }, .list_fold, "List.fold_rev(", &.{"call r"});
    // Each call takes its element's index as a literal; `k * 2` overflows
    // at the greatest `U64`, as the builtin's first call does.
    const indexed = try expectCase(.{ .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.fold_with_index, &.{ try f.k12(), try f.lit(4), try f.mixIndexed() }, f.u64_ty);
        }
    }.b }, null, &.{"call r"}, &.{"List.fold_with_index("});
    defer testing.allocator.free(indexed);
    try testing.expectEqual(@as(usize, 3), std.mem.count(u8, indexed, "= call r"));
    try expectStep(.{ .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.fold_with_index, &.{ try f.k12(), Ref.rowParam(0), try f.mixIndexed() }, f.u64_ty);
        }
    }.b }, .list_fold, "List.fold_with_index(", &.{"call r"});
    // Over `[]` it is the initial state.
    try expectStep(.{ .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.fold_with_index, &.{ try f.list(&.{}), Ref.rowParam(0), try f.mixIndexed() }, f.u64_ty);
        }
    }.b }, .list_fold, "List.fold_with_index(", &.{"value p0"});
    // `k + 1 + 2` crashes where `k + 1` overflows, as the sum does.
    try expectStep(.{ .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.sum, &.{try f.k12()}, f.u64_ty);
        }
    }.b }, .list_fold, "List.sum(", &.{"Num.U64.plus("});
    try expectStep(.{ .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return f.prim(.sum, &.{try f.list(&.{})}, f.u64_ty);
        }
    }.b }, .list_fold, "List.sum(", &.{"value n0"});
    inline for (.{ .any, .all }) |m| {
        try expectStep(.{ .result = .bool_, .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                return f.prim(m, &.{ try f.list(&.{ Ref.rowParam(0), try f.lit(9) }), try f.big() }, f.bool_ty);
            }
        }.b }, .list_fold, "List." ++ @tagName(m) ++ "(", &.{"call r"});
    }
}

// `|k| { var $s = k; for x in list { $s = $s * 2 + x }; $s }`, with an
// early exit when `brk`: `if x == 7 { break }`.
fn loopOver(f: *Fixture, list: Ref, brk: bool) !Ref {
    const body = try f.b.openRegion(.loop_body, &.{ f.u64_ty, f.u64_ty, f.u64_ty });
    try f.b.noteListLoop(body, list);
    const x = Ref.regionParam(body, 1);
    const s = Ref.regionParam(body, 2);
    const twice = try f.b.call(.u64, .times, &.{ s, try f.lit(2) });
    const next = try f.b.call(.u64, .plus, &.{ twice, x });
    if (brk) {
        const t = try f.b.call(.u64, .is_eq, &.{ x, try f.lit(7) });
        var arms: [2]RegionId = undefined;
        arms[0] = try f.b.openArm(t, 0);
        try f.b.close(.{ .continue_ = &.{next} });
        arms[1] = try f.b.openArm(t, 1);
        try f.b.close(.{ .break_ = &.{s} });
        try f.b.close(.{ .branch = try f.b.exitingSwitch(t, &arms, &.{}, &.{}) });
    } else try f.b.close(.{ .continue_ = &.{next} });
    return f.b.loopOf(.for_list, &.{ list, Ref.rowParam(0) }, body, &.{f.u64_ty});
}

fn listOfLength(f: *Fixture, n: usize) !Ref {
    const items = try testing.allocator.alloc(Ref, n);
    defer testing.allocator.free(items);
    for (items, 0..) |*it, i| it.* = try f.lit(@intCast(i % 5));
    return f.list(items);
}

test "N17g: a ForList over a known list of at most B elements is its body once per element; above B, or with a Break, it stays" {
    try expectStep(.{ .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return loopOver(f, try f.k12(), false);
        }
    }.b }, .list_unroll, "for_list(", &.{"Num.U64.plus("});
    try expectStep(.{ .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return loopOver(f, try listOfLength(f, max_unrolled), false);
        }
    }.b }, .list_unroll, "for_list(", &.{"Num.U64.plus("});
    const above = try expectCase(.{ .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return loopOver(f, try listOfLength(f, max_unrolled + 1), false);
        }
    }.b }, null, &.{"for_list("}, &.{});
    testing.allocator.free(above);
    const broken = try expectCase(.{ .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            return loopOver(f, try f.list(&.{ try f.lit(1), try f.lit(7), Ref.rowParam(0) }), true);
        }
    }.b }, null, &.{"for_list("}, &.{});
    testing.allocator.free(broken);
}

test "N17 pairs: a fold over a known list is the loop over it unrolled (N17f, N17g)" {
    // `[k, 1, 2].fold(k, |s, x| s * 2 + x)` and the `for` that computes it.
    var prints: [2][]u8 = undefined;
    inline for (.{ false, true }, 0..) |looped, i| {
        var f: Fixture = undefined;
        try f.init(false);
        defer f.deinit();
        const r = try f.b.beginRow(&.{f.u64_ty}, f.u64_ty);
        const v = if (looped) try loopOver(&f, try f.k12(), false) else try f.prim(.fold, &.{ try f.k12(), Ref.rowParam(0), try f.mix() }, f.u64_ty);
        try f.b.endRow(.{ .value = &.{v} });
        _ = try driver.runTo(testing.allocator, &f.b, r, &.{}, .inline_);
        var out: std.Io.Writer.Allocating = .init(testing.allocator);
        errdefer out.deinit();
        try dump.dumpSite(&out.writer, testing.allocator, &f.store, &f.types, r);
        prints[i] = try out.toOwnedSlice();
    }
    defer for (prints) |p| testing.allocator.free(p);
    try testing.expectEqualStrings(prints[0], prints[1]);
}

test "N17 pairs: N17 with N13 and N15a" {
    // N13c: a switch on the length of a known list is decided.
    const decided = try expectCase(.{ .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            const len = try f.prim(.len, &.{try f.k12()}, f.u64_ty);
            const t = try f.b.call(.u64, .is_eq, &.{ len, try f.lit(3) });
            var arms: [2]RegionId = undefined;
            for (&arms, 0..) |*a, key| {
                a.* = try f.b.openArm(t, @intCast(key));
                try f.b.close(.{ .value = &.{if (key == 1) Ref.rowParam(0) else try f.lit(0)} });
            }
            return f.b.switchOn(t, &arms, &.{}, &.{f.u64_ty}, &.{});
        }
    }.b }, null, &.{"value p0"}, &.{ "switch", "List.len(" });
    testing.allocator.free(decided);
    // N15a: a concat chain that drops `[]` and merges what is known.
    const chained = try expectCase(.{ .result = .list, .body = struct {
        fn b(f: *Fixture) anyerror!Ref {
            const inner = try f.prim(.concat, &.{ try f.list(&.{}), try f.list(&.{Ref.rowParam(0)}) }, f.list_ty);
            return f.prim(.concat, &.{ inner, try f.list(&.{try f.lit(1)}) }, f.list_ty);
        }
    }.b }, null, &.{"list(p0, n"}, &.{"List.concat("});
    testing.allocator.free(chained);
}

test "N13c on Try.ok_or: ok_or of a known tag is its payload or the fallback, and the knockout stops it" {
    inline for (.{ false, true }) |empty| {
        try expectStep(.{ .body = struct {
            fn b(f: *Fixture) anyerror!Ref {
                const t = try f.prim(.first, &.{if (empty) try f.list(&.{}) else try f.k12()}, f.first_ty);
                return f.b.primOf(prims.find(.try_, .ok_or).?, &.{ t, try f.lit(7) }, f.u64_ty);
            }
        }.b }, .known_ok_or, "Try.ok_or(", &.{if (empty) "= 7 : U64" else "value p0"});
    }
}

// `Str.from_interpolation`'s assembler (`Builtin.roc`) over the known
// `segments` and the values `values`: `segments.first().ok_or("")`, folded
// over the values with `|acc, v, i| acc.concat(v).concat(segments.get(i + 1).ok_or(""))`.
// The function's row builds the segments it captures in Roc.
fn assemble(f: *Fixture, segments: []const []const u8, values: []const Ref) !Ref {
    const b = &f.b;
    const str = try f.types.strTy();
    const oob = try f.types.tagUnionTy(&.{.{ .name = "OutOfBounds", .payload = &.{} }});
    const empty = try f.types.tagUnionTy(&.{.{ .name = "ListWasEmpty", .payload = &.{} }});
    const get_ty = try f.types.tagUnionTy(&.{ .{ .name = "Ok", .payload = &.{str} }, .{ .name = "Err", .payload = &.{oob} } });
    const first_ty = try f.types.tagUnionTy(&.{ .{ .name = "Ok", .payload = &.{str} }, .{ .name = "Err", .payload = &.{empty} } });
    const list_ty = try f.types.listTy(str);
    const ok_or = prims.find(.try_, .ok_or).?;
    const concat_str = prims.find(.str, .concat).?;
    const segs = struct {
        fn of(fx: *Fixture, ty: TyId, texts: []const []const u8) !Ref {
            const items = try testing.allocator.alloc(Ref, texts.len);
            defer testing.allocator.free(items);
            for (items, texts) |*it, t| it.* = try fx.b.litStr(t);
            return fx.b.listOf(ty, items);
        }
    };
    const held = b.suspendRow();
    const step = try b.beginRow(&.{ str, str, f.u64_ty }, str);
    const at = try b.call(.u64, .plus, &.{ Ref.rowParam(2), try f.lit(1) });
    const next = try b.primOf(prims.find(.list, .get).?, &.{ try segs.of(f, list_ty, segments), at }, get_ty);
    const joined = try b.primOf(concat_str, &.{ Ref.rowParam(0), Ref.rowParam(1) }, str);
    const out = try b.primOf(concat_str, &.{ joined, try b.primOf(ok_or, &.{ next, try b.litStr("") }, str) }, str);
    try b.endRow(.{ .value = &.{out} });
    b.resumeRow(held);
    const clo = try b.closure(step, &.{}, try f.types.funcTy(&.{ str, str, f.u64_ty }, str));
    const first = try b.primOf(prims.find(.list, .first).?, &.{try segs.of(f, list_ty, segments)}, first_ty);
    const init = try b.primOf(ok_or, &.{ first, try b.litStr("") }, str);
    return b.primOf(prims.find(.list, .fold_with_index).?, &.{ try b.listOf(list_ty, values), init, clo }, str);
}

test "N17 pairs: Str's assembler over known segments is the flat Str.concat chain without empty segments (N17f, N17b, N13c, N15a)" {
    const cases = [_][]const []const u8{
        &.{ "a", "b" },
        &.{ "", "" },
        &.{ "a", "", "c" },
        &.{ "", "x", "" },
        &.{ "", "", "", "" },
    };
    const inputs = [_][]const u8{ "", "<p>", "z" };
    inline for (cases) |segments| {
        const n = segments.len - 1;
        var params: [n]TyId = undefined;
        var values: [n]Ref = undefined;
        var prints: [2][]u8 = undefined;
        var raw: Fixture = undefined;
        try raw.init(true);
        defer raw.deinit();
        for (&params, &values, 0..) |*p, *v, i| {
            p.* = try raw.types.strTy();
            v.* = Ref.rowParam(@intCast(i));
        }
        const raw_root = try raw.b.beginRow(&params, try raw.types.strTy());
        try raw.b.endRow(.{ .value = &.{try assemble(&raw, segments, &values)} });
        inline for (.{ false, true }, 0..) |written, w| {
            var f: Fixture = undefined;
            try f.init(false);
            defer f.deinit();
            const fx = &f;
            const r = try fx.b.beginRow(&params, try fx.types.strTy());
            const v = if (written) blk: {
                // `"s0".concat(p0).concat("s1")...`, as the author writes it.
                var acc = try fx.b.litStr(segments[0]);
                for (values, segments[1..]) |x, s| {
                    acc = try fx.b.call(.str, .concat, &.{ acc, x });
                    acc = try fx.b.call(.str, .concat, &.{ acc, try fx.b.litStr(s) });
                }
                break :blk acc;
            } else try assemble(fx, segments, &values);
            try fx.b.endRow(.{ .value = &.{v} });
            _ = try driver.runTo(testing.allocator, &fx.b, r, &.{}, .inline_);
            var report = try verify.verifyAll(testing.allocator, &fx.store, &fx.types);
            defer report.deinit();
            try testing.expect(report.ok());
            var out: std.Io.Writer.Allocating = .init(testing.allocator);
            errdefer out.deinit();
            try dump.dumpSite(&out.writer, testing.allocator, &fx.store, &fx.types, r);
            prints[w] = try out.toOwnedSlice();
            if (!written) {
                // Soundness: every input, empty strings included, gives what
                // the assembler gives without the rules.
                var arena = std.heap.ArenaAllocator.init(testing.allocator);
                defer arena.deinit();
                for (inputs) |x0| for (inputs) |x1| {
                    var args: [n]eval.Value = undefined;
                    for (&args, 0..) |*a, i| a.* = .{ .str = if (i % 2 == 0) x0 else x1 };
                    var e0 = try eval.Evaluator.init(arena.allocator(), &raw.store, &raw.types, .strict);
                    var e1 = try eval.Evaluator.init(arena.allocator(), &fx.store, &fx.types, .strict);
                    try testing.expect((try e0.run(raw_root, &args)).eql(try e1.run(r, &args)));
                };
            }
        }
        defer for (prints) |p| testing.allocator.free(p);
        try testing.expectEqualStrings(prints[1], prints[0]);
        for ([_][]const u8{ "fold", "ok_or", "List.", "\"\" : Str" }) |gone| try testing.expect(std.mem.find(u8, prints[0], gone) == null);
    }
}
