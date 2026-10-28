//! Scrutinee polarity (normal-form 3.13, N13s): whether a switch reads
//! better on the negation of its scrutinee, with its arms swapped. The
//! builder's condition and the measure's `flipping_scrutinees` component
//! both read it from here, so the rule lowers exactly what the measure counts.

const ir = @import("ir.zig");
const types_mod = @import("types.zig");
const prims = @import("prims.zig");

const Ref = ir.Ref;
const RegionId = ir.RegionId;

/// The leaves of a `Bool` value, through the operands of its `And` and `Or`
/// nodes and the arms of its `Bool` switches.
pub const Leaves = struct {
    negated: u32 = 0,
    plain: u32 = 0,
    /// Integer `is_lte` leaves, which a negation flips to `is_lt` (N13q).
    lte: u32 = 0,
    lt: u32 = 0,
    /// Whether the first leaf is a `Bool.not` or an integer `is_lte`.
    first_flips: ?bool = null,

    fn add(l: *Leaves, leaf_flips: bool, class: enum { negated, plain, lte, lt }) void {
        if (l.first_flips == null) l.first_flips = leaf_flips;
        switch (class) {
            .negated => l.negated += 1,
            .plain => l.plain += 1,
            .lte => l.lte += 1,
            .lt => l.lt += 1,
        }
    }
};

/// The value region `r` ends in, if it ends in one value.
pub fn armValue(store: *const ir.Store, r: RegionId) ?Ref {
    const end = store.region(r).end;
    if (end.kind != .value or end.refs.len != 1) return null;
    return store.refSlice(end.refs)[0];
}

/// The arms of a single-output `Bool` switch without joins whose arms all
/// end in a value, the switches a negation passes into.
pub fn boolArms(store: *const ir.Store, types: *const types_mod.Types, n: ir.Node) ?[]const RegionId {
    if (n.tys.len != 1 or types.get(store.tySlice(n.tys)[0]) != .bool_) return null;
    const regions = store.regionSlice(n.regions);
    if (regions.len != n.payload) return null;
    for (regions) |r| if (armValue(store, r) == null) return null;
    return regions;
}

/// The leaves of `ref`.
pub fn leavesOf(store: *const ir.Store, types: *const types_mod.Types, ref: Ref) Leaves {
    var l: Leaves = .{};
    collect(store, types, ref, &l);
    return l;
}

fn collect(store: *const ir.Store, types: *const types_mod.Types, ref: Ref, l: *Leaves) void {
    if (ref.kind != .node) return l.add(false, .plain);
    const n = store.node(ref.nodeId());
    switch (n.op) {
        .and_, .or_ => {
            collect(store, types, store.refSlice(n.args)[0], l);
            for (store.regionSlice(n.regions)) |r| collect(store, types, armValue(store, r).?, l);
        },
        .switch_ => if (boolArms(store, types, n)) |arms| {
            for (arms) |r| collect(store, types, armValue(store, r).?, l);
        } else l.add(false, .plain),
        .prim => {
            const p = prims.lookup(ir.PrimId.of(n.payload)) orelse return l.add(false, .plain);
            // Only an integer comparison takes a negation as the flipped comparison (N13q).
            switch (p.method) {
                .not => l.add(true, .negated),
                .is_lte => if (p.owner.int() != null) l.add(true, .lte) else l.add(false, .plain),
                .is_lt => if (p.owner.int() != null) l.add(false, .lt) else l.add(false, .plain),
                .is_eq, .is_gt, .is_gte, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect, .first, .last, .prepend, .single, .with_capacity, .set, .drop_first, .take_first, .repeat, .map2, .map_with_index, .fold_rev, .sum, .any, .all => l.add(false, .plain),
            }
        },
        .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .call, .for_range, .for_list, .loop, .lambda, .apply => l.add(false, .plain),
    }
}

/// Whether a switch on `ref` flips to one on its negation. On a scrutinee in
/// negation normal form the negation drops every `Bool.not` leaf, puts one
/// on every plain leaf, flips every integer comparison, and turns an `And`
/// root into an `Or`, so each test below gives the opposite answer on it and
/// a switch flips at most once. A `Bool.not` over a connective is one leaf
/// whose negation exposes its operands; that flip lowers the measure's
/// earlier `negated_connectives` component instead.
pub fn flips(store: *const ir.Store, types: *const types_mod.Types, ref: Ref) bool {
    const l = leavesOf(store, types, ref);
    if (l.negated != l.plain) return l.negated > l.plain;
    if (l.lte != l.lt) return l.lte > l.lt;
    if (ref.kind != .node) return false;
    const n = store.node(ref.nodeId());
    return switch (n.op) {
        .and_, .or_ => n.op == .or_,
        .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .switch_, .for_range, .for_list, .loop, .lambda, .apply => l.first_flips.?,
    };
}

/// Whether a switch has the shape of a `Bool` switch pattern: two arms, no
/// joins, one output, no keys, on a `Bool`.
pub fn isBoolSwitch(types: *const types_mod.Types, scrutinee_ty: ir.TyId, arms: u32, regions: usize, outputs: usize, keys: usize) bool {
    return arms == 2 and regions == 2 and outputs == 1 and keys == 0 and types.get(scrutinee_ty) == .bool_;
}
