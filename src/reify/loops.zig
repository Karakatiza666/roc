//! The loop rules (normal-form 3.11, 3.12; plan 3.4).
//!
//! | Step | Rule | Here |
//! |---|---|---|
//! | N12 | a row whose every call to itself is a tail call becomes a row whose body is one `Loop` | `tailSites`, applied by `rebuild.runTail` |
//! | N11g | a slot every `Continue` passes unchanged is its initial value | `Ctx.fates` |
//! | N11h | a slot nothing after the loop, no other slot and no exit reads is removed | `Ctx.fates` |
//! | N11i | slots with equal initial values and equal next values under the assumption that they are equal are one slot | `Ctx.fates` |
//! | N11j | a general loop's outputs that nothing reads are not carried by its `Break`s; a `Return` in a loop that is its row's result is a `Break` | `Ctx.sameKind` |
//! | N11k | a loop over `List.iter(xs)` is `ForList(xs)` | `Ctx.iteratorToList` |
//! | N11l | a `Loop` that tests a counter against a bound and steps it by one is `ForRange`; `ForRange(0, List.len(xs))` is `ForList(xs)` | `Ctx.raiseCounter`, `Ctx.rangeToList` |
//! | N14b | a record or tuple slot that the body only reads by field or index, and every `Continue` gives as a construction, is one slot per component | `Ctx.splitSlots` |
//!
//! The rules are hooks on the rebuild (`rebuild.zig`). `analyze` reads one
//! loop of the row as the last round left it, and says how the rebuild
//! copies it instead: a `Rewrite`. The rebuild builds the new loop through
//! the smart constructors, so what the rewrite enables fires in the same
//! round. At most one family of rules applies to a loop in a round: slots
//! and outputs first, then a change of kind. A rule that needs the other's
//! result waits for the next round, and the measure (`measure.zig`) falls in
//! each.
//!
//! A bounded loop (`ForRange`, `ForList`) has one output per slot, which is
//! the slot as it stands when the indices run out, and a `Break` carries
//! them. A general `Loop` ends only in `Break` or `Return`, so its outputs
//! are the values its `Break`s carry, free of its slots.

const std = @import("std");
const ir = @import("ir.zig");
const types_mod = @import("types.zig");
const prims = @import("prims.zig");
const place = @import("place.zig");
const live_mod = @import("live.zig");
const scalar = @import("scalar.zig");

const Allocator = std.mem.Allocator;
const Ref = ir.Ref;
const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const RowId = ir.RowId;
const TyId = ir.TyId;
const Types = types_mod.Types;

/// What an old body parameter is in the loop a rewrite builds.
pub const ParamTo = union(enum) {
    /// Parameter `k` of the new body.
    param: u32,
    /// The initial value of old slot `k`: no `Continue` changes the slot.
    init: u32,
    /// What old body parameter `k` stands for: the two slots are equal.
    same_as: u32,
    /// Nothing reads it.
    gone,
    /// The slot is split (N14b): its components are parameters, and nothing
    /// reads the slot as one value.
    split,
};

/// What an old output of the loop is in the loop a rewrite builds.
pub const OutputTo = union(enum) {
    /// Output `k` of the new node.
    output: u32,
    /// The initial value of old slot `k`.
    init: u32,
    /// What old output `k` is.
    same_as: u32,
    /// Every `Break` gives this value, which is defined outside the loop.
    value: Ref,
    /// Nothing reads it.
    gone,
    /// The aggregate of old slot `k` (N14b), built after the loop from the
    /// outputs that hold its components.
    rebuilt: u32,
};

/// How a rewrite that splits slots (N14b) replaces them.
pub const Split = struct {
    /// How much of each old slot splits.
    shapes: []const scalar.Shape,
    /// The new slots in order: the old slot, and the components to read from
    /// it. The new loop has one output for each of them when it is bounded.
    parts: []const scalar.Leaf,
    /// The type of each old slot.
    slot_tys: []const TyId,
    /// Per old slot: where its first part stands among the parts.
    first: []const u32,
};

/// A node that stands for a parameter of the new body.
pub const Stands = struct { node: NodeId, param: u32 };

/// How the rebuild copies one loop: the loop it builds, and what of the
/// old one it keeps. Every ref is in the old row; the rebuild maps them.
pub const Rewrite = struct {
    /// The old body, whose parameters `params` maps.
    body: RegionId,
    op: ir.Op,
    payload: u32,
    /// The header arguments of the new node: the bounds, or the list.
    header: []const Ref,
    /// The old slots the new loop keeps, in order. `Continue` carries their
    /// next values, and the new node's slot arguments are their initial values.
    slots: []const u32,
    /// The types of the new body's parameters.
    param_tys: []const TyId,
    /// The types of the new node's outputs.
    out_tys: []const TyId,
    /// Per old body parameter.
    params: []const ParamTo,
    /// Per old output.
    outputs: []const OutputTo,
    /// The positions of the old `Break`s' values the new `Break`s keep, in order.
    break_keep: []const u32,
    /// Nodes of the old body that the header reads: built before the loop.
    hoist: []const NodeId,
    /// The region whose nodes and end the new body continues in after the old
    /// body's own nodes, or null when the new body ends as the old one did.
    continue_in: ?RegionId,
    /// Nodes of the old body the new loop does not build.
    skip: []const NodeId,
    /// Nodes that stand for a parameter of the new body.
    stands: []const Stands,
    /// Whether a `Return` on the loop's own paths becomes a `Break` of its value (N11j).
    returns_break: bool,
    /// Where set, the new slots are the parts of this, and `slots` lists all
    /// the old slots.
    split: ?*const Split = null,
};

/// The context `analyze` reads one loop in.
pub const Where = struct {
    /// The body of the row the rebuild builds, as it stood before the rebuild,
    /// when the loop is in that row and not in a body being inlined or in a
    /// lambda. A rule that reads the row's result (N11j) applies only then.
    row_body: ?RegionId,
    /// How the nodes of the row and the ends of its regions use values.
    usage: *const scalar.Usage,
};

/// How `analyze` finds a loop: the plan of its row and the types.
pub fn analyze(a: Allocator, p: *const place.Plan, types: *Types, n: NodeId, where: Where) Allocator.Error!?Rewrite {
    var c: Ctx = .{ .a = a, .p = p, .store = p.store, .types = types, .n = n, .nd = p.store.node(n), .where = where };
    return c.run();
}

const Ctx = struct {
    a: Allocator,
    p: *const place.Plan,
    store: *const ir.Store,
    types: *Types,
    n: NodeId,
    nd: ir.Node,
    where: Where,
    row: RowId = undefined,
    body: RegionId = undefined,
    /// Leading arguments before the slots' initial values.
    lead: u32 = 0,
    /// Leading body parameters before the slots.
    header: u32 = 0,
    slot_count: u32 = 0,
    args: []const Ref = &.{},
    /// The regions on the loop's own paths, and the terminators they end in.
    spine: std.ArrayList(RegionId) = .empty,
    conts: std.ArrayList(RegionId) = .empty,
    breaks: std.ArrayList(RegionId) = .empty,
    returns: std.ArrayList(RegionId) = .empty,
    out_read: []bool = &.{},

    fn run(c: *Ctx) Allocator.Error!?Rewrite {
        const store = c.store;
        c.row = store.region(c.nd.region).row;
        c.body = store.regionSlice(c.nd.regions)[0];
        c.lead = switch (c.nd.op) {
            .for_range => 2,
            .for_list => 1,
            .loop => 0,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .lambda, .apply => unreachable, // analyze is called for loops
        };
        c.header = switch (c.nd.op) {
            .for_range => 1,
            .for_list => 2,
            .loop => 0,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .lambda, .apply => unreachable, // analyze is called for loops
        };
        c.args = store.refSlice(c.nd.args);
        c.slot_count = @intCast(c.args.len - c.lead);
        try c.collect(c.body);
        c.out_read = try c.outputsRead();
        if (try c.sameKind()) |rw| return rw;
        if (try c.splitSlots()) |rw| return rw;
        switch (c.nd.op) {
            .loop => {
                if (try c.raiseCounter()) |rw| return rw;
                if (try c.iteratorToList()) |rw| return rw;
            },
            .for_range => if (try c.rangeToList()) |rw| return rw,
            .for_list => {},
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .lambda, .apply => unreachable, // analyze is called for loops
        }
        return null;
    }

    // The regions on the loop's own paths from `start`: it, and the arms and
    // joins of the exiting switches its paths end in. A region holds a loop
    // or a lambda's own paths apart: they are not walked.
    fn collect(c: *Ctx, start: RegionId) Allocator.Error!void {
        c.spine.clearRetainingCapacity();
        c.conts.clearRetainingCapacity();
        c.breaks.clearRetainingCapacity();
        c.returns.clearRetainingCapacity();
        try c.spine.append(c.a, start);
        var at: usize = 0;
        while (at < c.spine.items.len) : (at += 1) {
            const r = c.spine.items[at];
            const end = c.store.region(r).end;
            switch (end.kind) {
                .branch => try c.spine.appendSlice(c.a, c.store.regionSlice(c.store.node(NodeId.of(end.target)).regions)),
                .continue_ => try c.conts.append(c.a, r),
                .break_ => try c.breaks.append(c.a, r),
                .return_ => try c.returns.append(c.a, r),
                .open, .value, .jump => {},
            }
        }
    }

    fn param(c: *const Ctx, k: u32) Ref {
        return Ref.regionParam(c.body, @intCast(k));
    }

    // The slot a body parameter reads, or null for the index and the element.
    fn slotOf(c: *const Ctx, ref: Ref) ?u32 {
        if (ref.kind != .region_param or ref.regionId() != c.body or ref.output < c.header) return null;
        return ref.output - c.header;
    }

    fn endRefs(c: *const Ctx, r: RegionId) []const Ref {
        return c.store.refSlice(c.store.region(r).end.refs);
    }

    fn slotTy(c: *const Ctx, k: u32) TyId {
        return c.store.tySlice(c.store.region(c.body).params)[c.header + k];
    }

    // Which outputs of the loop something reads.
    fn outputsRead(c: *Ctx) Allocator.Error![]bool {
        const read = try c.a.alloc(bool, c.nd.tys.len);
        @memset(read, false);
        const sites = c.p.uses.get(c.n) orelse return read;
        for (sites.items) |site| {
            const refs = switch (site) {
                .node => |m| c.store.refSlice(c.store.node(m).args),
                .region => |r| c.endRefs(r),
            };
            for (refs) |ref| if (ref.kind == .node and ref.nodeId() == c.n) {
                read[ref.output] = true;
            };
        }
        return read;
    }

    // Whether the loop's value is its row's result: the row body ends in one
    // output of it. Gives that output.
    fn resultOutput(c: *const Ctx) ?u32 {
        const row_body = c.where.row_body orelse return null;
        if (c.nd.region != row_body) return null;
        const end = c.store.region(row_body).end;
        if (end.kind != .value or end.refs.len != 1) return null;
        const ref = c.store.refSlice(end.refs)[0];
        if (ref.kind != .node or ref.nodeId() != c.n) return null;
        return ref.output;
    }

    // What the loop's slots and outputs are. N11g, N11h, N11i and the outputs
    // of N11j: one rewrite of the same kind, or null when nothing changes.
    fn sameKind(c: *Ctx) Allocator.Error!?Rewrite {
        const slots = c.slot_count;
        const bounded = c.nd.op != .loop;
        const outs = c.nd.tys.len;
        const Fate = union(enum) { keep, constant, dead, same_as: u32 };
        const fates = try c.a.alloc(Fate, slots);
        @memset(fates, .keep);

        // N11g: every `Continue` passes the slot as it is. A bounded loop's
        // output is the slot too, so a `Break` that gives the output another
        // value keeps the slot unless nothing reads the output.
        for (fates, 0..) |*fate, k| {
            const me = c.param(c.header + @as(u32, @intCast(k)));
            const unchanged = for (c.conts.items) |r| {
                if (c.endRefs(r)[k] != me) break false;
            } else true;
            if (!unchanged) continue;
            if (bounded and c.out_read[k]) {
                const same = for (c.breaks.items) |r| {
                    if (c.endRefs(r)[k] != me) break false;
                } else true;
                if (!same) continue;
            }
            fate.* = .constant;
        }

        // N11h: what the loop reads of the slots, from what it gives out.
        const needed = try c.neededSlots(fates.len);
        for (fates, needed) |*fate, need| if (fate.* == .keep and !need) {
            fate.* = .dead;
        };

        // N11i: optimistic value numbering over the slots still kept.
        const class = try c.a.alloc(u32, slots);
        for (class, 0..) |*cl, k| cl.* = @intCast(k);
        for (0..slots) |k| {
            if (fates[k] != .keep) continue;
            for (0..k) |j| {
                if (fates[j] != .keep or class[j] != j) continue;
                if (c.slotTy(@intCast(j)) == c.slotTy(@intCast(k)) and c.args[c.lead + j] == c.args[c.lead + k]) {
                    class[k] = @intCast(j);
                    break;
                }
            }
        }
        try c.refine(fates, class);
        for (0..slots) |k| if (fates[k] == .keep and class[k] != k) {
            fates[k] = .{ .same_as = class[k] };
        };

        // The outputs of a general loop that nothing reads. A row's result
        // that is a loop carries a `Return` as a `Break` (N11j).
        const result = if (c.nd.op == .loop) c.resultOutput() else null;
        var keep_outputs: std.ArrayList(u32) = .empty;
        var narrowed = false;
        var cone: std.ArrayList(NodeId) = .empty;
        const outside_value = try c.a.alloc(?Ref, outs);
        @memset(outside_value, null);
        if (bounded) {
            for (fates, 0..) |fate, k| if (fate == .keep) try keep_outputs.append(c.a, @intCast(k));
        } else {
            for (c.out_read, 0..) |read, o| {
                if (!read) {
                    narrowed = true;
                } else if (try c.sameOutside(@intCast(o), &cone)) |value| {
                    outside_value[o] = value;
                    narrowed = true;
                } else try keep_outputs.append(c.a, @intCast(o));
            }
        }
        var returns_break = false;
        if (result) |k| {
            const row_result = c.store.row(c.row).result;
            if (keep_outputs.items.len == 1 and keep_outputs.items[0] == k and c.returns.items.len > 0 and c.store.tySlice(c.nd.tys)[k] == row_result) returns_break = true;
        }

        var changed = narrowed or returns_break;
        for (fates) |fate| if (fate != .keep) {
            changed = true;
        };
        if (!changed) return null;

        // The kept slots and what each old parameter and output becomes.
        var kept: std.ArrayList(u32) = .empty;
        const new_of = try c.a.alloc(u32, slots);
        @memset(new_of, std.math.maxInt(u32));
        for (fates, 0..) |fate, k| if (fate == .keep) {
            new_of[k] = @intCast(kept.items.len);
            try kept.append(c.a, @intCast(k));
        };
        const params = try c.a.alloc(ParamTo, c.header + slots);
        for (params[0..c.header], 0..) |*to, k| to.* = .{ .param = @intCast(k) };
        for (fates, 0..) |fate, k| {
            params[c.header + k] = switch (fate) {
                .keep => .{ .param = c.header + new_of[k] },
                .constant => .{ .init = @intCast(k) },
                .dead => .gone,
                .same_as => |j| .{ .same_as = c.header + j },
            };
        }
        const outputs = try c.a.alloc(OutputTo, outs);
        var out_tys: std.ArrayList(TyId) = .empty;
        if (bounded) {
            for (outputs, fates, 0..) |*to, fate, k| {
                to.* = switch (fate) {
                    .keep => .{ .output = new_of[k] },
                    .constant => .{ .init = @intCast(k) },
                    .dead => .gone,
                    .same_as => |j| .{ .same_as = j },
                };
            }
            for (kept.items) |k| try out_tys.append(c.a, c.store.tySlice(c.nd.tys)[k]);
        } else {
            @memset(outputs, .gone);
            for (outside_value, outputs) |value, *to| if (value) |v| {
                to.* = .{ .value = v };
            };
            for (keep_outputs.items, 0..) |o, new| {
                outputs[o] = .{ .output = @intCast(new) };
                try out_tys.append(c.a, c.store.tySlice(c.nd.tys)[o]);
            }
        }
        const param_tys = try c.a.alloc(TyId, c.header + kept.items.len);
        const old_params = c.store.tySlice(c.store.region(c.body).params);
        @memcpy(param_tys[0..c.header], old_params[0..c.header]);
        for (kept.items, 0..) |k, i| param_tys[c.header + i] = old_params[c.header + k];
        return .{
            .body = c.body,
            .op = c.nd.op,
            .payload = c.nd.payload,
            .header = c.args[0..c.lead],
            .slots = kept.items,
            .param_tys = param_tys,
            .out_tys = out_tys.items,
            .params = params,
            .outputs = outputs,
            .break_keep = keep_outputs.items,
            .hoist = cone.items,
            .continue_in = null,
            .skip = &.{},
            .stands = &.{},
            .returns_break = returns_break,
        };
    }

    // N14b: the slots that are records or tuples and are only read by field
    // or index split into one slot per component. A slot splits when the
    // body uses it in no other way (`scalar.Usage`), and its own `Continue`s
    // give it unchanged or as a construction; a component splits again under
    // the same condition. A bounded loop gives the slot as an output, which a
    // `Break` may give from any value; the components are read from it.
    fn splitSlots(c: *Ctx) Allocator.Error!?Rewrite {
        const slots = c.slot_count;
        const bounded = c.nd.op != .loop;
        const shapes = try c.a.alloc(scalar.Shape, slots);
        var any = false;
        for (shapes, 0..) |*shape, k| {
            const tolerate: SlotEnds = .{ .c = c, .k = @intCast(k), .bounded = bounded };
            const key = scalar.regionParamKey(c.body, c.header + @as(u32, @intCast(k)));
            const found = try c.where.usage.shapeOf(c.types, key, c.slotTy(@intCast(k)), .{ .ctx = &tolerate, .ok = SlotEnds.ok });
            shape.* = try c.constrained(found, @intCast(k));
            if (shape.* != .whole) any = true;
        }
        if (!any) return null;

        const parts = try scalar.leavesOf(c.a, shapes);
        const first = try c.a.alloc(u32, slots);
        const slot_tys = try c.a.alloc(TyId, slots);
        var at: u32 = 0;
        for (shapes, first, slot_tys, 0..) |shape, *f, *t, k| {
            f.* = at;
            t.* = c.slotTy(@intCast(k));
            at += shape.leafCount();
        }
        const old_params = c.store.tySlice(c.store.region(c.body).params);
        const param_tys = try c.a.alloc(TyId, c.header + parts.len);
        @memcpy(param_tys[0..c.header], old_params[0..c.header]);
        const part_tys = try c.a.alloc(TyId, parts.len);
        for (parts, part_tys) |leaf, *t| t.* = scalar.tyAt(c.types, slot_tys[leaf.index], leaf.path);
        @memcpy(param_tys[c.header..], part_tys);

        const params = try c.a.alloc(ParamTo, c.header + slots);
        for (params[0..c.header], 0..) |*to, i| to.* = .{ .param = @intCast(i) };
        for (shapes, first, 0..) |shape, f, k| {
            params[c.header + k] = if (shape == .whole) .{ .param = c.header + f } else .split;
        }
        const outs = c.nd.tys.len;
        const outputs = try c.a.alloc(OutputTo, outs);
        const out_tys = if (bounded) part_tys else try c.a.dupe(TyId, c.store.tySlice(c.nd.tys));
        const break_keep = try c.a.alloc(u32, outs);
        for (break_keep, 0..) |*k, i| k.* = @intCast(i);
        if (bounded) {
            for (outputs, shapes, first, 0..) |*to, shape, f, k| {
                to.* = if (shape == .whole) .{ .output = f } else if (c.out_read[k]) .{ .rebuilt = @intCast(k) } else .gone;
            }
        } else for (outputs, 0..) |*to, o| {
            to.* = .{ .output = @intCast(o) };
        }
        const all_slots = try c.a.alloc(u32, slots);
        for (all_slots, 0..) |*k, i| k.* = @intCast(i);

        var stands: std.ArrayList(Stands) = .empty;
        var skip: std.ArrayList(NodeId) = .empty;
        for (shapes, first, 0..) |shape, f, k| {
            if (shape == .whole) continue;
            const key = scalar.regionParamKey(c.body, c.header + @as(u32, @intCast(k)));
            try c.collectStands(&stands, &skip, key, shape, c.header + f);
        }
        const split = try c.a.create(Split);
        split.* = .{ .shapes = shapes, .parts = parts, .slot_tys = slot_tys, .first = first };
        return .{
            .body = c.body,
            .op = c.nd.op,
            .payload = c.nd.payload,
            .header = c.args[0..c.lead],
            .slots = all_slots,
            .param_tys = param_tys,
            .out_tys = out_tys,
            .params = params,
            .outputs = outputs,
            .break_keep = break_keep,
            .hoist = &.{},
            .continue_in = null,
            .skip = skip.items,
            .stands = stands.items,
            .returns_break = false,
            .split = split,
        };
    }

    // The reads of the split value `key`, which the new parameters from
    // `base` stand for: a read of a component that stays whole is that
    // parameter, and a read of one that splits again is not built.
    fn collectStands(c: *Ctx, stands: *std.ArrayList(Stands), skip: *std.ArrayList(NodeId), key: scalar.Key, shape: scalar.Shape, base: u32) Allocator.Error!void {
        const children = shape.split;
        for (c.where.usage.readsOf(key)) |read| {
            var before: u32 = 0;
            for (children[0..read.comp]) |child| before += child.leafCount();
            switch (children[read.comp]) {
                .whole => try stands.append(c.a, .{ .node = read.node, .param = base + before }),
                .split => {
                    try skip.append(c.a, read.node);
                    try c.collectStands(stands, skip, scalar.nodeKey(read.node, 0), children[read.comp], base + before);
                },
            }
        }
    }

    // Where a slot's own uses may end a region and still let it split: the
    // `Continue`s of this loop give it at its place, and so do its `Break`s
    // when the loop is bounded, because its output is the slot.
    const SlotEnds = struct {
        c: *const Ctx,
        k: u32,
        bounded: bool,

        fn ok(ctx: *const anyopaque, use: scalar.EndUse) bool {
            const self: *const SlotEnds = @ptrCast(@alignCast(ctx));
            if (use.pos != self.k) return false;
            if (std.mem.findScalar(RegionId, self.c.conts.items, use.region) != null) return true;
            return self.bounded and std.mem.findScalar(RegionId, self.c.breaks.items, use.region) != null;
        }
    };

    // The part of `shape` that every `Continue` keeps split: the slot as it
    // is, or a construction of the type, whose components split again only
    // when they are constructions too (a fresh construction, normal-form 3.14).
    fn constrained(c: *Ctx, shape: scalar.Shape, k: u32) Allocator.Error!scalar.Shape {
        var s = shape;
        const me = c.param(c.header + k);
        for (c.conts.items) |r| s = try c.constrainValue(s, c.endRefs(r)[k], me);
        return s;
    }

    fn constrainValue(c: *Ctx, shape: scalar.Shape, v: Ref, me: ?Ref) Allocator.Error!scalar.Shape {
        const children = switch (shape) {
            .whole => return .whole,
            .split => |children| children,
        };
        if (me != null and v == me.?) return shape;
        const made = c.construction(v) orelse return .whole;
        if (made.len != children.len) return .whole;
        const out = try c.a.alloc(scalar.Shape, children.len);
        for (children, made, out) |child, component, *o| o.* = try c.constrainValue(child, component, null);
        return .{ .split = out };
    }

    // The values a `Record` or `Tuple` node that sets every member is built from.
    fn construction(c: *const Ctx, v: Ref) ?[]const Ref {
        if (v.kind != .node or v.output != 0) return null;
        const nd = c.store.node(v.nodeId());
        if ((nd.op != .record and nd.op != .tuple) or nd.aux.len != 0) return null;
        return c.store.refSlice(nd.args);
    }

    // The value every `Break` of the loop gives for output `o`, when it is
    // one loop-invariant value (N11j): the loop gives it whenever it ends, so
    // the output is that value. The nodes of the body it needs are appended
    // to `cone`, dependencies first, to be built before the loop. A node
    // that is not speculatable stays where it is, because building it before
    // the loop would run it on a path that never breaks. A loop that never
    // ends has no output, as an unread loop has no effect.
    fn sameOutside(c: *Ctx, o: u32, cone: *std.ArrayList(NodeId)) Allocator.Error!?Ref {
        if (c.breaks.items.len == 0) return null;
        const first = c.endRefs(c.breaks.items[0])[o];
        for (c.breaks.items[1..]) |r| if (c.endRefs(r)[o] != first) return null;
        return if (try c.invariant(first, cone)) first else null;
    }

    fn invariant(c: *Ctx, ref: Ref, cone: *std.ArrayList(NodeId)) Allocator.Error!bool {
        switch (ref.kind) {
            .row_param, .input => return true,
            .region_param => return !c.store.encloses(c.body, ref.regionId()),
            .node => {
                const n = ref.nodeId();
                const nd = c.store.node(n);
                if (!c.store.encloses(c.body, nd.region)) return true;
                if (!nd.flags.speculatable or nd.regions.len != 0) return false;
                if (std.mem.findScalar(NodeId, cone.items, n) != null) return true;
                for (c.store.refSlice(nd.args)) |arg| if (!try c.invariant(arg, cone)) return false;
                try cone.append(c.a, n);
                return true;
            },
        }
    }

    // N11h: per slot, whether it flows into what the loop gives out. The
    // roots are the values a read output's `Break`s carry, a `Return`'s value,
    // every value a path's decision reads, and, for a bounded loop, the slot
    // itself where its output is read. A slot flows into the next value of
    // another slot only where that slot is needed.
    fn neededSlots(c: *Ctx, slots: usize) Allocator.Error![]bool {
        const needed = try c.a.alloc(bool, slots);
        @memset(needed, false);
        var seen: std.AutoHashMapUnmanaged(NodeId, void) = .empty;
        var queue: std.ArrayList(Ref) = .empty;
        if (c.nd.op != .loop) {
            for (0..slots) |k| if (c.out_read[k]) {
                needed[k] = true;
            };
        }
        for (c.spine.items) |r| {
            const end = c.store.region(r).end;
            switch (end.kind) {
                .break_ => for (c.endRefs(r), 0..) |ref, o| if (c.out_read[o]) try queue.append(c.a, ref),
                .return_, .jump => try queue.appendSlice(c.a, c.endRefs(r)),
                // The decision is read; the arms are walked on their own.
                .branch => try queue.appendSlice(c.a, c.store.refSlice(c.store.node(NodeId.of(end.target)).args)),
                .continue_, .open, .value => {},
            }
        }
        // Processed slots, so each one's next values are walked once.
        const walked = try c.a.alloc(bool, slots);
        @memset(walked, false);
        while (true) {
            while (queue.pop()) |ref| try c.demand(ref, needed, &seen, &queue);
            var more = false;
            for (0..slots) |k| {
                if (!needed[k] or walked[k]) continue;
                walked[k] = true;
                more = true;
                for (c.conts.items) |r| try queue.append(c.a, c.endRefs(r)[k]);
            }
            if (!more) break;
        }
        return needed;
    }

    // One value flows into what the loop gives out: its slot, or the values
    // its node reads and the regions that node owns end in.
    fn demand(c: *Ctx, ref: Ref, needed: []bool, seen: *std.AutoHashMapUnmanaged(NodeId, void), queue: *std.ArrayList(Ref)) Allocator.Error!void {
        switch (ref.kind) {
            .region_param => if (c.slotOf(ref)) |k| {
                needed[k] = true;
            },
            .row_param, .input => {},
            .node => {
                const n = ref.nodeId();
                if ((try seen.getOrPut(c.a, n)).found_existing) return;
                // A node outside the loop reads nothing of it.
                if (!c.store.encloses(c.body, c.store.node(n).region)) return;
                const nd = c.store.node(n);
                try queue.appendSlice(c.a, c.store.refSlice(nd.args));
                for (c.store.regionSlice(nd.regions)) |sub| {
                    const end = c.store.region(sub).end;
                    try queue.appendSlice(c.a, c.store.refSlice(end.refs));
                    if (end.kind == .branch) try queue.append(c.a, Ref.of(NodeId.of(end.target)));
                }
            },
        }
    }

    // N11i: split the classes of slots until the slots of a class have equal
    // next values, and equal `Break` values for bounded loops, under the
    // assumption that the slots of the class are equal. A class is named by
    // its lowest slot.
    fn refine(c: *Ctx, fates: anytype, class: []u32) Allocator.Error!void {
        while (true) {
            var split = false;
            for (0..class.len) |j| {
                if (fates[j] != .keep or class[j] != j) continue;
                // The members that differ from `j` leave for a class of their
                // own, named by the lowest of them; the next pass tests them.
                var left: ?u32 = null;
                for (j + 1..class.len) |k| {
                    if (fates[k] != .keep or class[k] != j) continue;
                    if (try c.congruentSlots(@intCast(j), @intCast(k), class)) continue;
                    if (left == null) left = @intCast(k);
                    class[k] = left.?;
                    split = true;
                }
            }
            if (!split) break;
        }
    }

    fn congruentSlots(c: *Ctx, j: u32, k: u32, class: []const u32) Allocator.Error!bool {
        var memo: std.AutoHashMapUnmanaged([2]u64, bool) = .empty;
        for (c.conts.items) |r| {
            const refs = c.endRefs(r);
            if (!try c.congruent(refs[j], refs[k], class, &memo)) return false;
        }
        if (c.nd.op != .loop) {
            for (c.breaks.items) |r| {
                const refs = c.endRefs(r);
                if (!try c.congruent(refs[j], refs[k], class, &memo)) return false;
            }
        }
        return true;
    }

    // Whether `x` and `y` are one value when the slots of a class are equal.
    fn congruent(c: *Ctx, x: Ref, y: Ref, class: []const u32, memo: *std.AutoHashMapUnmanaged([2]u64, bool)) Allocator.Error!bool {
        if (x == y) return true;
        if (c.slotOf(x)) |kx| {
            const ky = c.slotOf(y) orelse return false;
            return class[kx] == class[ky];
        }
        if (x.kind != .node or y.kind != .node or x.output != y.output) return false;
        const key: [2]u64 = .{ @bitCast(x), @bitCast(y) };
        if (memo.get(key)) |known| return known;
        const store = c.store;
        const a = store.node(x.nodeId());
        const b = store.node(y.nodeId());
        const equal = blk: {
            // Two nodes that stand outside the loop are one value only when they are one node.
            if (!store.encloses(c.body, a.region) or !store.encloses(c.body, b.region)) break :blk false;
            if (a.op != b.op or a.payload != b.payload or a.regions.len != 0 or b.regions.len != 0) break :blk false;
            if (!std.mem.eql(TyId, store.tySlice(a.tys), store.tySlice(b.tys))) break :blk false;
            if (!std.mem.eql(u32, store.wordSlice(a.aux), store.wordSlice(b.aux))) break :blk false;
            const xa = store.refSlice(a.args);
            const ya = store.refSlice(b.args);
            if (xa.len != ya.len) break :blk false;
            for (xa, ya) |p, q| if (!try c.congruent(p, q, class, memo)) break :blk false;
            break :blk true;
        };
        try memo.put(c.a, key, equal);
        return equal;
    }

    // Whether `ref` is a value the loop does not change: a value outside the
    // body, or a node in the body's own region that reads only such values.
    // Gives the body's nodes it reads, dependencies first.
    fn outside(c: *Ctx, ref: Ref, cone: *std.ArrayList(NodeId)) Allocator.Error!bool {
        switch (ref.kind) {
            .row_param, .input => return true,
            .region_param => return !c.store.encloses(c.body, ref.regionId()),
            .node => {
                const n = ref.nodeId();
                const nd = c.store.node(n);
                if (!c.store.encloses(c.body, nd.region)) return true;
                // Only the body's own nodes move out, as a cone of plain nodes.
                if (nd.region != c.body or nd.regions.len != 0) return false;
                if (std.mem.findScalar(NodeId, cone.items, n) != null) return true;
                for (c.store.refSlice(nd.args)) |arg| if (!try c.outside(arg, cone)) return false;
                try cone.append(c.a, n);
                return true;
            },
        }
    }

    // The nodes of `ref`'s cone are read by nothing else in the loop but the
    // loop's own header and what the new body keeps: a node in the cone is
    // built outside the loop for every reader, so it is one node.
    fn isIntLit(c: *const Ctx, ref: Ref, value: u128) bool {
        if (ref.kind != .node) return false;
        const nd = c.store.node(ref.nodeId());
        if (nd.op != .lit) return false;
        const lit = c.store.lit(ir.LitId.of(nd.payload));
        return lit.value == .int and lit.value.int == value and c.types.isInt(lit.ty);
    }

    fn primOf(c: *const Ctx, ref: Ref) ?struct { prim: prims.Prim, nd: ir.Node } {
        if (ref.kind != .node) return null;
        const nd = c.store.node(ref.nodeId());
        if (nd.op != .prim) return null;
        const prim = prims.lookup(ir.PrimId.of(nd.payload)) orelse return null;
        return .{ .prim = prim, .nd = nd };
    }

    // N11l, the first raising rule: a `Loop` that tests a counter against a
    // bound and steps it by one is a `ForRange` with the counter as its index.
    fn raiseCounter(c: *Ctx) Allocator.Error!?Rewrite {
        const store = c.store;
        const body_end = store.region(c.body).end;
        if (body_end.kind != .branch) return null;
        const w = NodeId.of(body_end.target);
        const sw = store.node(w);
        if (sw.op != .switch_ or sw.payload != 2 or sw.tys.len != 0 or sw.aux.len != 0) return null;
        const arms = store.regionSlice(sw.regions);
        if (arms.len != 2) return null;
        const cond_ref = store.refSlice(sw.args)[0];
        const cond = c.primOf(cond_ref) orelse return null;
        // The test is `is_lt(s, b)` with the arm for `False` leaving, or its
        // dual `is_lte(b, s)` with the arm for `True` leaving, which is what
        // `if s >= b { break }` gives (N13q does not reach an exiting switch).
        const dual = switch (cond.prim.method) {
            .is_lt => false,
            .is_lte => true,
            else => return null,
        };
        const int = cond.prim.owner.int() orelse return null;
        // The test is read by this switch alone.
        const sites = (c.p.uses.get(cond_ref.nodeId()) orelse return null).items;
        if (sites.len != 1 or sites[0] != .node or sites[0].node != w) return null;
        const test_args = store.refSlice(cond.nd.args);
        const counter_ref = test_args[if (dual) 1 else 0];
        const bound_ref = test_args[if (dual) 0 else 1];
        const counter = c.slotOf(counter_ref) orelse return null;
        var cone: std.ArrayList(NodeId) = .empty;
        if (!try c.outside(bound_ref, &cone)) return null;
        // The counter is a builtin integer.
        const counter_ty = c.slotTy(counter);
        if (!c.types.isInt(counter_ty)) return null;
        // The `False` arm leaves with the other slots, and computes nothing.
        const done = arms[if (dual) 1 else 0];
        const goes_on = arms[if (dual) 0 else 1];
        const done_end = store.region(done).end;
        if (done_end.kind != .break_ or c.p.membersOf(done).len != 0) return null;
        const others = try c.a.alloc(u32, c.slot_count - 1);
        var at: usize = 0;
        for (0..c.slot_count) |k| if (k != counter) {
            others[at] = @intCast(k);
            at += 1;
        };
        const done_refs = c.endRefs(done);
        if (done_refs.len != others.len or c.nd.tys.len != others.len) return null;
        for (done_refs, others, store.tySlice(c.nd.tys)) |ref, k, ty| {
            if (ref != c.param(@intCast(k)) or ty != c.slotTy(k)) return null;
        }
        // Every `Continue` steps the counter by one.
        if (c.conts.items.len == 0) return null;
        for (c.conts.items) |r| {
            const step = c.primOf(c.endRefs(r)[counter]) orelse return null;
            if (step.prim.method != .plus or step.prim.owner.int() != int) return null;
            const operands = store.refSlice(step.nd.args);
            if (operands.len != 2) return null;
            const stepped = (operands[0] == counter_ref and c.isIntLit(operands[1], 1)) or (operands[1] == counter_ref and c.isIntLit(operands[0], 1));
            if (!stepped) return null;
        }
        // Build the rewrite: the index first, then the other slots.
        const params = try c.a.alloc(ParamTo, c.slot_count);
        const param_tys = try c.a.alloc(TyId, 1 + others.len);
        param_tys[0] = counter_ty;
        for (params, 0..) |*to, k| to.* = if (k == counter) .{ .param = 0 } else .gone;
        for (others, 0..) |k, i| {
            params[k] = .{ .param = @intCast(1 + i) };
            param_tys[1 + i] = c.slotTy(k);
        }
        const outputs = try c.a.alloc(OutputTo, others.len);
        for (outputs, 0..) |*to, i| to.* = .{ .output = @intCast(i) };
        const header = try c.a.alloc(Ref, 2);
        header[0] = c.args[c.lead + counter];
        header[1] = bound_ref;
        const break_keep = try c.a.alloc(u32, others.len);
        for (break_keep, 0..) |*k, i| k.* = @intCast(i);
        const skip = try c.a.alloc(NodeId, 2);
        skip[0] = w;
        skip[1] = cond_ref.nodeId();
        return .{
            .body = c.body,
            .op = .for_range,
            .payload = 0,
            .header = header,
            .slots = others,
            .param_tys = param_tys,
            .out_tys = try c.a.dupe(TyId, c.store.tySlice(c.nd.tys)),
            .params = params,
            .outputs = outputs,
            .break_keep = break_keep,
            .hoist = cone.items,
            .continue_in = goes_on,
            .skip = skip,
            .stands = &.{},
            .returns_break = false,
        };
    }

    // N11l, the second raising rule: `ForRange(0, List.len(xs))` is
    // `ForList(xs)`. A read of the element at the index is the element, which
    // the builder does while it copies the body (`Builder.elem`).
    fn rangeToList(c: *Ctx) Allocator.Error!?Rewrite {
        if (c.nd.payload != 0) return null;
        if (!c.isIntLit(c.args[0], 0)) return null;
        const len = c.primOf(c.args[1]) orelse return null;
        if (len.prim.owner != .list or len.prim.method != .len) return null;
        const xs = c.store.refSlice(len.nd.args)[0];
        const list_ty = c.store.refTy(c.row, xs);
        const elem_ty = switch (c.types.get(list_ty)) {
            .list => |elem| elem,
            .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .nominal, .func, .opaque_, .recursive => return null,
        };
        const old_params = c.store.tySlice(c.store.region(c.body).params);
        // The index of a list is a `U64`, which is the type of the length.
        const index_ty = old_params[0];
        if (!c.types.isInt(index_ty) or c.store.refTy(c.row, c.args[1]) != index_ty) return null;
        const params = try c.a.alloc(ParamTo, old_params.len);
        params[0] = .{ .param = 0 };
        for (params[1..], 0..) |*to, k| to.* = .{ .param = @intCast(2 + k) };
        const param_tys = try c.a.alloc(TyId, old_params.len + 1);
        param_tys[0] = index_ty;
        param_tys[1] = elem_ty;
        @memcpy(param_tys[2..], old_params[1..]);
        const slots = try c.a.alloc(u32, c.slot_count);
        for (slots, 0..) |*k, i| k.* = @intCast(i);
        const outputs = try c.a.alloc(OutputTo, c.slot_count);
        for (outputs, 0..) |*to, i| to.* = .{ .output = @intCast(i) };
        const header = try c.a.alloc(Ref, 1);
        header[0] = xs;
        return .{
            .body = c.body,
            .op = .for_list,
            .payload = 0,
            .header = header,
            .slots = slots,
            .param_tys = param_tys,
            .out_tys = try c.a.dupe(TyId, c.store.tySlice(c.nd.tys)),
            .params = params,
            .outputs = outputs,
            .break_keep = slots,
            .hoist = &.{},
            .continue_in = null,
            .skip = &.{},
            .stands = &.{},
            .returns_break = false,
        };
    }

    // N11k: a loop whose iterator slot starts as `List.iter(xs)` and is only
    // stepped by `Iter.next`, and whose `Continue`s pass the `rest` of the
    // step, is `ForList(xs)`. The checker-authored role of the primitives
    // says which procedures these are. The iterator yields every element in
    // index order, one per step, and never skips, so the `Skip` arm is dead
    // and `Done` is the end of the list.
    fn iteratorToList(c: *Ctx) Allocator.Error!?Rewrite {
        const store = c.store;
        const body_end = store.region(c.body).end;
        if (body_end.kind != .branch) return null;
        const w = NodeId.of(body_end.target);
        const sw = store.node(w);
        if (sw.op != .switch_ or sw.tys.len != 0 or sw.aux.len != 0) return null;
        const arms = store.regionSlice(sw.regions);
        if (arms.len != 3 or sw.payload != 3) return null;
        const step_ref = store.refSlice(sw.args)[0];
        const step = c.primOf2(step_ref) orelse return null;
        if (step.role != .next) return null;
        const iterator_ref = store.refSlice(step.nd.args)[0];
        const it = c.slotOf(iterator_ref) orelse return null;
        // The step is read by this switch and by the reads of its `One` payload.
        const step_ty = c.store.refTy(c.row, step_ref);
        const members = switch (c.types.get(step_ty)) {
            .tag_union => |span| c.types.memberSlice(span),
            .bool_, .str, .int, .float, .dec, .record, .tuple, .list, .nominal, .func, .opaque_, .recursive => return null,
        };
        if (members.len != 3) return null;
        const done_arm = c.armNamed(members, "Done", arms) orelse return null;
        const one_arm = c.armNamed(members, "One", arms) orelse return null;
        const skip_arm = c.armNamed(members, "Skip", arms) orelse return null;
        // The iterator starts as the iterator of a list.
        var init = c.args[c.lead + it];
        while (c.primOf2(init)) |known| {
            if (known.role != .identity) break;
            init = store.refSlice(known.nd.args)[0];
        }
        const source = c.primOf2(init) orelse return null;
        if (source.role != .list_iter) return null;
        const xs = store.refSlice(source.nd.args)[0];
        const list_ty = c.store.refTy(c.row, xs);
        const elem_ty = switch (c.types.get(list_ty)) {
            .list => |elem| elem,
            .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .nominal, .func, .opaque_, .recursive => return null,
        };
        // The iterator is read by the step alone, and the step by the switch
        // and the reads of its payloads: the `One` payload is the body's, and
        // the `Skip` payload stands in the arm that never runs.
        if (try c.readsOf(iterator_ref) != 1) return null;
        const step_sites = (c.p.uses.get(step_ref.nodeId()) orelse return null).items;
        var payload_node: ?NodeId = null;
        const one_name = c.types.findName("One") orelse return null;
        const skip_name = c.types.findName("Skip") orelse return null;
        for (step_sites) |site| switch (site) {
            .node => |m| {
                if (m == w) continue;
                const read = store.node(m);
                if (read.op != .payload) return null;
                if (read.payload == one_name.index()) {
                    if (payload_node != null) return null;
                    payload_node = m;
                } else if (read.payload == skip_name.index()) {
                    if (!store.encloses(arms[skip_arm], read.region)) return null;
                } else return null;
            },
            .region => return null,
        };
        const payload_id = payload_node orelse return null;
        const payload_ref = Ref.of(payload_id);
        const payload_ty = c.store.refTy(c.row, payload_ref);
        const fields = switch (c.types.get(payload_ty)) {
            .record => |span| c.types.memberSlice(span),
            .bool_, .str, .int, .float, .dec, .tuple, .tag_union, .list, .nominal, .func, .opaque_, .recursive => return null,
        };
        if (fields.len != 2) return null;
        var item_at: ?u32 = null;
        var rest_at: ?u32 = null;
        for (fields, 0..) |f, i| {
            const text = c.types.nameText(f.name);
            if (std.mem.eql(u8, text, "item")) item_at = @intCast(i);
            if (std.mem.eql(u8, text, "rest")) rest_at = @intCast(i);
        }
        const item_index = item_at orelse return null;
        const rest_index = rest_at orelse return null;
        // The payload is read by its two fields alone.
        var item_node: ?NodeId = null;
        var rest_node: ?NodeId = null;
        const payload_sites = (c.p.uses.get(payload_id) orelse return null).items;
        for (payload_sites) |site| switch (site) {
            .node => |m| {
                const read = store.node(m);
                if (read.op != .field) return null;
                if (read.payload == item_index and item_node == null) item_node = m else if (read.payload == rest_index and rest_node == null) rest_node = m else return null;
            },
            .region => return null,
        };
        const rest_id = rest_node orelse return null;
        // `Done` ends the loop with the other slots; `One` is the body.
        const done = arms[done_arm];
        const done_end = store.region(done).end;
        if (done_end.kind != .break_ or c.p.membersOf(done).len != 0) return null;
        const others = try c.a.alloc(u32, c.slot_count - 1);
        var at: usize = 0;
        for (0..c.slot_count) |k| if (k != it) {
            others[at] = @intCast(k);
            at += 1;
        };
        const done_refs = c.endRefs(done);
        if (done_refs.len != others.len or c.nd.tys.len != others.len) return null;
        for (done_refs, others, store.tySlice(c.nd.tys)) |ref, k, ty| {
            if (ref != c.param(c.header + @as(u32, @intCast(k))) or ty != c.slotTy(k)) return null;
        }
        // Every `Continue` of the body passes the `rest` as the iterator.
        const one = arms[one_arm];
        var one_conts: std.ArrayList(RegionId) = .empty;
        var regions: std.ArrayList(RegionId) = .empty;
        try regions.append(c.a, one);
        var i: usize = 0;
        while (i < regions.items.len) : (i += 1) {
            const end = store.region(regions.items[i]).end;
            switch (end.kind) {
                .branch => try regions.appendSlice(c.a, store.regionSlice(store.node(NodeId.of(end.target)).regions)),
                .continue_ => try one_conts.append(c.a, regions.items[i]),
                .open, .value, .jump, .break_, .return_ => {},
            }
        }
        for (one_conts.items) |r| if (c.endRefs(r)[it] != Ref.of(rest_id)) return null;
        // The `rest` is read by those `Continue`s alone.
        const rest_sites = (c.p.uses.get(rest_id) orelse return null).items;
        for (rest_sites) |site| switch (site) {
            .region => |r| if (std.mem.findScalar(RegionId, one_conts.items, r) == null) return null,
            .node => return null,
        };
        // The item's type is the list's.
        if (item_node) |item| if (c.store.refTy(c.row, Ref.of(item)) != elem_ty) return null;
        // Build the rewrite: the index, the element, then the other slots.
        const old_params = c.store.tySlice(c.store.region(c.body).params);
        const params = try c.a.alloc(ParamTo, old_params.len);
        for (params) |*to| to.* = .gone;
        const param_tys = try c.a.alloc(TyId, 2 + others.len);
        param_tys[0] = try c.indexTy();
        param_tys[1] = elem_ty;
        for (others, 0..) |k, j| {
            params[c.header + k] = .{ .param = @intCast(2 + j) };
            param_tys[2 + j] = c.slotTy(k);
        }
        const outputs = try c.a.alloc(OutputTo, others.len);
        for (outputs, 0..) |*to, j| to.* = .{ .output = @intCast(j) };
        const header = try c.a.alloc(Ref, 1);
        header[0] = xs;
        const break_keep = try c.a.alloc(u32, others.len);
        for (break_keep, 0..) |*k, j| k.* = @intCast(j);
        const skip = try c.a.alloc(NodeId, 4);
        skip[0] = w;
        skip[1] = step_ref.nodeId();
        skip[2] = payload_id;
        skip[3] = rest_id;
        // The element stands for the item the body reads, when it reads one.
        const stands = try c.a.alloc(Stands, if (item_node == null) 0 else 1);
        if (item_node) |item| stands[0] = .{ .node = item, .param = 1 };
        return .{
            .body = c.body,
            .op = .for_list,
            .payload = 0,
            .header = header,
            .slots = others,
            .param_tys = param_tys,
            .out_tys = try c.a.dupe(TyId, c.store.tySlice(c.nd.tys)),
            .params = params,
            .outputs = outputs,
            .break_keep = break_keep,
            .hoist = &.{},
            .continue_in = one,
            .skip = skip,
            .stands = stands,
            .returns_break = false,
        };
    }

    // `U64`, the type of a list's index.
    fn indexTy(c: *Ctx) Allocator.Error!TyId {
        return c.types.intTy(.u64);
    }

    const RolePrim = struct { role: ir.IteratorRole, nd: ir.Node };

    // The primitive `ref` is, with the role the walk gave it, when it is one
    // the store names.
    fn primOf2(c: *const Ctx, ref: Ref) ?RolePrim {
        if (ref.kind != .node) return null;
        const nd = c.store.node(ref.nodeId());
        if (nd.op != .prim) return null;
        const name = c.store.primName(ir.PrimId.of(nd.payload));
        return .{ .role = name.role, .nd = nd };
    }

    // The index of the arm of the tag `name`.
    fn armNamed(c: *const Ctx, members: []const types_mod.Member, name: []const u8, arms: []const RegionId) ?usize {
        for (members, 0..) |m, i| if (std.mem.eql(u8, c.types.nameText(m.name), name)) {
            return if (i < arms.len) i else null;
        };
        return null;
    }

    // How many times the nodes the plan reaches, and the ends of its
    // regions, read `ref`.
    fn readsOf(c: *const Ctx, ref: Ref) Allocator.Error!u32 {
        var count: u32 = 0;
        var nodes = c.p.info.constKeyIterator();
        while (nodes.next()) |n| {
            for (c.store.refSlice(c.store.node(n).args)) |arg| {
                if (arg == ref) count += 1;
            }
        }
        for (c.p.regions.items) |r| {
            for (c.endRefs(r)) |arg| {
                if (arg == ref) count += 1;
            }
        }
        return count;
    }
};

/// The tail calls of a row (N12): the self calls, and the places they stand.
pub const Tail = struct {
    /// The calls of the row to itself, each the value a path of the row ends in.
    calls: std.AutoHashMapUnmanaged(NodeId, void) = .empty,
    /// The value switches the row's value is, each of whose arms ends in a
    /// path of the row: they become exiting switches.
    switches: std.AutoHashMapUnmanaged(NodeId, void) = .empty,
    /// The regions whose ends are paths of the row.
    spine: std.AutoHashMapUnmanaged(RegionId, void) = .empty,
};

/// N12: the tail calls of `row` when every call it makes to itself is one,
/// and there is one; null otherwise. A tail call is a call to the row that
/// nothing but a path's end reads, where the path is the row body, an arm or
/// join of an exiting switch in it, or an arm of a value switch whose
/// output is the row's value and nothing else reads. A call in a loop, in a
/// lambda, or read twice is not a tail call; and a closure of the row is
/// another way to reach it, so the row stays recursive. `live` says what the
/// rows reach. The caller's arena owns what it gives.
pub fn tailSites(a: Allocator, store: *const ir.Store, live: live_mod.Live, row: RowId) Allocator.Error!?Tail {
    const uses = try a.alloc(u32, store.nodeCount());
    @memset(uses, 0);
    var self_calls: u32 = 0;
    const nodes = store.nodes.slice();
    const ops = nodes.items(.op);
    const payloads = nodes.items(.payload);
    const regions = nodes.items(.region);
    const args = nodes.items(.args);
    for (0..@min(live.nodes.len, ops.len)) |k| {
        if (!live.nodes[k] or store.region(regions[k]).row != row) continue;
        for (store.refSlice(args[k])) |ref| if (ref.kind == .node) {
            uses[ref.target] += 1;
        };
        switch (ops[k]) {
            .call => if (payloads[k] == row.index()) {
                self_calls += 1;
            },
            .closure => if (payloads[k] == row.index()) return null,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .switch_, .for_range, .for_list, .loop, .lambda, .apply => {},
        }
    }
    if (self_calls == 0) return null;
    for (0..@min(live.regions.len, store.regionCount())) |k| {
        if (!live.regions[k]) continue;
        const r = RegionId.of(@intCast(k));
        if (store.region(r).row != row) continue;
        const end = store.region(r).end;
        for (store.refSlice(end.refs)) |ref| if (ref.kind == .node) {
            uses[ref.target] += 1;
        };
        if (end.kind == .branch) uses[end.target] += 1;
    }
    var tail: Tail = .{};
    var walk: TailWalk = .{ .a = a, .store = store, .row = row, .uses = uses, .tail = &tail };
    try walk.region(store.row(row).body);
    // Every call the row makes to itself is one of these.
    if (tail.calls.count() != self_calls) return null;
    return tail;
}

/// How many tail calls `row` has, when N12 applies to it: the measure's first
/// component counts them, and the rule removes them all.
pub fn selfTailCalls(gpa: Allocator, store: *const ir.Store, live: live_mod.Live, row: RowId) Allocator.Error!u32 {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const tail = try tailSites(arena.allocator(), store, live, row) orelse return 0;
    return @intCast(tail.calls.count());
}

const TailWalk = struct {
    a: Allocator,
    store: *const ir.Store,
    row: RowId,
    uses: []const u32,
    tail: *Tail,

    // A region of the row's paths: its end is a path's end, or goes on in the
    // arms and joins of the exiting switch it ends in.
    fn region(w: *TailWalk, r: RegionId) Allocator.Error!void {
        try w.tail.spine.put(w.a, r, {});
        const end = w.store.region(r).end;
        switch (end.kind) {
            .value, .return_ => try w.value(w.store.refSlice(end.refs)[0]),
            .branch => for (w.store.regionSlice(w.store.node(NodeId.of(end.target)).regions)) |sub| try w.region(sub),
            .jump, .open, .continue_, .break_ => {},
        }
    }

    // The value a path ends in: a call to the row, or a value switch whose
    // arms end the same way. Another value is the row's value as it is.
    fn value(w: *TailWalk, ref: Ref) Allocator.Error!void {
        if (ref.kind != .node or w.uses[ref.target] != 1) return;
        const n = ref.nodeId();
        const nd = w.store.node(n);
        switch (nd.op) {
            .call => if (nd.payload == w.row.index()) try w.tail.calls.put(w.a, n, {}),
            .switch_ => {
                const arms = w.store.regionSlice(nd.regions);
                if (nd.tys.len != 1 or arms.len != nd.payload) return;
                try w.tail.switches.put(w.a, n, {});
                for (arms) |arm| try w.region(arm);
            },
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .and_, .or_, .for_range, .for_list, .loop, .lambda, .apply => {},
        }
    }
};

/// L2: whether no loop of a row the plan reaches is one a rule of this
/// file rewrites. A fixpoint of the simplify rounds leaves none.
pub fn noneRewritable(gpa: Allocator, store: *const ir.Store, types: *Types, p: *const place.Plan) Allocator.Error!bool {
    var scratch = std.heap.ArenaAllocator.init(gpa);
    defer scratch.deinit();
    const usage = try scalar.Usage.ofPlan(scratch.allocator(), p);
    var nodes = p.info.constKeyIterator();
    while (nodes.next()) |n| {
        const op = store.node(n).op;
        if (op != .for_range and op != .for_list and op != .loop) continue;
        if (try analyze(scratch.allocator(), p, types, n, .{ .row_body = null, .usage = &usage })) |_| return false;
    }
    return true;
}

/// The steps this file owns, for the normal-form fingerprint (`mod.zig`):
/// adding, removing or renaming a rule changes it, and so the version.
pub const steps = [_][]const u8{ "N12", "N11g", "N11h", "N11i", "N11j", "N11k", "N11l" };

const testing = std.testing;
const builder_mod = @import("builder.zig");
const driver = @import("driver.zig");
const dump = @import("dump.zig");
const verify = @import("verify.zig");
const eval = @import("eval.zig");
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

    // Run the driver over the site of `root` and dump it.
    fn site(self: *Fixture, root: RowId) ![]u8 {
        _ = try driver.runTo(testing.allocator, &self.b, root, &.{}, .finalized);
        var report = try verify.verifyAll(testing.allocator, &self.store, &self.types);
        defer report.deinit();
        try testing.expect(report.ok());
        var out: std.Io.Writer.Allocating = .init(testing.allocator);
        errdefer out.deinit();
        try dump.dumpSite(&out.writer, testing.allocator, &self.store, &self.types, root);
        return out.toOwnedSlice();
    }

    fn run(self: *Fixture, arena: Allocator, root: RowId, args: []const eval.Value) !eval.Value {
        var e = try eval.Evaluator.init(arena, &self.store, &self.types, .strict);
        return e.run(root, args);
    }
};

/// How a counter loop is written: what each field changes is a condition of N11l.
const Counter = struct {
    /// How far each turn steps the counter.
    step: i128 = 1,
    test_: enum { lt, lte, ge_exits } = .lt,
    /// The bound is the other slot, not a value from outside the loop.
    bound_in_slot: bool = false,
    /// The `Break` carries the other slot plus one, not the slot itself.
    break_other: bool = false,
};

// `|n| loop(total = 0, i = 0) { if i < n { continue(total + i, i + step) } else { break(total) } }`.
fn counterRow(f: *Fixture, c: Counter) !RowId {
    const i64_ty = try f.types.intTy(.i64);
    const row = try f.b.beginRow(&.{i64_ty}, i64_ty);
    const zero = try f.b.litInt(i64_ty, 0);
    const lb = try f.b.openRegion(.loop_body, &.{ i64_ty, i64_ty });
    const total = Ref.regionParam(lb, 0);
    const i = Ref.regionParam(lb, 1);
    const bound = if (c.bound_in_slot) total else Ref.rowParam(0);
    const test_ = switch (c.test_) {
        .lt => try f.b.call(.i64, .is_lt, &.{ i, bound }),
        .lte => try f.b.call(.i64, .is_lte, &.{ i, bound }),
        .ge_exits => try f.b.call(.i64, .is_lte, &.{ bound, i }),
    };
    // The arm for `False` is key 0.
    const goes_on_key: u32 = if (c.test_ == .ge_exits) 0 else 1;
    var arms: [2]RegionId = undefined;
    for (&arms, 0..) |*a, key| {
        a.* = try f.b.openArm(test_, @intCast(key));
        if (key == goes_on_key) {
            const next_total = try f.b.call(.i64, .plus, &.{ total, i });
            const next_i = try f.b.call(.i64, .plus, &.{ i, try f.b.litInt(i64_ty, c.step) });
            try f.b.close(.{ .continue_ = &.{ next_total, next_i } });
        } else {
            const out = if (c.break_other) try f.b.call(.i64, .plus, &.{ total, try f.b.litInt(i64_ty, 1) }) else total;
            try f.b.close(.{ .break_ = &.{out} });
        }
    }
    const sw = try f.b.exitingSwitch(test_, &arms, &.{}, &.{});
    try f.b.close(.{ .branch = sw });
    const loop = try f.b.loopOf(.loop, &.{ zero, zero }, lb, &.{i64_ty});
    try f.b.endRow(.{ .value = &.{loop} });
    return row;
}

fn expectLoopKind(f: *Fixture, root: RowId, want: []const u8, unwanted: []const u8) !void {
    const got = try f.site(root);
    defer testing.allocator.free(got);
    if (std.mem.find(u8, got, want) == null or std.mem.find(u8, got, unwanted) != null) {
        std.debug.print("expected {s} and not {s} in:\n{s}\n", .{ want, unwanted, got });
        return error.TestUnexpectedResult;
    }
}

// The sum, over the counter, that the loop of `c` computes, before and after the rules.
fn expectSameValues(c: Counter, want_range: bool) !void {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const row = try counterRow(&f, c);
    var before: [4]eval.Value = undefined;
    for (&before, [_]i128{ 0, 1, 5, 9 }) |*o, n| o.* = try f.run(arena.allocator(), row, &.{.{ .int = n }});
    if (want_range) try expectLoopKind(&f, row, "for_range(", "loop(") else try expectLoopKind(&f, row, "loop(", "for_range");
    for (before, [_]i128{ 0, 1, 5, 9 }) |was, n| try testing.expect(was.eql(try f.run(arena.allocator(), row, &.{.{ .int = n }})));
}

test "N11l: a loop that tests a counter against a bound and steps it by one is a ForRange" {
    try expectSameValues(.{}, true);
}

test "N11l: the test spelled as the exit, `if i >= n { break }`, is the same ForRange" {
    try expectSameValues(.{ .test_ = .ge_exits }, true);
}

test "N11l: a step of 2 stays a general Loop" {
    try expectSameValues(.{ .step = 2 }, false);
}

test "N11l: a bound read from a slot stays a general Loop" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const row = try counterRow(&f, .{ .bound_in_slot = true });
    try expectLoopKind(&f, row, "loop(", "for_range");
}

test "N11l: a Break that is not the other slots stays a general Loop" {
    try expectSameValues(.{ .break_other = true }, false);
}

test "N11l: a test with `<=` stays a general Loop" {
    try expectSameValues(.{ .test_ = .lte }, false);
}

// `|xs| for_range(0, List.len(xs), acc = 0) { acc + xs[i] }`.
fn indexedSum(f: *Fixture, start: i128) !RowId {
    const u64_ty = try f.types.intTy(.u64);
    const list_ty = try f.types.listTy(u64_ty);
    const row = try f.b.beginRow(&.{list_ty}, u64_ty);
    const from = try f.b.litInt(u64_ty, start);
    const acc0 = try f.b.litInt(u64_ty, 0);
    const lb = try f.b.openRegion(.loop_body, &.{ u64_ty, u64_ty });
    const item = try f.b.elem(Ref.rowParam(0), Ref.regionParam(lb, 0), u64_ty);
    try f.b.close(.{ .continue_ = &.{try f.b.call(.u64, .plus, &.{ Ref.regionParam(lb, 1), item })} });
    const len = try f.b.call(.list, .len, &.{Ref.rowParam(0)});
    const loop = try f.b.loopOf(.for_range, &.{ from, len, acc0 }, lb, &.{u64_ty});
    try f.b.endRow(.{ .value = &.{loop} });
    return row;
}

test "N11l: ForRange(0, List.len(xs)) is ForList(xs), and the item at the index is the element" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const row = try indexedSum(&f, 0);
    const got = try f.site(row);
    defer testing.allocator.free(got);
    try testing.expect(std.mem.find(u8, got, "for_list(p0") != null);
    try testing.expect(std.mem.find(u8, got, "for_range") == null);
    try testing.expect(std.mem.find(u8, got, "item(") == null);
}

test "N11l: a range that does not start at 0 stays a ForRange" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const row = try indexedSum(&f, 1);
    const got = try f.site(row);
    defer testing.allocator.free(got);
    try testing.expect(std.mem.find(u8, got, "for_range(") != null);
    try testing.expect(std.mem.find(u8, got, "for_list") == null);
}

// `|n| for_range(0, n, a = 0, b = 0, dead = 0) { continue(a + 1, <b>, dead + 1) }` read through `a + b` only.
fn slotRow(f: *Fixture, how: enum { invariant, dead, equal }) !RowId {
    const i64_ty = try f.types.intTy(.i64);
    const row = try f.b.beginRow(&.{i64_ty}, i64_ty);
    const zero = try f.b.litInt(i64_ty, 0);
    const one = try f.b.litInt(i64_ty, 1);
    const lb = try f.b.openRegion(.loop_body, &.{ i64_ty, i64_ty, i64_ty, i64_ty });
    const i = Ref.regionParam(lb, 0);
    const a = Ref.regionParam(lb, 1);
    const b = Ref.regionParam(lb, 2);
    const d = Ref.regionParam(lb, 3);
    const next_a = try f.b.call(.i64, .plus, &.{ a, i });
    const next_b = switch (how) {
        .invariant => b,
        .dead => try f.b.call(.i64, .plus, &.{ b, d }),
        .equal => next_a,
    };
    const next_d = try f.b.call(.i64, .plus, &.{ d, one });
    try f.b.close(.{ .continue_ = &.{ next_a, next_b, next_d } });
    const loop = try f.b.loopOf(.for_range, &.{ zero, Ref.rowParam(0), zero, if (how == .equal) zero else Ref.rowParam(0), zero }, lb, &.{ i64_ty, i64_ty, i64_ty });
    // The `dead` case reads the first slot alone, so the second and the third are dead.
    const first = Ref.node(loop.nodeId(), 0);
    const read = if (how == .dead) first else try f.b.call(.i64, .plus, &.{ first, Ref.node(loop.nodeId(), 1) });
    try f.b.endRow(.{ .value = &.{read} });
    return row;
}

fn slotsOf(f: *Fixture, root: RowId) !usize {
    const got = try f.site(root);
    defer testing.allocator.free(got);
    const at = std.mem.find(u8, got, "body (") orelse return error.TestUnexpectedResult;
    const close = std.mem.findPos(u8, got, at, ")") orelse return error.TestUnexpectedResult;
    return std.mem.count(u8, got[at..close], ":");
}

test "N11g: a slot every Continue passes unchanged is its initial value" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const row = try slotRow(&f, .invariant);
    // The index and the sum are left: the unchanged slot and the dead one are gone.
    try testing.expectEqual(@as(usize, 2), try slotsOf(&f, row));
}

test "N11i: slots with equal starts and equal next values are one slot" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const row = try slotRow(&f, .equal);
    try testing.expectEqual(@as(usize, 2), try slotsOf(&f, row));
}

test "N11h: a slot nothing outside reads, and no other slot reads, is removed" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const row = try slotRow(&f, .dead);
    // `b` reads `d`, but nothing reads `b` except its own next value: both go.
    try testing.expectEqual(@as(usize, 2), try slotsOf(&f, row));
}

test "N12: a row whose every call to itself is a tail call is a Loop, and a call that is not stays a call" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    for ([_]bool{ true, false }) |tail| {
        var f: Fixture = undefined;
        f.init();
        defer f.deinit();
        const i64_ty = try f.types.intTy(.i64);
        // `count(n) = if n < 1 then n else count(n - 1)`, or `1 + count(n - 1)`.
        const row = try f.b.beginRow(&.{i64_ty}, i64_ty);
        const one = try f.b.litInt(i64_ty, 1);
        const c = try f.b.call(.i64, .is_lt, &.{ Ref.rowParam(0), one });
        const done = try f.b.openArm(c, 1);
        try f.b.close(.{ .value = &.{Ref.rowParam(0)} });
        const more = try f.b.openArm(c, 0);
        const again = try f.b.callRow(row, &.{try f.b.call(.i64, .minus, &.{ Ref.rowParam(0), one })});
        try f.b.close(.{ .value = &.{if (tail) again else try f.b.call(.i64, .plus, &.{ one, again })} });
        const sw = try f.b.switchOn(c, &.{ more, done }, &.{}, &.{i64_ty}, &.{});
        try f.b.endRow(.{ .value = &.{sw} });
        const got = try f.site(row);
        defer testing.allocator.free(got);
        try testing.expectEqual(tail, std.mem.find(u8, got, "loop(p0") != null);
        try testing.expectEqual(!tail, std.mem.find(u8, got, "call r0(") != null);
    }
}

test "N11j: the outputs of a general Loop that nothing reads are not carried by its Break" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const row = try f.b.beginRow(&.{i64_ty}, i64_ty);
    const zero = try f.b.litInt(i64_ty, 0);
    const lb = try f.b.openRegion(.loop_body, &.{ i64_ty, i64_ty });
    const total = Ref.regionParam(lb, 0);
    const i = Ref.regionParam(lb, 1);
    const c = try f.b.call(.i64, .is_lt, &.{ total, Ref.rowParam(0) });
    var arms: [2]RegionId = undefined;
    arms[0] = try f.b.openArm(c, 0);
    try f.b.close(.{ .break_ = &.{ total, i } });
    arms[1] = try f.b.openArm(c, 1);
    try f.b.close(.{ .continue_ = &.{ try f.b.call(.i64, .plus, &.{ total, i }), try f.b.call(.i64, .plus, &.{ i, i }) } });
    const sw = try f.b.exitingSwitch(c, &arms, &.{}, &.{});
    try f.b.close(.{ .branch = sw });
    const loop = try f.b.loopOf(.loop, &.{ zero, zero }, lb, &.{ i64_ty, i64_ty });
    try f.b.endRow(.{ .value = &.{Ref.node(loop.nodeId(), 0)} });
    const got = try f.site(row);
    defer testing.allocator.free(got);
    try testing.expect(std.mem.find(u8, got, "break s") != null);
    try testing.expect(std.mem.find(u8, got, "break s2.0, s2.1") == null);
}

test "a ForList whose body divides stays not speculatable" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const i64_ty = try f.types.intTy(.i64);
    const u64_ty = try f.types.intTy(.u64);
    const list_ty = try f.types.listTy(i64_ty);
    const row = try f.b.beginRow(&.{ list_ty, i64_ty }, i64_ty);
    const zero = try f.b.litInt(i64_ty, 0);
    const lb = try f.b.openRegion(.loop_body, &.{ u64_ty, i64_ty, i64_ty });
    try f.b.noteListLoop(lb, Ref.rowParam(0));
    const quotient = try f.b.call(.i64, .div_trunc, &.{ Ref.regionParam(lb, 1), Ref.rowParam(1) });
    try f.b.close(.{ .continue_ = &.{try f.b.call(.i64, .plus, &.{ Ref.regionParam(lb, 2), quotient })} });
    const loop = try f.b.loopOf(.for_list, &.{ Ref.rowParam(0), zero }, lb, &.{i64_ty});
    try f.b.endRow(.{ .value = &.{loop} });
    const got = try f.site(row);
    defer testing.allocator.free(got);
    // `!spec` marks a node that is not speculatable.
    const at = std.mem.find(u8, got, "for_list(") orelse return error.TestUnexpectedResult;
    const line_end = std.mem.findPos(u8, got, at, "\n") orelse got.len;
    try testing.expect(std.mem.find(u8, got[at..line_end], "!spec") != null);
    try testing.expect(!f.store.row(row).speculatable);
}

// `|n| out = for_range(0, n, acc = { a: 0, b: 0 }) { <next> }; out.a + out.b`,
// where `<next>` is `{ a: acc.a + i, b: acc.b + 1 }` built fresh, or chosen by
// a switch, or handed to a row that returns it.
const NextAcc = enum { fresh, switched, through_row, unchanged_in_one_arm };

fn recordSlotRow(f: *Fixture, next: NextAcc) !RowId {
    const i64_ty = try f.types.intTy(.i64);
    const pair = try f.types.recordTy(&.{ .{ .name = "a", .ty = i64_ty }, .{ .name = "b", .ty = i64_ty } });
    const identity = try f.b.beginRow(&.{pair}, pair);
    try f.b.endRow(.{ .value = &.{Ref.rowParam(0)} });
    const row = try f.b.beginRow(&.{i64_ty}, i64_ty);
    const zero = try f.b.litInt(i64_ty, 0);
    const one = try f.b.litInt(i64_ty, 1);
    const start = try f.b.record(pair, &.{ zero, zero });
    const lb = try f.b.openRegion(.loop_body, &.{ i64_ty, pair });
    const i = Ref.regionParam(lb, 0);
    const acc = Ref.regionParam(lb, 1);
    const grown = try f.b.record(pair, &.{
        try f.b.call(.i64, .plus, &.{ try f.b.field(acc, 0), i }),
        try f.b.call(.i64, .plus, &.{ try f.b.field(acc, 1), one }),
    });
    const value = switch (next) {
        .fresh => grown,
        .through_row => try f.b.callRow(identity, &.{grown}),
        .switched, .unchanged_in_one_arm => blk: {
            const c = try f.b.call(.i64, .is_lt, &.{ i, one });
            const arm0 = try f.b.openArm(c, 0);
            try f.b.close(.{ .value = &.{grown} });
            const arm1 = try f.b.openArm(c, 1);
            try f.b.close(.{ .value = &.{if (next == .unchanged_in_one_arm) acc else try f.b.record(pair, &.{ zero, zero })} });
            break :blk try f.b.switchOn(c, &.{ arm0, arm1 }, &.{}, &.{pair}, &.{});
        },
    };
    try f.b.close(.{ .continue_ = &.{value} });
    const loop = try f.b.loopOf(.for_range, &.{ zero, Ref.rowParam(0), start }, lb, &.{pair});
    const out_a = try f.b.field(loop, 0);
    const out_b = try f.b.field(loop, 1);
    try f.b.endRow(.{ .value = &.{try f.b.call(.i64, .plus, &.{ out_a, out_b })} });
    return row;
}

// How many parameters the first loop body of the site has: a record type
// has colons of its own, so the entries are counted by their separators.
fn slotEntries(f: *Fixture, root: RowId) !usize {
    const got = try f.site(root);
    defer testing.allocator.free(got);
    const at = std.mem.find(u8, got, "body (") orelse return error.TestUnexpectedResult;
    const close = std.mem.findPos(u8, got, at, ")") orelse return error.TestUnexpectedResult;
    return 1 + std.mem.count(u8, got[at..close], ", s");
}

fn expectRecordSlot(next: NextAcc, split: bool) !void {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const row = try recordSlotRow(&f, next);
    var before: [4]eval.Value = undefined;
    for (&before, [_]i128{ 0, 1, 5, 9 }) |*o, n| o.* = try f.run(arena.allocator(), row, &.{.{ .int = n }});
    // The index and the slots: two components, or the record.
    try testing.expectEqual(@as(usize, if (split) 3 else 2), try slotEntries(&f, row));
    for (before, [_]i128{ 0, 1, 5, 9 }) |was, n| try testing.expect(was.eql(try f.run(arena.allocator(), row, &.{.{ .int = n }})));
}

test "N14b: a record slot the body only reads by field, and every Continue builds, is one slot per component" {
    try expectRecordSlot(.fresh, true);
}

test "N14b: a slot the Continue takes from a switch that keeps it in one arm stays a record" {
    try expectRecordSlot(.unchanged_in_one_arm, false);
}

test "N14b: a slot the Continue takes from a switch of constructions stays a record" {
    try expectRecordSlot(.switched, false);
}

test "N14b: a slot the Continue hands to a row that returns it stays a record" {
    try expectRecordSlot(.through_row, false);
}

test "N14b: the slot's output is read after the loop through the components it was split into" {
    var f: Fixture = undefined;
    f.init();
    defer f.deinit();
    const row = try recordSlotRow(&f, .fresh);
    const got = try f.site(row);
    defer testing.allocator.free(got);
    // No record is built or read in the row any more.
    try testing.expect(std.mem.find(u8, got, "record(") == null);
    try testing.expect(std.mem.find(u8, got, "field ") == null);
}
