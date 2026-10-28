//! The verifier (I5): the invariants of plan 5.2 that hold from M0.
//!
//! | Invariant | Checked by |
//! |---|---|
//! | every ref points to a row parameter, a parameter of an enclosing region, or an earlier node in an enclosing region | `checkRef` |
//! | every node's types agree with its op and its argument types; a `Lambda` owns one lambda body over its function type's parameters | `checkTypes` |
//! | a value that flows into a slot has a type that conforms to the slot's (`Types.widens`): the member of a record, tuple or tag, a `Wrap` or `Call` or `Apply` argument, a region's end value, a jump value, a loop argument. A projection takes its type from its argument and stays exact. | `checkTypes`, `region` |
//! | `speculatable` agrees with the op, the builtin table, the callee row, and the owned regions | `checkSpeculatable` |
//! | every path of a loop body ends in `Continue`, `Break`, `Return` or a `Jump`; `Continue` and `Break` appear only in loop bodies; a `Jump` names a join of the exiting switch its region belongs to, and a join jumps only to a later join | `checkEnd` |
//!
//! Every violation is a compiler bug. The verifier reports all of them, with
//! the node or region, so a test shows what broke rather than an unequal dump.

const std = @import("std");
const ir = @import("ir.zig");
const types_mod = @import("types.zig");
const prims = @import("prims.zig");
const live_mod = @import("live.zig");

const Allocator = std.mem.Allocator;
const Ref = ir.Ref;
const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const RowId = ir.RowId;
const TyId = ir.TyId;

/// The violations one verification found.
pub const Report = struct {
    gpa: Allocator,
    messages: std.ArrayList([]u8) = .empty,

    pub fn deinit(self: *Report) void {
        for (self.messages.items) |m| self.gpa.free(m);
        self.messages.deinit(self.gpa);
    }

    /// Whether no invariant was violated.
    pub fn ok(self: *const Report) bool {
        return self.messages.items.len == 0;
    }

    pub fn add(self: *Report, comptime fmt: []const u8, args: anytype) Allocator.Error!void {
        try self.messages.append(self.gpa, try std.fmt.allocPrint(self.gpa, fmt, args));
    }
};

/// Verify every row of `store`. Only what a row reaches is checked (`live.zig`):
/// a node nothing reads, and a region a rule dropped, have no reader, and
/// the rebuild does not copy them.
pub fn verifyAll(gpa: Allocator, store: *const ir.Store, types: *types_mod.Types) Allocator.Error!Report {
    var report: Report = .{ .gpa = gpa };
    errdefer report.deinit();
    var v: Verifier = .{ .store = store, .types = types, .report = &report };
    var live = try live_mod.ofStore(gpa, store);
    defer live.deinit(gpa);
    for (0..store.rows.items.len) |i| try v.row(RowId.of(@intCast(i)));
    for (live.nodes, 0..) |l, i| {
        if (l) try v.node(NodeId.of(@intCast(i)));
    }
    for (live.regions, 0..) |l, i| {
        if (l) try v.region(RegionId.of(@intCast(i)));
    }
    return report;
}

const Verifier = struct {
    store: *const ir.Store,
    types: *types_mod.Types,
    report: *Report,

    fn row(self: *Verifier, r: RowId) Allocator.Error!void {
        const body = self.store.row(r).body;
        const reg = self.store.region(body);
        if (reg.kind != .row_body or reg.row != r) try self.report.add("row {d}: body region {d} is not its row body", .{ r.index(), body.index() });
    }

    fn checkRef(self: *Verifier, where: RegionId, before: ?NodeId, ref: Ref, what: []const u8, id: u32) Allocator.Error!void {
        const row_id = self.store.region(where).row;
        switch (ref.kind) {
            .row_param => if (ref.output >= self.store.row(row_id).params.len)
                try self.report.add("{s} {d}: row parameter {d} out of range", .{ what, id, ref.output }),
            // N18c: only the root reads a slot, and the root is the one row
            // with fixed parameters that no call reaches.
            .input => {
                if (ref.target >= self.store.slots.items.len) return self.report.add("{s} {d}: input slot {d} does not exist", .{ what, id, ref.target });
                if (!self.store.row(row_id).fixed_params) try self.report.add("{s} {d}: reads input slot {d} in a row that is not the root", .{ what, id, ref.target });
            },
            .region_param => {
                const p = ref.regionId();
                if (p.index() >= self.store.regionCount()) return self.report.add("{s} {d}: region {d} does not exist", .{ what, id, p.index() });
                if (!self.store.encloses(p, where)) try self.report.add("{s} {d}: reads a parameter of region {d}, which does not enclose it", .{ what, id, p.index() });
                if (ref.output >= self.store.region(p).params.len) try self.report.add("{s} {d}: parameter {d} of region {d} out of range", .{ what, id, ref.output, p.index() });
            },
            .node => {
                const m = ref.nodeId();
                if (m.index() >= self.store.nodeCount()) return self.report.add("{s} {d}: node {d} does not exist", .{ what, id, m.index() });
                if (before) |b| if (m.index() >= b.index()) try self.report.add("{s} {d}: reads node {d}, which is not earlier", .{ what, id, m.index() });
                const m_region = self.store.nodes.items(.region)[m.index()];
                if (!self.store.encloses(m_region, where)) try self.report.add("{s} {d}: reads node {d}, whose region {d} does not enclose region {d}", .{ what, id, m.index(), m_region.index(), where.index() });
                if (ref.output >= self.store.nodes.items(.tys)[m.index()].len) try self.report.add("{s} {d}: output {d} of node {d} out of range", .{ what, id, ref.output, m.index() });
            },
        }
    }

    fn node(self: *Verifier, n: NodeId) Allocator.Error!void {
        const nd = self.store.node(n);
        for (self.store.refSlice(nd.args)) |a| try self.checkRef(nd.region, n, a, "node", n.index());
        for (self.store.regionSlice(nd.regions)) |r| {
            const reg = self.store.region(r);
            if (reg.owner != n) try self.report.add("node {d}: owns region {d}, whose owner is {d}", .{ n.index(), r.index(), reg.owner.index() });
            if (reg.parent != nd.region) try self.report.add("node {d}: owns region {d}, whose parent is not the node's region", .{ n.index(), r.index() });
        }
        try self.checkTypes(n, nd);
        try self.checkSpeculatable(n, nd);
    }

    // Whether literal `a` comes before `b` in key order: integers by value,
    // strings by their bytes. Other literals are no switch keys.
    fn litBefore(self: *const Verifier, a: ir.Lit, b: ir.Lit) bool {
        return switch (a.value) {
            .int => |x| blk: {
                const y = b.value.int;
                break :blk if (self.types.get(a.ty).int.signed()) @as(i128, @bitCast(x)) < @as(i128, @bitCast(y)) else x < y;
            },
            .str => |x| std.mem.order(u8, self.store.byteSlice(x), self.store.byteSlice(b.value.str)) == .lt,
            .bool_, .float, .dec, .bytes => false,
        };
    }

    fn argTy(self: *Verifier, nd: ir.Node, k: usize) TyId {
        return self.store.refTy(self.store.region(nd.region).row, self.store.refSlice(nd.args)[k]);
    }

    // Whether argument `k` of `nd` conforms to the slot type `slot`: the same
    // type, or one that widens to it (design.md "Row Coercion Primitive").
    fn argFits(self: *Verifier, nd: ir.Node, k: usize, slot: TyId) Allocator.Error!bool {
        return self.types.widens(self.argTy(nd, k), slot);
    }

    // Whether the arguments of `nd` from `first` on conform to `slots`, in
    // order. `Types.widens` can intern, which moves the type pools, so a
    // caller passes a copy of what it read from them.
    fn argsFit(self: *Verifier, nd: ir.Node, first: usize, slots: []const TyId) Allocator.Error!bool {
        const copy = try self.report.gpa.dupe(TyId, slots);
        defer self.report.gpa.free(copy);
        for (copy, first..) |slot, k| if (!try self.argFits(nd, k, slot)) return false;
        return true;
    }

    fn checkTypes(self: *Verifier, n: NodeId, nd: ir.Node) Allocator.Error!void {
        const tys = self.store.tySlice(nd.tys);
        const args = self.store.refSlice(nd.args);
        const single = tys.len == 1;
        const bad = switch (nd.op) {
            .lit => !single or self.store.lit(ir.LitId.of(nd.payload)).ty != tys[0],
            .prim => blk: {
                // A primitive the table does not hold takes the types the checker gave it.
                const p = prims.lookup(ir.PrimId.of(nd.payload)) orelse break :blk !single;
                if (!single or !p.takes(args.len)) break :blk true;
                // A checked chain is one only where N13u proved it fits.
                if (!p.associative and args.len > p.arity and !self.provedFit(n)) break :blk true;
                break :blk !try self.primTypesAgree(p, nd, tys[0]);
            },
            .record => blk: {
                if (!single) break :blk true;
                const t = self.types.get(tys[0]);
                if (t != .record) break :blk true;
                const members = self.types.memberSlice(t.record);
                const set = self.store.wordSlice(nd.aux);
                // A node that sets every member lists none, and one that
                // leaves a member unset lists the members it sets, in the
                // type's order, with every required member among them.
                if (args.len == members.len) {
                    if (set.len != 0) break :blk true;
                } else {
                    if (set.len != args.len) break :blk true;
                    var from: usize = 0;
                    for (set) |k| {
                        if (k < from or k >= members.len) break :blk true;
                        from = k + 1;
                    }
                    for (members, 0..) |m, k| {
                        if (!m.optional and std.mem.findScalar(u32, set, @intCast(k)) == null) break :blk true;
                    }
                }
                const slots = try self.report.gpa.alloc(TyId, args.len);
                defer self.report.gpa.free(slots);
                for (slots, 0..) |*slot, at| {
                    const k = if (args.len == members.len) at else set[at];
                    slot.* = self.types.tySlice(members[k].tys)[0];
                }
                break :blk !try self.argsFit(nd, 0, slots);
            },
            .tuple => blk: {
                if (!single) break :blk true;
                const t = self.types.get(tys[0]);
                if (t != .tuple) break :blk true;
                const elems = self.types.tySlice(t.tuple);
                if (elems.len != args.len) break :blk true;
                break :blk !try self.argsFit(nd, 0, elems);
            },
            .tag => blk: {
                if (!single) break :blk true;
                const t = self.types.get(tys[0]);
                if (t != .tag_union) break :blk true;
                const members = self.types.memberSlice(t.tag_union);
                const at = self.types.memberIndex(tys[0], types_mod.NameId.of(nd.payload)) orelse break :blk true;
                const payload = self.types.tySlice(members[at].tys);
                if (payload.len != args.len) break :blk true;
                break :blk !try self.argsFit(nd, 0, payload);
            },
            .field => blk: {
                const t = self.types.get(self.argTy(nd, 0));
                if (!single or t != .record) break :blk true;
                const members = self.types.memberSlice(t.record);
                break :blk nd.payload >= members.len or self.types.tySlice(members[nd.payload].tys)[0] != tys[0];
            },
            .index => blk: {
                const t = self.types.get(self.argTy(nd, 0));
                if (!single or t != .tuple) break :blk true;
                const elems = self.types.tySlice(t.tuple);
                break :blk nd.payload >= elems.len or elems[nd.payload] != tys[0];
            },
            .payload => blk: {
                const t = self.types.get(self.argTy(nd, 0));
                if (!single or t != .tag_union or nd.aux.len != 1) break :blk true;
                const members = self.types.memberSlice(t.tag_union);
                const at = self.types.memberIndex(self.argTy(nd, 0), types_mod.NameId.of(nd.payload)) orelse break :blk true;
                const payload = self.types.tySlice(members[at].tys);
                const k = self.store.wordSlice(nd.aux)[0];
                break :blk k >= payload.len or payload[k] != tys[0];
            },
            .wrap => blk: {
                if (!single or self.types.get(tys[0]) != .nominal) break :blk true;
                break :blk !try self.argFits(nd, 0, try self.types.unfold(tys[0]));
            },
            .unwrap => blk: {
                const arg = self.argTy(nd, 0);
                if (!single or self.types.get(arg) != .nominal) break :blk true;
                break :blk try self.types.unfold(arg) != tys[0];
            },
            .call => blk: {
                const callee = self.store.row(RowId.of(nd.payload));
                const params = self.store.tySlice(callee.params);
                if (!single or params.len != args.len) break :blk true;
                // The call is read at the row's result type or a wider one.
                if (!try self.types.widens(callee.result, tys[0])) break :blk true;
                break :blk !try self.argsFit(nd, 0, params);
            },
            .and_, .or_ => blk: {
                const bool_ty = try self.types.boolTy();
                if (!single or tys[0] != bool_ty or self.argTy(nd, 0) != bool_ty) break :blk true;
                for (self.store.regionSlice(nd.regions)) |r| if (!try self.endGives(r, &.{bool_ty})) break :blk true;
                break :blk false;
            },
            .switch_ => blk: {
                const regions = self.store.regionSlice(nd.regions);
                if (nd.payload > regions.len or nd.payload == 0) break :blk true;
                const scrutinee = self.argTy(nd, 0);
                if (self.types.armCount(scrutinee)) |arms| {
                    if (arms != nd.payload or nd.aux.len != 0) break :blk true;
                } else {
                    if (nd.aux.len + 1 != nd.payload) break :blk true;
                    // Keys are literals of the scrutinee's type, ascending and distinct (normal-form 3.7).
                    const keys = self.store.wordSlice(nd.aux);
                    for (keys, 0..) |k, i| {
                        const lit = self.store.lit(ir.LitId.of(k));
                        if (lit.ty != scrutinee) break :blk true;
                        if (i > 0 and !self.litBefore(self.store.lit(ir.LitId.of(keys[i - 1])), lit)) break :blk true;
                    }
                }
                for (regions[0..nd.payload]) |r| {
                    const end = self.store.region(r).end;
                    if (end.kind == .value and !try self.endGives(r, tys)) break :blk true;
                }
                break :blk false;
            },
            .for_range, .for_list, .loop => blk: {
                const body = self.store.regionSlice(nd.regions);
                if (body.len != 1) break :blk true;
                const params = self.store.tySlice(self.store.region(body[0]).params);
                const lead: usize = switch (nd.op) {
                    .for_range => 2,
                    .for_list => 1,
                    .loop => 0,
                    .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .lambda, .apply => unreachable, // this branch is reached for loop ops only
                };
                const header: usize = switch (nd.op) {
                    .for_range => 1,
                    .for_list => 2,
                    .loop => 0,
                    .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .lambda, .apply => unreachable, // this branch is reached for loop ops only
                };
                if (args.len < lead or params.len != header + (args.len - lead)) break :blk true;
                // A bounded loop's outputs are its slots, as they stand when
                // the indices run out. A general loop ends only in `Break`,
                // so its outputs are the values its `Break`s carry, and they
                // are free of its slots (N12).
                if (nd.op == .loop) {
                    for (0..args.len - lead) |k| if (!try self.argFits(nd, lead + k, params[header + k])) break :blk true;
                    break :blk false;
                }
                if (tys.len != args.len - lead) break :blk true;
                for (tys, 0..) |t, k| if (t != params[header + k] or !try self.argFits(nd, lead + k, t)) break :blk true;
                break :blk false;
            },
            .apply => blk: {
                if (!single or args.len == 0) break :blk true;
                const f = self.types.get(self.argTy(nd, 0));
                if (f != .func or f.func.ret != tys[0]) break :blk true;
                const params = self.types.tySlice(f.func.params);
                if (params.len != args.len - 1) break :blk true;
                break :blk !try self.argsFit(nd, 1, params);
            },
            .lambda => blk: {
                const body = self.store.regionSlice(nd.regions);
                if (!single or args.len != 0 or body.len != 1) break :blk true;
                const reg = self.store.region(body[0]);
                const f = self.types.get(tys[0]);
                if (reg.kind != .lambda_body or f != .func) break :blk true;
                if (!std.mem.eql(TyId, self.store.tySlice(reg.params), self.types.tySlice(f.func.params))) break :blk true;
                break :blk !try self.endGives(body[0], &.{f.func.ret});
            },
            .crash => !single or std.enums.fromInt(ir.CrashKind, nd.payload) == null,
            .derived, .list, .closure, .elem, .opt_field => !single,
        };
        if (bad) try self.report.add("node {d}: types disagree with op {s}", .{ n.index(), @tagName(nd.op) });
    }

    // Whether the values region `r` ends in conform to the types `want`.
    fn endGives(self: *Verifier, r: RegionId, want: []const TyId) Allocator.Error!bool {
        const reg = self.store.region(r);
        if (reg.end.kind != .value) return true;
        const refs = self.store.refSlice(reg.end.refs);
        if (refs.len != want.len) return false;
        for (refs, want) |ref, w| if (!try self.types.widens(self.store.refTy(reg.row, ref), w)) return false;
        return true;
    }

    fn primTypesAgree(self: *Verifier, p: prims.Prim, nd: ir.Node, result: TyId) Allocator.Error!bool {
        const operand: ?TyId = if (p.owner.int()) |int|
            try self.types.intTy(int)
        else if (p.owner.float()) |float|
            try self.types.floatTy(float)
        else switch (p.owner) {
            .bool_ => try self.types.boolTy(),
            .str => try self.types.strTy(),
            .list, .iter => null,
            .u8, .i8, .u16, .i16, .u32, .i32, .u64, .i64, .u128, .i128, .f32, .f64 => unreachable, // int and float owners are handled by the branches above
        };
        if (operand) |o| for (0..self.store.refSlice(nd.args).len) |k| if (self.argTy(nd, k) != o) return false;
        const bool_ty = try self.types.boolTy();
        return switch (p.method) {
            .is_eq, .is_lt, .is_lte, .is_gt, .is_gte, .not => result == bool_ty,
            .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat => result == self.argTy(nd, 0),
            .len => result == try self.types.intTy(.u64),
            .is_empty => result == bool_ty,
            .append, .keep_if => result == self.argTy(nd, 0),
            .fold => result == self.argTy(nd, 1),
            .prepend, .drop_first, .take_first => result == self.argTy(nd, 0),
            .fold_rev => result == self.argTy(nd, 1),
            .any, .all => result == bool_ty,
            .get, .map, .collect, .first, .last, .single, .with_capacity, .set, .repeat, .map2, .map_with_index, .sum => true,
        };
    }

    fn checkSpeculatable(self: *Verifier, n: NodeId, nd: ir.Node) Allocator.Error!void {
        const want: bool = switch (nd.op) {
            .lit, .record, .tuple, .list, .tag, .wrap, .unwrap, .closure, .field, .index, .opt_field, .lambda => true,
            .payload, .elem, .crash, .derived, .loop, .apply => false,
            // A checked op N13u proved fits its type is speculatable, and the
            // store records the proof (`ir.NodeRange.fits`).
            .prim => if (prims.lookup(ir.PrimId.of(nd.payload))) |p| p.speculatable or self.provedFit(n) else false,
            .call => self.store.row(RowId.of(nd.payload)).speculatable,
            .and_, .or_, .switch_, .for_range, .for_list => for (self.store.regionSlice(nd.regions)) |r| {
                if (!self.regionSpeculatable(r)) break false;
            } else true,
        };
        if (want != nd.flags.speculatable) try self.report.add("node {d}: speculatable is {}, the op gives {}", .{ n.index(), nd.flags.speculatable, want });
    }

    fn provedFit(self: *const Verifier, n: NodeId) bool {
        const r = self.store.ranges.get(n) orelse return false;
        return r.fits;
    }

    fn regionSpeculatable(self: *Verifier, r: RegionId) bool {
        const reg = self.store.region(r);
        switch (reg.end.kind) {
            .value, .continue_ => {},
            .open, .jump, .return_, .branch, .break_ => return false,
        }
        for (self.store.nodes.items(.region), self.store.nodes.items(.flags)) |nr, f| {
            if (nr == r and !f.speculatable) return false;
        }
        return true;
    }

    fn region(self: *Verifier, r: RegionId) Allocator.Error!void {
        const reg = self.store.region(r);
        if (reg.end.kind == .open) return self.report.add("region {d}: not closed", .{r.index()});
        if (reg.kind != .row_body and reg.owner == NodeId.none) return self.report.add("region {d}: has no owner", .{r.index()});
        for (self.store.refSlice(reg.end.refs)) |ref| try self.checkRef(r, null, ref, "region", r.index());
        const loop = self.innermostLoopBody(r);
        switch (reg.end.kind) {
            .open => unreachable, // open ends are reported just above
            .value => {
                if (reg.kind == .loop_body) try self.report.add("region {d}: a loop body ends in Value", .{r.index()});
                // A row body delivers the row's result.
                if (reg.kind == .row_body and !try self.endGives(r, &.{self.store.row(reg.row).result}))
                    try self.report.add("region {d}: the row body's value does not conform to the row's result", .{r.index()});
            },
            .return_ => {
                const refs = self.store.refSlice(reg.end.refs);
                const want = self.returnTy(r) orelse return;
                if (refs.len != 1 or !try self.types.widens(self.store.refTy(reg.row, refs[0]), want))
                    try self.report.add("region {d}: Return does not conform to the result of what it leaves", .{r.index()});
            },
            .continue_, .break_ => {
                const lb = loop orelse return self.report.add("region {d}: {s} outside a loop body", .{ r.index(), @tagName(reg.end.kind) });
                // `Continue` carries the next slots and `Break` the loop's outputs.
                const owner = self.store.node(self.store.region(lb).owner);
                const slots = self.store.tySlice(self.store.region(lb).params).len - switch (owner.op) {
                    .for_range => @as(usize, 1),
                    .for_list => 2,
                    .loop => 0,
                    .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .switch_, .lambda, .apply => unreachable, // a loop body is owned by a loop
                };
                const want = if (reg.end.kind == .continue_) slots else owner.tys.len;
                if (reg.end.refs.len != want) try self.report.add("region {d}: {s} carries {d} values for {d}", .{ r.index(), @tagName(reg.end.kind), reg.end.refs.len, want });
            },
            .branch => {
                const sw = NodeId.of(reg.end.target);
                if (sw.index() >= self.store.nodeCount() or self.store.node(sw).op != .switch_ or self.store.node(sw).region != r)
                    return self.report.add("region {d}: Branch names node {d}, which is not a switch in it", .{ r.index(), sw.index() });
                try self.checkExitingArms(sw);
            },
            .jump => try self.checkJump(r),
        }
    }

    // The result type of what a `Return` in region `r` leaves: the innermost
    // enclosing lambda, or else the row.
    // Null where the lambda is malformed, which `checkTypes` reports.
    fn returnTy(self: *Verifier, r: RegionId) ?TyId {
        var cur = r;
        while (true) {
            const reg = self.store.region(cur);
            switch (reg.kind) {
                .lambda_body => {
                    if (reg.owner == NodeId.none) return null;
                    return switch (self.types.get(self.store.tySlice(self.store.node(reg.owner).tys)[0])) {
                        .func => |f| f.ret,
                        .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .nominal, .opaque_, .recursive => null,
                    };
                },
                .row_body => return self.store.row(reg.row).result,
                .arm, .join, .operand, .loop_body => cur = reg.parent,
            }
        }
    }

    fn innermostLoopBody(self: *Verifier, r: RegionId) ?RegionId {
        var cur = r;
        while (cur != RegionId.none) {
            const reg = self.store.region(cur);
            switch (reg.kind) {
                .loop_body => return cur,
                .row_body, .lambda_body => return null,
                .arm, .join, .operand => cur = reg.parent,
            }
        }
        return null;
    }

    fn checkExitingArms(self: *Verifier, sw: NodeId) Allocator.Error!void {
        const nd = self.store.node(sw);
        for (self.store.regionSlice(nd.regions)) |r| {
            if (self.store.region(r).end.kind == .value) try self.report.add("node {d}: an arm or join of an exiting switch ends in Value", .{sw.index()});
        }
    }

    fn checkJump(self: *Verifier, r: RegionId) Allocator.Error!void {
        const reg = self.store.region(r);
        const target = RegionId.of(reg.end.target);
        if (target.index() >= self.store.regionCount()) return self.report.add("region {d}: jumps to region {d}, which does not exist", .{ r.index(), target.index() });
        const join = self.store.region(target);
        // The jumping region is an arm or join of the switch that owns the join, or nested in one.
        var cur = r;
        const sw = join.owner;
        while (cur != RegionId.none and self.store.region(cur).owner != sw) cur = self.store.region(cur).parent;
        if (join.kind != .join or cur == RegionId.none) return self.report.add("region {d}: jumps to region {d}, which is not a join of its exiting switch", .{ r.index(), target.index() });
        if (self.store.region(cur).kind == .join) {
            const regions = self.store.regionSlice(self.store.node(sw).regions);
            const from = std.mem.findScalar(RegionId, regions, cur).?;
            const to = std.mem.findScalar(RegionId, regions, target).?;
            if (to <= from) try self.report.add("region {d}: a join jumps to an earlier join {d}", .{ r.index(), target.index() });
        }
        const params = self.store.tySlice(join.params);
        const refs = self.store.refSlice(reg.end.refs);
        if (params.len != refs.len) return self.report.add("region {d}: jumps with {d} values to a join of {d} parameters", .{ r.index(), refs.len, params.len });
        for (params, refs) |p, ref| if (!try self.types.widens(self.store.refTy(reg.row, ref), p)) try self.report.add("region {d}: a jump value's type does not conform to the join parameter", .{r.index()});
    }
};

const testing = std.testing;
const builder_mod = @import("builder.zig");

test "a well-formed row verifies" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    _ = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const c = try b.call(.i64, .is_lt, &.{ Ref.rowParam(0), Ref.rowParam(1) });
    const arm0 = try b.openArm(c, 0);
    try b.close(.{ .value = &.{Ref.rowParam(0)} });
    const arm1 = try b.openArm(c, 1);
    try b.close(.{ .value = &.{Ref.rowParam(1)} });
    const sw = try b.switchOn(c, &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{});
    try b.endRow(.{ .value = &.{sw} });

    var report = try verifyAll(testing.allocator, &store, &types);
    defer report.deinit();
    try testing.expect(report.ok());
}

test "a ref into a sibling arm and a Continue outside a loop are reported" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    _ = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const c = try b.call(.i64, .is_lt, &.{ Ref.rowParam(0), Ref.rowParam(1) });
    const arm0 = try b.openArm(c, 0);
    const inner = try b.call(.i64, .plus_wrap, &.{ Ref.rowParam(0), Ref.rowParam(0) });
    try b.close(.{ .value = &.{inner} });
    const arm1 = try b.openArm(c, 1);
    try b.close(.{ .continue_ = &.{inner} });
    const sw = try b.switchOn(c, &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{});
    try b.endRow(.{ .value = &.{sw} });

    var report = try verifyAll(testing.allocator, &store, &types);
    defer report.deinit();
    try testing.expect(!report.ok());
    var saw_enclose = false;
    var saw_continue = false;
    for (report.messages.items) |m| {
        if (std.mem.find(u8, m, "does not enclose") != null) saw_enclose = true;
        if (std.mem.find(u8, m, "outside a loop body") != null) saw_continue = true;
    }
    try testing.expect(saw_enclose and saw_continue);
}

test "a flipped speculatable flag is reported" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    _ = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const q = try b.call(.i64, .div_trunc, &.{ Ref.rowParam(0), Ref.rowParam(1) });
    try b.endRow(.{ .value = &.{q} });
    store.nodes.items(.flags)[q.nodeId().index()].speculatable = true;

    var report = try verifyAll(testing.allocator, &store, &types);
    defer report.deinit();
    try testing.expectEqual(@as(usize, 1), report.messages.items.len);
}

test "a tag of a narrower union read at a wider union verifies, and the wider switch takes the arm of its own tag" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    // `C` is member 1 of the narrow union and member 2 of the wide one.
    const narrow = try types.tagUnionTy(&.{ .{ .name = "B", .payload = &.{} }, .{ .name = "C", .payload = &.{} } });
    const wide = try types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{} }, .{ .name = "C", .payload = &.{} } });
    const names = [_]types_mod.NameId{ try types.name("A"), try types.name("B"), try types.name("C") };

    // make() = C, at the narrow union.
    const make = try b.beginRow(&.{}, narrow);
    try b.endRow(.{ .value = &.{try b.tag(narrow, names[2], &.{})} });
    // read(w) = match w { A => 1, B => 2, C => 3 }
    const read = try b.beginRow(&.{wide}, i64_ty);
    var arms: [3]RegionId = undefined;
    for (&arms, names, 1..) |*arm, name, value| {
        arm.* = try b.openTagArm(Ref.rowParam(0), name);
        try b.close(.{ .value = &.{try b.litInt(i64_ty, @intCast(value))} });
    }
    try b.endRow(.{ .value = &.{try b.tagSwitchOn(Ref.rowParam(0), &names, &arms, &.{}, &.{i64_ty})} });
    // main() = read(make()): the narrow value flows into the wide parameter.
    const main = try b.beginRow(&.{}, i64_ty);
    try b.endRow(.{ .value = &.{try b.callRow(read, &.{try b.callRow(make, &.{})})} });

    var report = try verifyAll(testing.allocator, &store, &types);
    defer report.deinit();
    try testing.expect(report.ok());
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var strict = try @import("eval.zig").Evaluator.init(arena.allocator(), &store, &types, .strict);
    try testing.expect((try strict.run(main, &.{})).eql(.{ .int = 3 }));
}

test "a value of a wider union where a narrower one is expected does not verify" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const narrow = try types.tagUnionTy(&.{ .{ .name = "B", .payload = &.{} }, .{ .name = "C", .payload = &.{} } });
    const wide = try types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{} }, .{ .name = "C", .payload = &.{} } });
    const take = try b.beginRow(&.{narrow}, narrow);
    try b.endRow(.{ .value = &.{Ref.rowParam(0)} });
    _ = try b.beginRow(&.{wide}, narrow);
    try b.endRow(.{ .value = &.{try b.callRow(take, &.{Ref.rowParam(0)})} });

    var report = try verifyAll(testing.allocator, &store, &types);
    defer report.deinit();
    try testing.expect(!report.ok());
}

test "a call may carry a wider type than its row's result, and not a narrower one" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const narrow = try types.tagUnionTy(&.{ .{ .name = "B", .payload = &.{} }, .{ .name = "C", .payload = &.{} } });
    const wide = try types.tagUnionTy(&.{ .{ .name = "A", .payload = &.{} }, .{ .name = "B", .payload = &.{} }, .{ .name = "C", .payload = &.{} } });
    const names = [_]types_mod.NameId{ try types.name("A"), try types.name("B"), try types.name("C") };
    const make = try b.beginRow(&.{}, narrow);
    try b.endRow(.{ .value = &.{try b.tag(narrow, names[2], &.{})} });
    // A call of `make` at the wide union, which `make`'s result widens to.
    _ = try b.beginRow(&.{}, wide);
    try b.endRow(.{ .value = &.{try b.callRowAt(make, &.{}, wide)} });
    {
        var report = try verifyAll(testing.allocator, &store, &types);
        defer report.deinit();
        try testing.expect(report.ok());
    }
    // A call of the wide row at the narrow union, which the result does not widen to.
    const make_wide = try b.beginRow(&.{}, wide);
    try b.endRow(.{ .value = &.{try b.tag(wide, names[2], &.{})} });
    _ = try b.beginRow(&.{}, narrow);
    try b.endRow(.{ .value = &.{try b.callRowAt(make_wide, &.{}, narrow)} });
    var report = try verifyAll(testing.allocator, &store, &types);
    defer report.deinit();
    try testing.expect(!report.ok());
}

test "an input slot verifies in the root and is reported in any other row" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    const row = try b.beginRow(&.{i64_ty}, i64_ty);
    const sum = try b.call(.i64, .plus_wrap, &.{ Ref.rowParam(0), try b.input(i64_ty, 0) });
    try b.endRow(.{ .value = &.{sum} });

    var not_root = try verifyAll(testing.allocator, &store, &types);
    defer not_root.deinit();
    try testing.expect(!not_root.ok());
    var saw = false;
    for (not_root.messages.items) |m| {
        if (std.mem.find(u8, m, "in a row that is not the root") != null) saw = true;
    }
    try testing.expect(saw);

    store.rows.items[row.index()].fixed_params = true;
    var root = try verifyAll(testing.allocator, &store, &types);
    defer root.deinit();
    try testing.expect(root.ok());
}
