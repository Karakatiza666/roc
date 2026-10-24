//! The dump text format (I7), read by golden tests and `roc reify --dump`.
//!
//! One line per node, nested regions indented under the node that owns them,
//! and each region's terminator last:
//!
//! ```
//! row r0 (I64, I64) -> I64
//!   n0 = Num.I64.is_lt(p0, p1) : Bool
//!   n1 = switch n0 : I64
//!     arm 0
//!       value p0
//!     arm 1
//!       value p1
//!   value n1
//! ```

const std = @import("std");
const collections = @import("collections");
const ir = @import("ir.zig");
const types_mod = @import("types.zig");
const live_mod = @import("live.zig");
const number = @import("number.zig");

const Allocator = std.mem.Allocator;

const Writer = std.Io.Writer;
const Ref = ir.Ref;
const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const RowId = ir.RowId;
const TyId = ir.TyId;

/// Write every row of `store`.
pub fn dumpAll(w: *Writer, store: *const ir.Store, types: *const types_mod.Types) Writer.Error!void {
    for (0..store.rows.items.len) |i| try dumpRow(w, store, types, RowId.of(@intCast(i)));
}

/// Write one row.
pub fn dumpRow(w: *Writer, store: *const ir.Store, types: *const types_mod.Types, row: RowId) Writer.Error!void {
    const view: View = .{ .store = store, .types = types };
    try view.row(w, row, row.index());
}

/// Write the rows `root` reaches, as `code_emit` writes them: only the nodes
/// a row reaches, numbered canonically within each row (N9, `number.zig`),
/// and the rows in the order their `Call` and `Closure` nodes are met, root
/// first. A region parameter is `s` and the index of the node that owns the
/// region; a jump names the join by its place among its switch's joins.
///
/// Two sites with one normal form dump alike, whatever dead nodes the
/// builder left behind and whatever order it built the rest in.
pub fn dumpSite(w: *Writer, gpa: Allocator, store: *const ir.Store, types: *const types_mod.Types, root: RowId) (Writer.Error || Allocator.Error)!void {
    var returns = try live_mod.Returns.init(gpa, store);
    defer returns.deinit(gpa);
    var rows: ir.RowTable(number.Numbering) = .empty;
    defer {
        for (rows.values()) |*n| n.deinit(gpa);
        rows.deinit(gpa);
    }
    try number.siteRows(gpa, store, &returns, root, &rows);
    const index = try gpa.alloc(u32, store.nodeCount());
    defer gpa.free(index);
    var members: collections.DenseMapUnmanaged(RegionId, std.ArrayList(NodeId)) = .empty;
    defer {
        var lists = members.valueIterator();
        while (lists.next()) |l| l.deinit(gpa);
        members.deinit(gpa);
    }
    const regions = store.nodes.items(.region);
    for (rows.values()) |*numbering| for (numbering.order.items, 0..) |n, i| {
        index[n.index()] = @intCast(i);
        const gop = try members.getOrPut(gpa, regions[n.index()]);
        if (!gop.found_existing) gop.value_ptr.* = .empty;
        try gop.value_ptr.append(gpa, n);
    };
    const view: View = .{ .store = store, .types = types, .index = index, .members = &members, .rows = &rows };
    for (rows.keys(), 0..) |r, at| try view.row(w, r, @intCast(at));
}

/// How the dump names what it writes: every node by its store id, or only
/// the nodes a site keeps, numbered as the emitter numbers them.
const View = struct {
    store: *const ir.Store,
    types: *const types_mod.Types,
    index: ?[]u32 = null,
    /// Per region, in site mode: its nodes in numbering order.
    members: ?*const collections.DenseMapUnmanaged(RegionId, std.ArrayList(NodeId)) = null,
    rows: ?*const ir.RowTable(number.Numbering) = null,

    fn nodeName(v: View, n: u32) u32 {
        const index = v.index orelse return n;
        return index[n];
    }

    fn rowName(v: View, r: u32) u32 {
        const rows = v.rows orelse return r;
        return @intCast(rows.getIndex(RowId.of(r)).?);
    }

    fn row(v: View, w: *Writer, id: RowId, name: u32) Writer.Error!void {
        const r = v.store.row(id);
        try w.print("row r{d} (", .{name});
        for (v.store.tySlice(r.params), 0..) |t, i| {
            if (i > 0) try w.writeAll(", ");
            try writeTy(w, v.types, t);
        }
        try w.writeAll(") -> ");
        try writeTy(w, v.types, r.result);
        if (r.recursive) try w.writeAll(" recursive");
        try w.writeAll("\n");
        try v.regionOf(w, r.body, 1);
    }

    fn regionOf(v: View, w: *Writer, r: RegionId, depth: usize) Writer.Error!void {
        if (v.members) |members| {
            if (members.get(r)) |list| for (list.items) |n| try v.node(w, n, depth);
        } else for (v.store.nodes.items(.region), 0..) |nr, i| {
            if (nr == r) try v.node(w, NodeId.of(@intCast(i)), depth);
        }
        const end = v.store.region(r).end;
        try indent(w, depth);
        switch (end.kind) {
            .open => try w.writeAll("open"),
            .value => try w.writeAll("value"),
            .jump => try v.jumpName(w, RegionId.of(end.target)),
            .return_ => try w.writeAll("return"),
            .branch => try w.print("branch n{d}", .{v.nodeName(end.target)}),
            .continue_ => try w.writeAll("continue"),
            .break_ => try w.writeAll("break"),
        }
        try v.refs(w, v.store.refSlice(end.refs), " ");
        try w.writeAll("\n");
    }

    fn jumpName(v: View, w: *Writer, join: RegionId) Writer.Error!void {
        if (v.index == null) return w.print("jump j{d}", .{join.index()});
        const sw = v.store.node(v.store.region(join).owner);
        const joins = v.store.regionSlice(sw.regions)[sw.payload..];
        const at = std.mem.findScalar(RegionId, joins, join).?;
        try w.print("jump j{d}", .{at});
    }

    fn regionName(v: View, w: *Writer, sub: RegionId) Writer.Error!void {
        if (v.index == null) return w.print("s{d}", .{sub.index()});
        try w.print("s{d}", .{v.nodeName(v.store.region(sub).owner.index())});
    }

    fn node(v: View, w: *Writer, n: NodeId, depth: usize) Writer.Error!void {
        const store = v.store;
        const types = v.types;
        const nd = store.node(n);
        try indent(w, depth);
        try w.print("n{d} = ", .{v.nodeName(n.index())});
        const args = store.refSlice(nd.args);
        switch (nd.op) {
            .lit => try writeLit(w, store, types, store.lit(ir.LitId.of(nd.payload))),
            .prim => {
                const p = store.primName(ir.PrimId.of(nd.payload));
                try w.print("{s}.{s}(", .{ p.owner, p.method });
                try v.refs(w, args, "");
                try w.writeAll(")");
            },
            .call, .closure => {
                try w.print("{s} r{d}(", .{ @tagName(nd.op), v.rowName(nd.payload) });
                try v.refs(w, args, "");
                try w.writeAll(")");
            },
            .tag => {
                try w.print("tag {s}(", .{types.nameText(types_mod.NameId.of(nd.payload))});
                try v.refs(w, args, "");
                try w.writeAll(")");
            },
            .field, .index => {
                try w.print("{s} {d}(", .{ @tagName(nd.op), nd.payload });
                try v.refs(w, args, "");
                try w.writeAll(")");
            },
            .payload => {
                try w.print("payload {s}.{d}(", .{ types.nameText(types_mod.NameId.of(nd.payload)), store.wordSlice(nd.aux)[0] });
                try v.refs(w, args, "");
                try w.writeAll(")");
            },
            .switch_ => {
                try w.writeAll("switch ");
                try v.refs(w, args, "");
            },
            .crash, .derived, .record, .tuple, .list, .wrap, .unwrap, .elem, .opt_field, .and_, .or_, .for_range, .for_list, .loop, .lambda, .apply => {
                try w.print("{s}(", .{opName(nd.op)});
                try v.refs(w, args, "");
                try w.writeAll(")");
            },
        }
        try w.writeAll(" :");
        for (store.tySlice(nd.tys)) |t| {
            try w.writeAll(" ");
            try writeTy(w, types, t);
        }
        if (!nd.flags.speculatable) try w.writeAll(" !spec");
        try w.writeAll("\n");
        const owned = store.regionSlice(nd.regions);
        for (owned, 0..) |sub, k| {
            try indent(w, depth + 1);
            const reg = store.region(sub);
            switch (reg.kind) {
                .arm => {
                    // A literal switch's arm names its key, and its last arm is the default.
                    const keys = store.wordSlice(nd.aux);
                    if (nd.op != .switch_ or keys.len == 0) {
                        try w.print("arm {d}", .{k});
                    } else if (k < keys.len) {
                        try w.writeAll("arm ");
                        try writeLit(w, store, types, store.lit(ir.LitId.of(keys[k])));
                    } else try w.writeAll("default");
                },
                .join => if (v.index == null) try w.print("join j{d}", .{sub.index()}) else try w.print("join j{d}", .{k - nd.payload}),
                .operand => try w.writeAll("operand"),
                .loop_body => try w.writeAll("body"),
                .lambda_body => try w.writeAll("lambda"),
                .row_body => unreachable, // row_body regions are dumped by the row, not as a node's region
            }
            const params = store.tySlice(reg.params);
            if (params.len > 0) {
                try w.writeAll(" (");
                for (params, 0..) |t, i| {
                    if (i > 0) try w.writeAll(", ");
                    try v.regionName(w, sub);
                    try w.print(".{d}: ", .{i});
                    try writeTy(w, types, t);
                }
                try w.writeAll(")");
            }
            try w.writeAll("\n");
            try v.regionOf(w, sub, depth + 2);
        }
    }

    fn refs(v: View, w: *Writer, list: []const Ref, lead: []const u8) Writer.Error!void {
        for (list, 0..) |r, i| {
            try w.writeAll(if (i == 0) lead else ", ");
            switch (r.kind) {
                .row_param => try w.print("p{d}", .{r.output}),
                .region_param => {
                    try v.regionName(w, r.regionId());
                    try w.print(".{d}", .{r.output});
                },
                .node => if (r.output == 0) try w.print("n{d}", .{v.nodeName(r.target)}) else try w.print("n{d}.{d}", .{ v.nodeName(r.target), r.output }),
            }
        }
    }
};

fn indent(w: *Writer, depth: usize) Writer.Error!void {
    for (0..depth) |_| try w.writeAll("  ");
}

fn opName(op: ir.Op) []const u8 {
    return switch (op) {
        .and_ => "and",
        .or_ => "or",
        .switch_ => "switch",
        .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .for_range, .for_list, .loop, .lambda, .apply => @tagName(op),
    };
}

fn writeLit(w: *Writer, store: *const ir.Store, types: *const types_mod.Types, lit: ir.Lit) Writer.Error!void {
    switch (lit.value) {
        .int => |bits| {
            const int = types.get(lit.ty).int;
            if (int.signed()) try w.print("{d}", .{@as(i128, @bitCast(bits))}) else try w.print("{d}", .{bits});
        },
        .float => |bits| try w.print("float 0x{x}", .{bits}),
        .bool_ => |b| try w.writeAll(if (b) "True" else "False"),
        .str => |span| try w.print("\"{s}\"", .{store.byteSlice(span)}),
        .dec => |bits| try w.print("dec {d}", .{@as(i128, @bitCast(bits))}),
        .bytes => |span| try w.print("bytes {d}", .{span.len}),
    }
}

/// Write a type.
pub fn writeTy(w: *Writer, types: *const types_mod.Types, ty: TyId) Writer.Error!void {
    switch (types.get(ty)) {
        .bool_ => try w.writeAll("Bool"),
        .str => try w.writeAll("Str"),
        .int => |i| try w.writeAll(switch (i) {
            .u8 => "U8",
            .i8 => "I8",
            .u16 => "U16",
            .i16 => "I16",
            .u32 => "U32",
            .i32 => "I32",
            .u64 => "U64",
            .i64 => "I64",
            .u128 => "U128",
            .i128 => "I128",
        }),
        .float => |f| try w.writeAll(switch (f) {
            .f32 => "F32",
            .f64 => "F64",
        }),
        .dec => try w.writeAll("Dec"),
        .opaque_ => |o| {
            try w.writeAll(types.nameText(o.name));
            const args = types.tySlice(o.args);
            if (args.len > 0) {
                try w.writeAll("(");
                for (args, 0..) |t, i| {
                    if (i > 0) try w.writeAll(", ");
                    try writeTy(w, types, t);
                }
                try w.writeAll(")");
            }
        },
        .recursive => |n| try w.writeAll(types.nameText(n)),
        .record => |span| {
            try w.writeAll("{ ");
            for (types.memberSlice(span), 0..) |m, i| {
                if (i > 0) try w.writeAll(", ");
                try w.print("{s} {s} ", .{ types.nameText(m.name), if (m.optional) "?" else ":" });
                try writeTy(w, types, types.tySlice(m.tys)[0]);
            }
            try w.writeAll(" }");
        },
        .tuple => |span| {
            try w.writeAll("(");
            for (types.tySlice(span), 0..) |t, i| {
                if (i > 0) try w.writeAll(", ");
                try writeTy(w, types, t);
            }
            try w.writeAll(")");
        },
        .tag_union => |span| {
            try w.writeAll("[");
            for (types.memberSlice(span), 0..) |m, i| {
                if (i > 0) try w.writeAll(", ");
                try w.writeAll(types.nameText(m.name));
                const payload = types.tySlice(m.tys);
                if (payload.len > 0) {
                    try w.writeAll("(");
                    for (payload, 0..) |t, k| {
                        if (k > 0) try w.writeAll(", ");
                        try writeTy(w, types, t);
                    }
                    try w.writeAll(")");
                }
            }
            try w.writeAll("]");
        },
        .list => |elem| {
            try w.writeAll("List(");
            try writeTy(w, types, elem);
            try w.writeAll(")");
        },
        .nominal => |nom| try w.writeAll(types.nameText(nom.name)),
        .func => |f| {
            try w.writeAll("(");
            for (types.tySlice(f.params), 0..) |t, i| {
                if (i > 0) try w.writeAll(", ");
                try writeTy(w, types, t);
            }
            try w.writeAll(" -> ");
            try writeTy(w, types, f.ret);
            try w.writeAll(")");
        },
    }
}

const testing = std.testing;
const builder_mod = @import("builder.zig");

test "a switch dumps with its arms nested under it" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    const row = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const c = try b.call(.i64, .is_lt, &.{ Ref.rowParam(0), Ref.rowParam(1) });
    const arm0 = try b.openArm(c, 0);
    try b.close(.{ .value = &.{Ref.rowParam(0)} });
    const arm1 = try b.openArm(c, 1);
    try b.close(.{ .value = &.{Ref.rowParam(1)} });
    const sw = try b.switchOn(c, &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{});
    try b.endRow(.{ .value = &.{sw} });

    var out: Writer.Allocating = .init(testing.allocator);
    defer out.deinit();
    try dumpRow(&out.writer, &store, &types, row);
    try testing.expectEqualStrings(
        \\row r0 (I64, I64) -> I64
        \\  n0 = Num.I64.is_lt(p0, p1) : Bool
        \\  n1 = switch n0 : I64
        \\    arm 0
        \\      value p0
        \\    arm 1
        \\      value p1
        \\  value n1
        \\
    , out.written());
}

test "a site dumps only what its rows reach, numbered as the emitter numbers it" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    // A row nothing calls, then the root, which builds a node it never reads
    // and then calls a helper.
    _ = try b.beginRow(&.{i64_ty}, i64_ty);
    try b.endRow(.{ .value = &.{Ref.rowParam(0)} });
    const helper = try b.beginRow(&.{i64_ty}, i64_ty);
    try b.endRow(.{ .value = &.{try b.call(.i64, .plus, &.{ Ref.rowParam(0), Ref.rowParam(0) })} });
    const root = try b.beginRow(&.{i64_ty}, i64_ty);
    _ = try b.call(.i64, .times, &.{ Ref.rowParam(0), Ref.rowParam(0) });
    try b.endRow(.{ .value = &.{try b.callRow(helper, &.{Ref.rowParam(0)})} });

    var out: Writer.Allocating = .init(testing.allocator);
    defer out.deinit();
    try dumpSite(&out.writer, testing.allocator, &store, &types, root);
    try testing.expectEqualStrings(
        \\row r0 (I64) -> I64
        \\  n0 = call r1(p0) : I64 !spec
        \\  value n0
        \\row r1 (I64) -> I64
        \\  n0 = Num.I64.plus(p0, p0) : I64 !spec
        \\  value n0
        \\
    , out.written());
}
