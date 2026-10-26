//! Interned types of the normal form (I2).
//!
//! Aliases are expanded before a type reaches this table, record fields and
//! tags are kept in name order, and nominals are named. Two structurally equal
//! types get one `TyId`, so type equality is integer equality.

const std = @import("std");
const collections = @import("collections");
const ir = @import("ir.zig");

const Allocator = std.mem.Allocator;
const TyId = ir.TyId;

/// An interned name: a field, a tag, or a nominal type.
pub const NameId = enum(u32) {
    _,

    /// The name with this index.
    pub fn of(i: u32) NameId {
        return @fromBackingInt(@intCast(i));
    }

    /// This name's index.
    pub fn index(self: NameId) u32 {
        return @backingInt(self);
    }
};

/// Integer widths and signedness of the builtin integer types.
pub const IntTy = enum(u8) {
    u8,
    i8,
    u16,
    i16,
    u32,
    i32,
    u64,
    i64,
    u128,
    i128,

    /// Width in bits.
    pub fn bits(self: IntTy) u8 {
        return switch (self) {
            .u8, .i8 => 8,
            .u16, .i16 => 16,
            .u32, .i32 => 32,
            .u64, .i64 => 64,
            .u128, .i128 => 128,
        };
    }

    /// Whether the type is signed.
    pub fn signed(self: IntTy) bool {
        return switch (self) {
            .i8, .i16, .i32, .i64, .i128 => true,
            .u8, .u16, .u32, .u64, .u128 => false,
        };
    }

    /// The least value, as an `i129`-safe `i256`.
    pub fn min(self: IntTy) i256 {
        if (!self.signed()) return 0;
        return -(@as(i256, 1) << @intCast(self.bits() - 1));
    }

    /// The greatest value.
    pub fn max(self: IntTy) i256 {
        if (!self.signed()) return (@as(i256, 1) << @intCast(self.bits())) - 1;
        return (@as(i256, 1) << @intCast(self.bits() - 1)) - 1;
    }
};

/// Float widths.
pub const FloatTy = enum(u8) { f32, f64 };

/// A record field or a tag: a name and the types it carries.
pub const Member = struct {
    name: NameId,
    tys: ir.Span,
    /// A record field the type marks optional: a value of the type may lack it.
    optional: bool = false,
};

/// The structure of one interned type.
pub const Ty = union(enum) {
    bool_,
    str,
    int: IntTy,
    float: FloatTy,
    dec,
    /// Fields in name order; each member carries exactly one type.
    record: ir.Span,
    tuple: ir.Span,
    /// Tags in name order; each member carries its payload types.
    tag_union: ir.Span,
    list: TyId,
    nominal: struct { name: NameId, backing: TyId },
    func: struct { params: ir.Span, ret: TyId },
    /// A nominal whose backing this module may not read, named with its
    /// type arguments.
    opaque_: struct { name: NameId, args: ir.Span },
    /// A reference back to the enclosing `nominal` of this name, so a
    /// recursive type is a finite tree.
    recursive: NameId,
};

/// A field of a record under construction, before sorting.
pub const FieldSpec = struct {
    name: []const u8,
    ty: TyId,
    optional: bool = false,
};

/// A tag of a union under construction, before sorting.
pub const TagSpec = struct {
    name: []const u8,
    payload: []const TyId,
};

/// The type table.
pub const Types = struct {
    gpa: Allocator,
    tys: std.ArrayList(Ty) = .empty,
    members: std.ArrayList(Member) = .empty,
    ty_pool: std.ArrayList(TyId) = .empty,
    names: std.StringArrayHashMapUnmanaged(void) = .empty,
    interned: std.HashMapUnmanaged(TyKey, TyId, TyKeyContext, std.hash_map.default_max_load_percentage) = .empty,
    key_words: std.ArrayList(u32) = .empty,

    /// The structural key of a type: a slice of `key_words`.
    const TyKey = struct { start: u32, len: u32 };

    const TyKeyContext = struct {
        words: *const std.ArrayList(u32),

        pub fn hash(ctx: TyKeyContext, key: TyKey) u64 {
            return std.hash.Wyhash.hash(0, std.mem.sliceAsBytes(ctx.words.items[key.start..][0..key.len]));
        }

        pub fn eql(ctx: TyKeyContext, a: TyKey, b: TyKey) bool {
            return std.mem.eql(u32, ctx.words.items[a.start..][0..a.len], ctx.words.items[b.start..][0..b.len]);
        }
    };

    pub fn init(gpa: Allocator) Types {
        return .{ .gpa = gpa };
    }

    pub fn deinit(self: *Types) void {
        self.tys.deinit(self.gpa);
        self.members.deinit(self.gpa);
        self.ty_pool.deinit(self.gpa);
        for (self.names.keys()) |k| self.gpa.free(k);
        self.names.deinit(self.gpa);
        self.interned.deinit(self.gpa);
        self.key_words.deinit(self.gpa);
    }

    /// Intern a name.
    pub fn name(self: *Types, text: []const u8) Allocator.Error!NameId {
        if (self.names.getIndex(text)) |i| return NameId.of(@intCast(i));
        const owned = try self.gpa.dupe(u8, text);
        errdefer self.gpa.free(owned);
        try self.names.put(self.gpa, owned, {});
        return NameId.of(@intCast(self.names.count() - 1));
    }

    /// The name `text` interns to, when something interned it.
    pub fn findName(self: *const Types, text: []const u8) ?NameId {
        return if (self.names.getIndex(text)) |i| NameId.of(@intCast(i)) else null;
    }

    /// The text of a name.
    pub fn nameText(self: *const Types, n: NameId) []const u8 {
        return self.names.keys()[n.index()];
    }

    /// The structure of a type.
    pub fn get(self: *const Types, ty: TyId) Ty {
        return self.tys.items[ty.index()];
    }

    /// The members of a record or tag union.
    pub fn memberSlice(self: *const Types, span: ir.Span) []const Member {
        return self.members.items[span.start..][0..span.len];
    }

    /// The types of a span of the type pool.
    pub fn tySlice(self: *const Types, span: ir.Span) []const TyId {
        return self.ty_pool.items[span.start..][0..span.len];
    }

    /// `Bool`.
    pub fn boolTy(self: *Types) Allocator.Error!TyId {
        return self.intern(.bool_, &.{0});
    }

    /// `Str`.
    pub fn strTy(self: *Types) Allocator.Error!TyId {
        return self.intern(.str, &.{1});
    }

    /// A builtin integer type.
    pub fn intTy(self: *Types, int: IntTy) Allocator.Error!TyId {
        return self.intern(.{ .int = int }, &.{ 2, @backingInt(int) });
    }

    /// `Dec`.
    pub fn decTy(self: *Types) Allocator.Error!TyId {
        return self.intern(.dec, &.{10});
    }

    /// An opaque nominal named `text` at `args`.
    pub fn opaqueTy(self: *Types, text: []const u8, args: []const TyId) Allocator.Error!TyId {
        const n = try self.name(text);
        var key: std.ArrayList(u32) = .empty;
        defer key.deinit(self.gpa);
        try key.appendSlice(self.gpa, &.{ 11, n.index() });
        for (args) |a| try key.append(self.gpa, a.index());
        if (self.lookup(key.items)) |found| return found;
        const span = try self.addTyPool(args);
        return self.intern(.{ .opaque_ = .{ .name = n, .args = span } }, key.items);
    }

    /// A reference back to the enclosing nominal named `text`.
    pub fn recursiveTy(self: *Types, text: []const u8) Allocator.Error!TyId {
        const n = try self.name(text);
        return self.intern(.{ .recursive = n }, &.{ 12, n.index() });
    }

    /// A builtin float type.
    pub fn floatTy(self: *Types, float: FloatTy) Allocator.Error!TyId {
        return self.intern(.{ .float = float }, &.{ 3, @backingInt(float) });
    }

    /// `List(elem)`.
    pub fn listTy(self: *Types, elem: TyId) Allocator.Error!TyId {
        return self.intern(.{ .list = elem }, &.{ 4, elem.index() });
    }

    /// A tuple of `elems`.
    pub fn tupleTy(self: *Types, elems: []const TyId) Allocator.Error!TyId {
        var key: std.ArrayList(u32) = .empty;
        defer key.deinit(self.gpa);
        try key.append(self.gpa, 5);
        for (elems) |e| try key.append(self.gpa, e.index());
        if (self.lookup(key.items)) |found| return found;
        const span = try self.addTyPool(elems);
        return self.intern(.{ .tuple = span }, key.items);
    }

    /// A record of `fields`, which are sorted by name here.
    pub fn recordTy(self: *Types, fields: []const FieldSpec) Allocator.Error!TyId {
        const sorted = try self.gpa.dupe(FieldSpec, fields);
        defer self.gpa.free(sorted);
        std.mem.sort(FieldSpec, sorted, {}, struct {
            fn lt(_: void, a: FieldSpec, b: FieldSpec) bool {
                return std.mem.order(u8, a.name, b.name) == .lt;
            }
        }.lt);
        var key: std.ArrayList(u32) = .empty;
        defer key.deinit(self.gpa);
        try key.append(self.gpa, 6);
        var members: std.ArrayList(Member) = .empty;
        defer members.deinit(self.gpa);
        for (sorted) |f| {
            const n = try self.name(f.name);
            try key.appendSlice(self.gpa, &.{ n.index(), f.ty.index(), @intFromBool(f.optional) });
            try members.append(self.gpa, .{ .name = n, .tys = try self.addTyPool(&.{f.ty}), .optional = f.optional });
        }
        if (self.lookup(key.items)) |found| return found;
        const span = try self.addMembers(members.items);
        return self.intern(.{ .record = span }, key.items);
    }

    /// A closed tag union of `tags`, which are sorted by name here.
    pub fn tagUnionTy(self: *Types, tags: []const TagSpec) Allocator.Error!TyId {
        const sorted = try self.gpa.dupe(TagSpec, tags);
        defer self.gpa.free(sorted);
        std.mem.sort(TagSpec, sorted, {}, struct {
            fn lt(_: void, a: TagSpec, b: TagSpec) bool {
                return std.mem.order(u8, a.name, b.name) == .lt;
            }
        }.lt);
        var key: std.ArrayList(u32) = .empty;
        defer key.deinit(self.gpa);
        try key.append(self.gpa, 7);
        var members: std.ArrayList(Member) = .empty;
        defer members.deinit(self.gpa);
        for (sorted) |t| {
            const n = try self.name(t.name);
            try key.appendSlice(self.gpa, &.{ n.index(), @intCast(t.payload.len) });
            for (t.payload) |p| try key.append(self.gpa, p.index());
            try members.append(self.gpa, .{ .name = n, .tys = try self.addTyPool(t.payload) });
        }
        if (self.lookup(key.items)) |found| return found;
        const span = try self.addMembers(members.items);
        return self.intern(.{ .tag_union = span }, key.items);
    }

    /// A nominal type named `text` over `backing`.
    pub fn nominalTy(self: *Types, text: []const u8, backing: TyId) Allocator.Error!TyId {
        const n = try self.name(text);
        return self.intern(.{ .nominal = .{ .name = n, .backing = backing } }, &.{ 8, n.index(), backing.index() });
    }

    /// A function type.
    pub fn funcTy(self: *Types, params: []const TyId, ret: TyId) Allocator.Error!TyId {
        var key: std.ArrayList(u32) = .empty;
        defer key.deinit(self.gpa);
        try key.appendSlice(self.gpa, &.{ 9, ret.index() });
        for (params) |p| try key.append(self.gpa, p.index());
        if (self.lookup(key.items)) |found| return found;
        const span = try self.addTyPool(params);
        return self.intern(.{ .func = .{ .params = span, .ret = ret } }, key.items);
    }

    /// The backing of the nominal `nominal`, with every `recursive` of its
    /// name that refers to it replaced by the nominal itself: the type an
    /// `Unwrap` gives and a `Wrap` takes.
    ///
    /// A `recursive` refers to the nearest enclosing nominal of its name, so
    /// the backing on its own leaves each one dangling, and unfolding closes
    /// it. A nested nominal of the same name binds its own, so the
    /// replacement stops there.
    pub fn unfold(self: *Types, nominal: TyId) Allocator.Error!TyId {
        const n = self.get(nominal).nominal;
        var memo: collections.DenseMapUnmanaged(TyId, TyId) = .empty;
        defer memo.deinit(self.gpa);
        return self.replaceRecursive(n.backing, n.name, nominal, &memo);
    }

    fn replaceRecursive(self: *Types, ty: TyId, name_id: NameId, with: TyId, memo: *collections.DenseMapUnmanaged(TyId, TyId)) Allocator.Error!TyId {
        if (memo.get(ty)) |done| return done;
        const out: TyId = switch (self.get(ty)) {
            .recursive => |r| if (r == name_id) with else ty,
            .bool_, .str, .int, .float, .dec => ty,
            .list => |elem| try self.listTy(try self.replaceRecursive(elem, name_id, with, memo)),
            .tuple => |span| blk: {
                const elems = try self.gpa.dupe(TyId, self.tySlice(span));
                defer self.gpa.free(elems);
                for (elems) |*e| e.* = try self.replaceRecursive(e.*, name_id, with, memo);
                break :blk try self.tupleTy(elems);
            },
            .func => |f| blk: {
                const params = try self.gpa.dupe(TyId, self.tySlice(f.params));
                defer self.gpa.free(params);
                for (params) |*p| p.* = try self.replaceRecursive(p.*, name_id, with, memo);
                break :blk try self.funcTy(params, try self.replaceRecursive(f.ret, name_id, with, memo));
            },
            .opaque_ => |o| blk: {
                const args = try self.gpa.dupe(TyId, self.tySlice(o.args));
                defer self.gpa.free(args);
                for (args) |*a| a.* = try self.replaceRecursive(a.*, name_id, with, memo);
                const text = try self.gpa.dupe(u8, self.nameText(o.name));
                defer self.gpa.free(text);
                break :blk try self.opaqueTy(text, args);
            },
            .nominal => |m| blk: {
                if (m.name == name_id) break :blk ty;
                const backing = try self.replaceRecursive(m.backing, name_id, with, memo);
                const text = try self.gpa.dupe(u8, self.nameText(m.name));
                defer self.gpa.free(text);
                break :blk try self.nominalTy(text, backing);
            },
            .record => |span| blk: {
                const members = try self.gpa.dupe(Member, self.memberSlice(span));
                defer self.gpa.free(members);
                const fields = try self.gpa.alloc(FieldSpec, members.len);
                defer self.gpa.free(fields);
                for (members, fields) |m, *f| f.* = .{
                    .name = self.nameText(m.name),
                    .ty = try self.replaceRecursive(self.tySlice(m.tys)[0], name_id, with, memo),
                    .optional = m.optional,
                };
                break :blk try self.recordTy(fields);
            },
            .tag_union => |span| blk: {
                const members = try self.gpa.dupe(Member, self.memberSlice(span));
                defer self.gpa.free(members);
                const tags = try self.gpa.alloc(TagSpec, members.len);
                defer self.gpa.free(tags);
                var payloads: std.ArrayList([]TyId) = .empty;
                defer {
                    for (payloads.items) |pl| self.gpa.free(pl);
                    payloads.deinit(self.gpa);
                }
                for (members, tags) |m, *t| {
                    const pl = try self.gpa.dupe(TyId, self.tySlice(m.tys));
                    try payloads.append(self.gpa, pl);
                    for (pl) |*p| p.* = try self.replaceRecursive(p.*, name_id, with, memo);
                    t.* = .{ .name = self.nameText(m.name), .payload = pl };
                }
                break :blk try self.tagUnionTy(tags);
            },
        };
        try memo.put(self.gpa, ty, out);
        return out;
    }

    /// A `from`, `to` pair `widens` was asked of: two types together, not a
    /// dense index of either.
    const WidenPairKey = [2]TyId;

    /// Whether a value of `from` conforms to a slot of `to` (design.md "Row
    /// Coercion Primitive"). A tag keeps its name at the wider type. The
    /// reach is the root, every tag payload of a reached union, and the
    /// backing of a reached nominal. At a reached tag union every tag of
    /// `from` is in `to` with as many payloads. Every other position is the
    /// same type on both sides.
    pub fn widens(self: *Types, from: TyId, to: TyId) Allocator.Error!bool {
        var assumed: std.AutoHashMapUnmanaged(WidenPairKey, void) = .empty;
        defer assumed.deinit(self.gpa);
        return self.widensUnder(from, to, &assumed);
    }

    /// `widens`, where each pair in `assumed` holds already: a recursive
    /// type reaches its own pair again through its payloads.
    fn widensUnder(self: *Types, from: TyId, to: TyId, assumed: *std.AutoHashMapUnmanaged(WidenPairKey, void)) Allocator.Error!bool {
        if (from == to) return true;
        if ((try assumed.getOrPut(self.gpa, .{ from, to })).found_existing) return true;
        switch (self.get(from)) {
            .nominal => |source| {
                const target = switch (self.get(to)) {
                    .nominal => |target| target,
                    .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .func, .opaque_, .recursive => return false,
                };
                if (source.name != target.name) return false;
                return self.widensUnder(try self.unfold(from), try self.unfold(to), assumed);
            },
            .tag_union => |source_span| {
                const target_span = switch (self.get(to)) {
                    .tag_union => |target_span| target_span,
                    .bool_, .str, .int, .float, .dec, .record, .tuple, .list, .nominal, .func, .opaque_, .recursive => return false,
                };
                // `unfold` interns, which can move the member and type pools,
                // so the slices are copied before the payloads are compared.
                const sources = try self.gpa.dupe(Member, self.memberSlice(source_span));
                defer self.gpa.free(sources);
                const targets = try self.gpa.dupe(Member, self.memberSlice(target_span));
                defer self.gpa.free(targets);
                for (sources) |source| {
                    const target = for (targets) |candidate| {
                        if (candidate.name == source.name) break candidate;
                    } else return false;
                    if (source.tys.len != target.tys.len) return false;
                    const source_payload = try self.gpa.dupe(TyId, self.tySlice(source.tys));
                    defer self.gpa.free(source_payload);
                    const target_payload = try self.gpa.dupe(TyId, self.tySlice(target.tys));
                    defer self.gpa.free(target_payload);
                    for (source_payload, target_payload) |a, b| {
                        if (!try self.widensUnder(a, b, assumed)) return false;
                    }
                }
                return true;
            },
            .bool_, .str, .int, .float, .dec, .record, .tuple, .list, .func, .opaque_, .recursive => return false,
        }
    }

    /// Whether `ty` is a builtin integer type.
    pub fn isInt(self: *const Types, ty: TyId) bool {
        return switch (self.get(ty)) {
            .int => true,
            .bool_, .str, .float, .dec, .record, .tuple, .tag_union, .list, .nominal, .func, .opaque_, .recursive => false,
        };
    }

    /// Whether `ty` is a float type.
    pub fn isFloat(self: *const Types, ty: TyId) bool {
        return switch (self.get(ty)) {
            .float => true,
            .bool_, .str, .int, .dec, .record, .tuple, .tag_union, .list, .nominal, .func, .opaque_, .recursive => false,
        };
    }

    /// Whether `ty` is a record, tuple or tag union: the aggregates N14 counts.
    pub fn isAggregate(self: *const Types, ty: TyId) bool {
        return switch (self.get(ty)) {
            .record, .tuple, .tag_union => true,
            .bool_, .str, .int, .float, .dec, .list, .nominal, .func, .opaque_, .recursive => false,
        };
    }

    /// Whether N14 splits a value of `ty`: a record or tuple with at least one
    /// component, none of which a value may lack.
    pub fn isSplittable(self: *const Types, ty: TyId) bool {
        return switch (self.get(ty)) {
            .record => |span| blk: {
                const members = self.memberSlice(span);
                if (members.len == 0) break :blk false;
                for (members) |m| if (m.optional) break :blk false;
                break :blk true;
            },
            .tuple => |span| span.len > 0,
            .bool_, .str, .int, .float, .dec, .tag_union, .list, .nominal, .func, .opaque_, .recursive => false,
        };
    }

    /// How many components `ty` has, when N14 splits it.
    pub fn componentCount(self: *const Types, ty: TyId) u32 {
        return switch (self.get(ty)) {
            .record, .tuple => |span| span.len,
            .bool_, .str, .int, .float, .dec, .tag_union, .list, .nominal, .func, .opaque_, .recursive => 0,
        };
    }

    /// The type of component `i` of the record or tuple `ty`, in the type's order.
    pub fn componentTy(self: *const Types, ty: TyId, i: u32) TyId {
        return switch (self.get(ty)) {
            .record => |span| self.tySlice(self.memberSlice(span)[i].tys)[0],
            .tuple => |span| self.tySlice(span)[i],
            .bool_, .str, .int, .float, .dec, .tag_union, .list, .nominal, .func, .opaque_, .recursive => unreachable, // only a record or tuple has components
        };
    }

    /// The layers of records and tuples that N14 splits in `ty`, counted
    /// through the components it splits: a splittable record of splittable
    /// records counts one for each. Splitting a layer lowers the count by one.
    pub fn splitLayers(self: *const Types, ty: TyId) u32 {
        if (!self.isSplittable(ty)) return 0;
        var layers: u32 = 1;
        for (0..self.componentCount(ty)) |i| layers += self.splitLayers(self.componentTy(ty, @intCast(i)));
        return layers;
    }

    /// The position of the tag `name` among the members of the tag union `union_ty`,
    /// which are in name order. Null when the union has no such tag.
    pub fn memberIndex(self: *const Types, union_ty: TyId, name_id: NameId) ?u32 {
        const span = switch (self.get(union_ty)) {
            .tag_union => |span| span,
            .bool_, .str, .int, .float, .dec, .record, .tuple, .list, .nominal, .func, .opaque_, .recursive => return null,
        };
        for (self.memberSlice(span), 0..) |m, i| {
            if (m.name == name_id) return @intCast(i);
        }
        return null;
    }

    /// The number of arms a switch on a value of `ty` has, when the type fixes it.
    pub fn armCount(self: *const Types, ty: TyId) ?u32 {
        return switch (self.get(ty)) {
            .bool_ => 2,
            .tag_union => |span| span.len,
            .str, .int, .float, .dec, .record, .tuple, .list, .nominal, .func, .opaque_, .recursive => null,
        };
    }

    fn lookup(self: *Types, key: []const u32) ?TyId {
        const start: u32 = @intCast(self.key_words.items.len);
        self.key_words.appendSlice(self.gpa, key) catch return null;
        defer self.key_words.shrinkRetainingCapacity(start);
        return self.interned.getContext(.{ .start = start, .len = @intCast(key.len) }, .{ .words = &self.key_words });
    }

    fn intern(self: *Types, ty: Ty, key: []const u32) Allocator.Error!TyId {
        const start: u32 = @intCast(self.key_words.items.len);
        try self.key_words.appendSlice(self.gpa, key);
        const k: TyKey = .{ .start = start, .len = @intCast(key.len) };
        const gop = try self.interned.getOrPutContext(self.gpa, k, .{ .words = &self.key_words });
        if (gop.found_existing) {
            self.key_words.shrinkRetainingCapacity(start);
            return gop.value_ptr.*;
        }
        const id = TyId.of(@intCast(self.tys.items.len));
        try self.tys.append(self.gpa, ty);
        gop.value_ptr.* = id;
        return id;
    }

    fn addTyPool(self: *Types, items: []const TyId) Allocator.Error!ir.Span {
        const start: u32 = @intCast(self.ty_pool.items.len);
        try self.ty_pool.appendSlice(self.gpa, items);
        return .{ .start = start, .len = @intCast(items.len) };
    }

    fn addMembers(self: *Types, items: []const Member) Allocator.Error!ir.Span {
        const start: u32 = @intCast(self.members.items.len);
        try self.members.appendSlice(self.gpa, items);
        return .{ .start = start, .len = @intCast(items.len) };
    }
};

test "structurally equal types intern to one id" {
    var types = Types.init(std.testing.allocator);
    defer types.deinit();
    const i64_ty = try types.intTy(.i64);
    const bool_ty = try types.boolTy();
    const a = try types.recordTy(&.{ .{ .name = "y", .ty = bool_ty }, .{ .name = "x", .ty = i64_ty } });
    const b = try types.recordTy(&.{ .{ .name = "x", .ty = i64_ty }, .{ .name = "y", .ty = bool_ty } });
    try std.testing.expectEqual(a, b);
    try std.testing.expectEqual(i64_ty, try types.intTy(.i64));
    const fields = types.memberSlice(types.get(a).record);
    try std.testing.expectEqualStrings("x", types.nameText(fields[0].name));
    const u = try types.tagUnionTy(&.{ .{ .name = "B", .payload = &.{} }, .{ .name = "A", .payload = &.{i64_ty} } });
    try std.testing.expectEqual(@as(?u32, 2), types.armCount(u));
    try std.testing.expect(u != a);
}

test "unfolding a recursive nominal puts it where its backing refers back to it, and stops at a nested nominal of its name" {
    var types = Types.init(std.testing.allocator);
    defer types.deinit();
    const i64_ty = try types.intTy(.i64);
    // Tree := [Leaf(I64), Node(Tree, Tree)]
    const back = try types.recursiveTy("Tree");
    const backing = try types.tagUnionTy(&.{ .{ .name = "Leaf", .payload = &.{i64_ty} }, .{ .name = "Node", .payload = &.{ back, back } } });
    const tree = try types.nominalTy("Tree", backing);
    const unfolded = try types.unfold(tree);
    const node = types.memberSlice(types.get(unfolded).tag_union)[1];
    try std.testing.expectEqual(tree, types.tySlice(node.tys)[0]);
    try std.testing.expectEqual(tree, types.tySlice(node.tys)[1]);
    // A nominal of the same name inside the backing binds its own reference.
    const inner = try types.nominalTy("Tree", try types.listTy(back));
    const outer = try types.nominalTy("Tree", try types.tupleTy(&.{ back, inner }));
    const unfolded_outer = try types.unfold(outer);
    const parts = types.tySlice(types.get(unfolded_outer).tuple);
    try std.testing.expectEqual(outer, parts[0]);
    try std.testing.expectEqual(inner, parts[1]);
    // A type that does not refer back unfolds to its backing.
    const plain = try types.nominalTy("Box", i64_ty);
    try std.testing.expectEqual(i64_ty, try types.unfold(plain));
}
