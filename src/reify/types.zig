//! Interned types of the normal form (I2).
//!
//! Aliases are expanded before a type reaches this table, record fields and
//! tags are kept in name order, and nominals are named. Two structurally equal
//! types get one `TyId`, so type equality is integer equality. A recursive
//! type has many structures, one for each place its cycle can close, so a
//! type a node carries is the canonical one (`canonical`,
//! roc-reify-normal-form.md 2.1).

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
    /// Per type, whether a `recursive` occurs in it. A closed type without
    /// one is a finite tree, which is its own canonical spelling.
    has_recursive: std.ArrayList(bool) = .empty,
    /// `canonical` of a closed type, and each answer mapped to itself.
    canonical_of: collections.DenseMapUnmanaged(TyId, TyId) = .empty,
    /// `unfold` of a closed nominal.
    unfolded_of: collections.DenseMapUnmanaged(TyId, TyId) = .empty,

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
        self.has_recursive.deinit(self.gpa);
        self.canonical_of.deinit(self.gpa);
        self.unfolded_of.deinit(self.gpa);
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
        return self.recursiveNamed(try self.name(text));
    }

    fn recursiveNamed(self: *Types, n: NameId) Allocator.Error!TyId {
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
        return self.nominalNamed(try self.name(text), backing);
    }

    fn nominalNamed(self: *Types, n: NameId, backing: TyId) Allocator.Error!TyId {
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

    /// The canonical spelling of the closed type `ty`: the one `TyId` every
    /// spelling of its meaning gets (roc-reify-normal-form.md 2.1).
    ///
    /// A recursive type is a finite tree only through `recursive`, and one
    /// infinite type has many such trees: a cycle through two nominals can be
    /// closed at either of them, and unrolled any number of times. The
    /// canonical tree closes a nominal exactly where the nearest enclosing
    /// nominal of its name is the same type, and nowhere else.
    pub fn canonical(self: *Types, ty: TyId) Allocator.Error!TyId {
        if (!self.has_recursive.items[ty.index()]) return ty;
        if (self.canonical_of.get(ty)) |done| return done;
        var spelling = Spelling.init(self);
        defer spelling.deinit();
        const root = try spelling.graphOf(ty);
        try spelling.refine();
        const out = try spelling.spell(root, Spelling.no_chain);
        try self.canonical_of.put(self.gpa, ty, out);
        try self.canonical_of.put(self.gpa, out, out);
        return out;
    }

    /// The backing of the closed nominal `nominal`, spelled canonically from
    /// its own root: the type an `Unwrap` gives and a `Wrap` takes.
    ///
    /// The backing on its own leaves each `recursive` that refers to
    /// `nominal` dangling, and unfolding closes it. The result is spelled
    /// afresh, because the backing no longer sits inside `nominal`: a cycle
    /// through a second nominal closes at that one now (2.1).
    pub fn unfold(self: *Types, nominal: TyId) Allocator.Error!TyId {
        const n = self.get(nominal).nominal;
        if (!self.has_recursive.items[nominal.index()]) return n.backing;
        if (self.unfolded_of.get(nominal)) |done| return done;
        var spelling = Spelling.init(self);
        defer spelling.deinit();
        const root = try spelling.graphOf(nominal);
        try spelling.refine();
        const out = try spelling.spell(spelling.nodes.items[root].kids[0], Spelling.no_chain);
        try self.unfolded_of.put(self.gpa, nominal, out);
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
        try self.has_recursive.ensureUnusedCapacity(self.gpa, 1);
        try self.tys.append(self.gpa, ty);
        self.has_recursive.appendAssumeCapacity(self.holdsRecursive(ty));
        gop.value_ptr.* = id;
        return id;
    }

    // Whether a `recursive` occurs in `ty`, from what its parts hold.
    fn holdsRecursive(self: *const Types, ty: Ty) bool {
        const flags = self.has_recursive.items;
        return switch (ty) {
            .recursive => true,
            .bool_, .str, .int, .float, .dec => false,
            .list => |elem| flags[elem.index()],
            .nominal => |m| flags[m.backing.index()],
            .tuple => |span| self.anyRecursive(self.tySlice(span)),
            .opaque_ => |o| self.anyRecursive(self.tySlice(o.args)),
            .func => |f| flags[f.ret.index()] or self.anyRecursive(self.tySlice(f.params)),
            .record, .tag_union => |span| for (self.memberSlice(span)) |m| {
                if (self.anyRecursive(self.tySlice(m.tys))) break true;
            } else false,
        };
    }

    fn anyRecursive(self: *const Types, tys: []const TyId) bool {
        for (tys) |t| if (self.has_recursive.items[t.index()]) return true;
        return false;
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

/// One closed type as a finite graph, and its canonical spelling as a tree
/// (`Types.canonical`, `Types.unfold`).
///
/// | Step | What it does |
/// | --- | --- |
/// | `graphOf` | one node per position of the spelling; a `recursive` is an edge back to the nominal it names, not a node |
/// | `refine` | partition refinement: two nodes share a class exactly when they are the same infinite type |
/// | `spell` | the tree again, with a nominal closed where the nearest enclosing nominal of its name has its class |
const Spelling = struct {
    types: *Types,
    arena: std.heap.ArenaAllocator,
    nodes: std.ArrayList(Node) = .empty,
    /// The node of a part of the type: its `TyId`, then the node each name
    /// it leaves free refers to, in name order.
    node_of: std.StringHashMapUnmanaged(u32) = .empty,
    /// The `recursive` names each part leaves free, sorted.
    free_of: std.AutoHashMapUnmanaged(TyId, []const NameId) = .empty,
    /// The class of each node, after `refine`.
    class: []u32 = &.{},
    /// The nominals `spell` is inside, each a link to the one around it.
    chains: std.ArrayList(Chain) = .empty,
    chain_of: std.AutoHashMapUnmanaged(Chain, u32) = .empty,
    spelled: std.AutoHashMapUnmanaged([2]u32, TyId) = .empty,

    const Node = struct { ty: TyId, kids: []const u32 };
    const Chain = struct { outer: u32, name: NameId, class: u32 };
    const Binding = struct { name: NameId, node: u32 };
    const no_chain: u32 = std.math.maxInt(u32);

    fn init(types: *Types) Spelling {
        return .{ .types = types, .arena = std.heap.ArenaAllocator.init(types.gpa) };
    }

    fn deinit(self: *Spelling) void {
        self.arena.deinit();
    }

    fn alloc(self: *Spelling) Allocator {
        return self.arena.allocator();
    }

    /// The graph of the closed type `ty`; answers its root node.
    fn graphOf(self: *Spelling, ty: TyId) Allocator.Error!u32 {
        var env: std.ArrayList(Binding) = .empty;
        const root = try self.add(ty, &env);
        std.debug.assert(env.items.len == 0);
        return root;
    }

    fn add(self: *Spelling, ty: TyId, env: *std.ArrayList(Binding)) Allocator.Error!u32 {
        switch (self.types.get(ty)) {
            .recursive => |n| return bound(env.items, n),
            .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .nominal, .func, .opaque_ => {},
        }
        const free = try self.freeNames(ty);
        const key = try self.alloc().alloc(u32, 1 + free.len);
        key[0] = ty.index();
        for (free, key[1..]) |n, *k| k.* = bound(env.items, n);
        const gop = try self.node_of.getOrPut(self.alloc(), std.mem.sliceAsBytes(key));
        if (gop.found_existing) return gop.value_ptr.*;
        const at: u32 = @intCast(self.nodes.items.len);
        gop.value_ptr.* = at;
        try self.nodes.append(self.alloc(), .{ .ty = ty, .kids = &.{} });
        const parts = try self.partsOf(ty);
        const nominal = switch (self.types.get(ty)) {
            .nominal => |m| m.name,
            .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .func, .opaque_, .recursive => null,
        };
        if (nominal) |n| try env.append(self.alloc(), .{ .name = n, .node = at });
        const kids = try self.alloc().alloc(u32, parts.len);
        for (parts, kids) |part, *kid| kid.* = try self.add(part, env);
        if (nominal != null) _ = env.pop();
        self.nodes.items[at].kids = kids;
        return at;
    }

    // The node the nearest enclosing nominal named `n` stands at.
    fn bound(env: []const Binding, n: NameId) u32 {
        var i = env.len;
        while (i > 0) {
            i -= 1;
            if (env[i].name == n) return env[i].node;
        }
        unreachable; // a type spelled is closed, so each `recursive` names a nominal around it
    }

    // The parts of `ty`, in the order its constructor takes them.
    fn partsOf(self: *Spelling, ty: TyId) Allocator.Error![]const TyId {
        const types = self.types;
        var parts: std.ArrayList(TyId) = .empty;
        switch (types.get(ty)) {
            .bool_, .str, .int, .float, .dec, .recursive => {},
            .list => |elem| try parts.append(self.alloc(), elem),
            .nominal => |m| try parts.append(self.alloc(), m.backing),
            .tuple => |span| try parts.appendSlice(self.alloc(), types.tySlice(span)),
            .opaque_ => |o| try parts.appendSlice(self.alloc(), types.tySlice(o.args)),
            .func => |f| {
                try parts.appendSlice(self.alloc(), types.tySlice(f.params));
                try parts.append(self.alloc(), f.ret);
            },
            .record, .tag_union => |span| for (types.memberSlice(span)) |m| try parts.appendSlice(self.alloc(), types.tySlice(m.tys)),
        }
        return parts.items;
    }

    fn freeNames(self: *Spelling, ty: TyId) Allocator.Error![]const NameId {
        if (self.free_of.get(ty)) |done| return done;
        var names: std.ArrayList(NameId) = .empty;
        switch (self.types.get(ty)) {
            .recursive => |n| try names.append(self.alloc(), n),
            .bool_, .str, .int, .float, .dec, .record, .tuple, .tag_union, .list, .func, .opaque_ => {
                for (try self.partsOf(ty)) |part| try names.appendSlice(self.alloc(), try self.freeNames(part));
            },
            .nominal => |m| for (try self.freeNames(m.backing)) |n| {
                if (n != m.name) try names.append(self.alloc(), n);
            },
        }
        std.mem.sort(NameId, names.items, {}, struct {
            fn lt(_: void, a: NameId, b: NameId) bool {
                return a.index() < b.index();
            }
        }.lt);
        var kept: usize = 0;
        for (names.items) |n| {
            if (kept > 0 and names.items[kept - 1] == n) continue;
            names.items[kept] = n;
            kept += 1;
        }
        const free = names.items[0..kept];
        try self.free_of.put(self.alloc(), ty, free);
        return free;
    }

    /// Partition refinement (Moore): start from the constructor of each node,
    /// and split a class while its nodes have parts in different classes.
    fn refine(self: *Spelling) Allocator.Error!void {
        const count = self.nodes.items.len;
        var class = try self.alloc().alloc(u32, count);
        var words: std.ArrayList(u32) = .empty;
        var ids: std.StringHashMapUnmanaged(u32) = .empty;
        for (self.nodes.items, class) |nd, *c| {
            words.clearRetainingCapacity();
            try self.label(nd.ty, &words);
            c.* = try intern(self.alloc(), &ids, words.items);
        }
        var classes = ids.count();
        while (true) {
            const next = try self.alloc().alloc(u32, count);
            var next_ids: std.StringHashMapUnmanaged(u32) = .empty;
            for (self.nodes.items, next, 0..) |nd, *c, i| {
                words.clearRetainingCapacity();
                try words.append(self.alloc(), class[i]);
                for (nd.kids) |kid| try words.append(self.alloc(), class[kid]);
                c.* = try intern(self.alloc(), &next_ids, words.items);
            }
            // Each round refines the last, so an equal count is the same partition.
            if (next_ids.count() == classes) break;
            classes = next_ids.count();
            class = next;
        }
        self.class = class;
    }

    fn intern(arena: Allocator, ids: *std.StringHashMapUnmanaged(u32), words: []const u32) Allocator.Error!u32 {
        const gop = try ids.getOrPut(arena, std.mem.sliceAsBytes(words));
        if (!gop.found_existing) {
            gop.key_ptr.* = std.mem.sliceAsBytes(try arena.dupe(u32, words));
            gop.value_ptr.* = @intCast(ids.count() - 1);
        }
        return gop.value_ptr.*;
    }

    // What a node is apart from its parts.
    fn label(self: *Spelling, ty: TyId, words: *std.ArrayList(u32)) Allocator.Error!void {
        const types = self.types;
        const a = self.alloc();
        switch (types.get(ty)) {
            .bool_ => try words.append(a, 0),
            .str => try words.append(a, 1),
            .int => |i| try words.appendSlice(a, &.{ 2, @backingInt(i) }),
            .float => |f| try words.appendSlice(a, &.{ 3, @backingInt(f) }),
            .list => try words.append(a, 4),
            .tuple => |span| try words.appendSlice(a, &.{ 5, span.len }),
            .record => |span| {
                try words.appendSlice(a, &.{ 6, span.len });
                for (types.memberSlice(span)) |m| try words.appendSlice(a, &.{ m.name.index(), @intFromBool(m.optional) });
            },
            .tag_union => |span| {
                try words.appendSlice(a, &.{ 7, span.len });
                for (types.memberSlice(span)) |m| try words.appendSlice(a, &.{ m.name.index(), m.tys.len });
            },
            .nominal => |m| try words.appendSlice(a, &.{ 8, m.name.index() }),
            .func => |f| try words.appendSlice(a, &.{ 9, f.params.len }),
            .dec => try words.append(a, 10),
            .opaque_ => |o| try words.appendSlice(a, &.{ 11, o.name.index(), o.args.len }),
            .recursive => unreachable, // a `recursive` is an edge of the graph, never a node
        }
    }

    // The class of the nearest nominal named `n` in `chain`, if any.
    fn nearest(self: *const Spelling, chain: u32, n: NameId) ?u32 {
        var at = chain;
        while (at != no_chain) {
            const link = self.chains.items[at];
            if (link.name == n) return link.class;
            at = link.outer;
        }
        return null;
    }

    fn push(self: *Spelling, chain: u32, n: NameId, class: u32) Allocator.Error!u32 {
        const link: Chain = .{ .outer = chain, .name = n, .class = class };
        const gop = try self.chain_of.getOrPut(self.alloc(), link);
        if (!gop.found_existing) {
            gop.value_ptr.* = @intCast(self.chains.items.len);
            try self.chains.append(self.alloc(), link);
        }
        return gop.value_ptr.*;
    }

    /// The tree of `node`, inside the nominals of `chain`.
    fn spell(self: *Spelling, node: u32, chain: u32) Allocator.Error!TyId {
        if (self.spelled.get(.{ node, chain })) |done| return done;
        const types = self.types;
        const nd = self.nodes.items[node];
        const out: TyId = switch (types.get(nd.ty)) {
            .bool_, .str, .int, .float, .dec => nd.ty,
            .recursive => unreachable, // a `recursive` is an edge of the graph, never a node
            .nominal => |m| blk: {
                if (self.nearest(chain, m.name) == self.class[node]) break :blk try types.recursiveNamed(m.name);
                const backing = try self.spell(nd.kids[0], try self.push(chain, m.name, self.class[node]));
                break :blk try types.nominalNamed(m.name, backing);
            },
            .list => try types.listTy(try self.spell(nd.kids[0], chain)),
            .tuple => try types.tupleTy(try self.spellAll(nd.kids, chain)),
            .func => blk: {
                const parts = try self.spellAll(nd.kids, chain);
                break :blk try types.funcTy(parts[0 .. parts.len - 1], parts[parts.len - 1]);
            },
            .opaque_ => |o| try types.opaqueTy(types.nameText(o.name), try self.spellAll(nd.kids, chain)),
            .record => |span| blk: {
                const members = try self.alloc().dupe(Member, types.memberSlice(span));
                const parts = try self.spellAll(nd.kids, chain);
                const fields = try self.alloc().alloc(FieldSpec, members.len);
                for (members, parts, fields) |m, part, *f| f.* = .{ .name = types.nameText(m.name), .ty = part, .optional = m.optional };
                break :blk try types.recordTy(fields);
            },
            .tag_union => |span| blk: {
                const members = try self.alloc().dupe(Member, types.memberSlice(span));
                const parts = try self.spellAll(nd.kids, chain);
                const tags = try self.alloc().alloc(TagSpec, members.len);
                var next: usize = 0;
                for (members, tags) |m, *t| {
                    t.* = .{ .name = types.nameText(m.name), .payload = parts[next..][0..m.tys.len] };
                    next += m.tys.len;
                }
                break :blk try types.tagUnionTy(tags);
            },
        };
        try self.spelled.put(self.alloc(), .{ node, chain }, out);
        return out;
    }

    fn spellAll(self: *Spelling, kids: []const u32, chain: u32) Allocator.Error![]TyId {
        const parts = try self.alloc().alloc(TyId, kids.len);
        for (kids, parts) |kid, *part| part.* = try self.spell(kid, chain);
        return parts;
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

test "one recursive type has one spelling, wherever its cycle is closed" {
    var types = Types.init(std.testing.allocator);
    defer types.deinit();
    // Person := { links : List(Link) }, Link := { row : Person }
    const back_person = try types.recursiveTy("Person");
    const back_link = try types.recursiveTy("Link");
    // Spelled from `Person`, and from `Link`.
    const person = try types.nominalTy("Person", try types.recordTy(&.{.{ .name = "links", .ty = try types.listTy(try types.nominalTy("Link", try types.recordTy(&.{.{ .name = "row", .ty = back_person }}))) }}));
    const link = try types.nominalTy("Link", try types.recordTy(&.{.{ .name = "row", .ty = try types.nominalTy("Person", try types.recordTy(&.{.{ .name = "links", .ty = try types.listTy(back_link) }})) }}));
    // `Person` unrolled one more time: closed at `Link` rather than at itself.
    const person_backing = try types.recordTy(&.{.{ .name = "links", .ty = try types.listTy(link) }});
    const unrolled = try types.nominalTy("Person", person_backing);
    try std.testing.expect(unrolled != person);
    try std.testing.expectEqual(person, try types.canonical(person));
    try std.testing.expectEqual(person, try types.canonical(unrolled));
    try std.testing.expectEqual(link, try types.canonical(link));
    // An `Unwrap` of a `Link` holds the `Person` spelled at its own root.
    try std.testing.expectEqual(try types.recordTy(&.{.{ .name = "row", .ty = person }}), try types.unfold(link));
    try std.testing.expectEqual(person_backing, try types.unfold(person));
    try std.testing.expectEqual(person_backing, try types.unfold(unrolled));
}

test "a field reached through a second nominal of a cycle has the type spelled at its own root" {
    var types = Types.init(std.testing.allocator);
    defer types.deinit();
    const str = try types.strTy();
    // C := { name : Str, nick ?: Wrap(C) }, Wrap(a) := { items : List(a) }
    const c = try types.nominalTy("C", try types.recordTy(&.{
        .{ .name = "name", .ty = str },
        .{ .name = "nick", .ty = try types.nominalTy("Wrap", try types.recordTy(&.{.{ .name = "items", .ty = try types.listTy(try types.recursiveTy("C")) }})), .optional = true },
    }));
    const wrap_c = try types.nominalTy("Wrap", try types.recordTy(&.{.{ .name = "items", .ty = try types.listTy(try types.nominalTy("C", try types.recordTy(&.{
        .{ .name = "name", .ty = str },
        .{ .name = "nick", .ty = try types.recursiveTy("Wrap"), .optional = true },
    }))) }}));
    const backing = try types.unfold(c);
    const nick = types.memberSlice(types.get(backing).record)[1];
    try std.testing.expect(nick.optional);
    try std.testing.expectEqual(wrap_c, types.tySlice(nick.tys)[0]);
    // Self recursion alone, through `List` only, had one spelling already.
    const d = try types.nominalTy("D", try types.recordTy(&.{.{ .name = "nick", .ty = try types.listTy(try types.recursiveTy("D")), .optional = true }}));
    try std.testing.expectEqual(d, try types.canonical(d));
    try std.testing.expectEqual(try types.recordTy(&.{.{ .name = "nick", .ty = try types.listTy(d), .optional = true }}), try types.unfold(d));
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

test "a nominal inside another instance of its name expands again, and closes only under its own instance" {
    var types = Types.init(std.testing.allocator);
    defer types.deinit();
    // Wrap(a) := { items : List(a) }, A := { x : Wrap(B) }, B := { y : Wrap(A) }
    const wrapOf = struct {
        fn of(t: *Types, item: TyId) Allocator.Error!TyId {
            return t.nominalTy("Wrap", try t.recordTy(&.{.{ .name = "items", .ty = try t.listTy(item) }}));
        }
    }.of;
    const aOf = struct {
        fn of(t: *Types, x: TyId) Allocator.Error!TyId {
            return t.nominalTy("A", try t.recordTy(&.{.{ .name = "x", .ty = x }}));
        }
    }.of;
    const bOf = struct {
        fn of(t: *Types, y: TyId) Allocator.Error!TyId {
            return t.nominalTy("B", try t.recordTy(&.{.{ .name = "y", .ty = y }}));
        }
    }.of;
    // The T1 tree of `Wrap(A)`: the inner `Wrap(A)` sits under `Wrap(B)`, so
    // it expands, and its `A` closes at the `A` around it.
    const back_a = try types.recursiveTy("A");
    const wrap_a = try wrapOf(&types, try aOf(&types, try wrapOf(&types, try bOf(&types, try wrapOf(&types, back_a)))));
    try std.testing.expectEqual(wrap_a, try types.canonical(wrap_a));
    // The same type unrolled once more closes at its T1 tree.
    const unrolled = try wrapOf(&types, try aOf(&types, try wrapOf(&types, try bOf(&types, try wrapOf(&types, try aOf(&types, try wrapOf(&types, try bOf(&types, try wrapOf(&types, back_a)))))))));
    try std.testing.expect(unrolled != wrap_a);
    try std.testing.expectEqual(wrap_a, try types.canonical(unrolled));
    // `Recursive(Wrap)` under `Wrap(B)` is `Wrap(B)`, so this tree gives `B`
    // a field of `Wrap(B)`: another type.
    const misread = try wrapOf(&types, try aOf(&types, try wrapOf(&types, try bOf(&types, try types.recursiveTy("Wrap")))));
    try std.testing.expect(try types.canonical(misread) != wrap_a);
    // The backing of `Wrap(A)` holds `A` spelled from its own root, where
    // the `Wrap(A)` inside `B` closes at nothing and expands.
    const a = try aOf(&types, try wrapOf(&types, try bOf(&types, try wrapOf(&types, back_a))));
    try std.testing.expectEqual(a, try types.canonical(a));
    try std.testing.expectEqual(try types.recordTy(&.{.{ .name = "items", .ty = try types.listTy(a) }}), try types.unfold(wrap_a));
}
