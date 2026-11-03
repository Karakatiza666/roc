//! Step 2's enumeration (`roc-reify-rule-derivation.md` 3.2): the typed
//! terms of a signature, bottom-up by size, each built only from terms
//! already kept and kept only when no rule rewrites it. The enumeration
//! visits normal forms only.

const std = @import("std");
const reify = @import("reify");
const term = @import("term.zig");
const sig_mod = @import("sig.zig");

const Allocator = std.mem.Allocator;
const Term = term.Term;
const Sym = term.Sym;
const Sort = sig_mod.Sort;

/// A term of the enumeration.
pub const Entry = struct {
    t: Term,
    size: u32,
    sort: Sort,
};

/// One way to build a term: a symbol over arguments of these sorts. A
/// literal switch's key is this literal, placed after the scrutinee.
const Ctor = struct {
    sym: Sym,
    args: []const Sort,
    result: Sort,
    key: ?i64 = null,

    // The nodes the constructor adds besides its root and its arguments.
    fn extra(self: Ctor) u32 {
        return @intFromBool(self.key != null);
    }
};

fn ctors(arena: Allocator, sig: sig_mod.Signature) Allocator.Error![]Ctor {
    var out: std.ArrayList(Ctor) = .empty;
    const bool_sym: Sym = .{ .op = .prim, .owner = .{ .fixed = .bool_ } };
    const int_sym: Sym = .{ .op = .prim, .owner = .{ .fixed = .i64 } };
    for (sig.ops) |op| switch (op) {
        .not => try out.append(arena, .{ .sym = with(bool_sym, .not), .args = &.{.bool}, .result = .bool }),
        .and_ => try out.append(arena, .{ .sym = .{ .op = .and_ }, .args = &.{ .bool, .bool }, .result = .bool }),
        .or_ => try out.append(arena, .{ .sym = .{ .op = .or_ }, .args = &.{ .bool, .bool }, .result = .bool }),
        .is_eq => {
            try out.append(arena, .{ .sym = with(int_sym, .is_eq), .args = &.{ .i64, .i64 }, .result = .bool });
            try out.append(arena, .{ .sym = with(bool_sym, .is_eq), .args = &.{ .bool, .bool }, .result = .bool });
        },
        .is_lt, .is_lte, .is_gt, .is_gte => try out.append(arena, .{ .sym = with(int_sym, std.meta.stringToEnum(reify.prims.Method, @tagName(op)).?), .args = &.{ .i64, .i64 }, .result = .bool }),
        .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor => try out.append(arena, .{ .sym = with(int_sym, std.meta.stringToEnum(reify.prims.Method, @tagName(op)).?), .args = &.{ .i64, .i64 }, .result = .i64 }),
        .switch_bool, .switch_union => for (sig.sorts) |s| {
            const args = try arena.dupe(Sort, &.{ if (op == .switch_bool) .bool else .union_ab, s, s });
            try out.append(arena, .{ .sym = .{ .op = .switch_ }, .args = args, .result = s });
        },
        // One key per integer literal a chain builtin does not own.
        .switch_lit => for (sig.lits) |l| switch (l) {
            .bool => {},
            .int => |n| if (!sig.isChainLit(n)) for (sig.sorts) |s| {
                const args = try arena.dupe(Sort, &.{ .i64, s, s });
                try out.append(arena, .{ .sym = .{ .op = .switch_, .index = 1 }, .args = args, .result = s, .key = n });
            },
        },
        .tag => {
            try out.append(arena, .{ .sym = .{ .op = .tag, .index = 0 }, .args = &.{.i64}, .result = .union_ab });
            try out.append(arena, .{ .sym = .{ .op = .tag, .index = 1 }, .args = &.{}, .result = .union_ab });
        },
        .payload => try out.append(arena, .{ .sym = .{ .op = .payload, .index = 0 }, .args = &.{.union_ab}, .result = .i64 }),
        .record => try out.append(arena, .{ .sym = .{ .op = .record }, .args = &.{ .i64, .bool }, .result = .record_xy }),
        .field => {
            try out.append(arena, .{ .sym = .{ .op = .field, .index = 0 }, .args = &.{.record_xy}, .result = .i64 });
            try out.append(arena, .{ .sym = .{ .op = .field, .index = 1 }, .args = &.{.record_xy}, .result = .bool });
        },
        .tuple => try out.append(arena, .{ .sym = .{ .op = .tuple }, .args = &.{ .i64, .bool }, .result = .tuple_ib }),
        .index => {
            try out.append(arena, .{ .sym = .{ .op = .index, .index = 0 }, .args = &.{.tuple_ib}, .result = .i64 });
            try out.append(arena, .{ .sym = .{ .op = .index, .index = 1 }, .args = &.{.tuple_ib}, .result = .bool });
        },
        .wrap => try out.append(arena, .{ .sym = .{ .op = .wrap }, .args = &.{.i64}, .result = .nominal_i64 }),
        .unwrap => try out.append(arena, .{ .sym = .{ .op = .unwrap }, .args = &.{.nominal_i64}, .result = .i64 }),
        .concat, .len, .get => unreachable, // enumerated methods exclude concat, len and get
    };
    return out.toOwnedSlice(arena);
}

fn with(s: Sym, m: reify.prims.Method) Sym {
    var out = s;
    out.method = m;
    return out;
}

/// What the enumeration calls for every term it keeps, with the term built.
pub const Visitor = struct {
    ctx: *anyopaque,
    visit: *const fn (ctx: *anyopaque, entry: Entry, inst: *sig_mod.Instance) reify.eval.Error!void,
};

/// Every irreducible term of `sig` up to size `k`, by size, then in
/// constructor and argument order. `knocked_out` rows are off in the normalizer.
pub fn run(arena: Allocator, gpa: Allocator, sig: sig_mod.Signature, vars: sig_mod.Vars, k: u32, knocked_out: []const bool, visitor: Visitor) reify.eval.Error![]Entry {
    const cs = try ctors(arena, sig);
    const sort_count = @typeInfo(Sort).@"enum".field_names.len;
    // by_size[n][sort]: the kept terms of size n.
    const by_size = try arena.alloc([sort_count]std.ArrayList(Term), k + 1);
    for (by_size) |*row| row.* = @splat(.empty);
    var out: std.ArrayList(Entry) = .empty;
    var e: Enumerator = .{ .sig = sig, .arena = arena, .gpa = gpa, .vars = vars, .knocked_out = knocked_out, .visitor = visitor, .out = &out, .by_size = by_size };

    for (vars.sorts.items, 0..) |s, v| try e.consider(.{ .var_ = @intCast(v) }, 1, s);
    for (sig.lits) |l| switch (l) {
        .bool => |b| try e.consider(.{ .app = .{ .sym = .{ .op = .lit, .lit = b }, .args = &.{} } }, 1, .bool),
        .int => |n| try e.consider(.{ .app = .{ .sym = .{ .op = .lit, .int = n }, .args = &.{} } }, 1, .i64),
    };
    for (cs) |c| if (c.args.len == 0) try e.consider(.{ .app = .{ .sym = c.sym, .args = &.{} } }, 1, c.result);
    var n: u32 = 2;
    while (n <= k) : (n += 1) {
        for (cs) |c| {
            if (c.args.len == 0 or c.args.len + c.extra() > n - 1) continue;
            const args = try arena.alloc(Term, c.args.len);
            try e.fill(c, args, 0, n - 1 - c.extra(), n);
        }
    }
    return out.toOwnedSlice(arena);
}

// A payload read of a member its union can never be is a compiler bug in a
// well-formed body (`eval.zig`), so no body contains one. Such a term is ⊥
// on every input and would join every term around it into one group.
fn wellFormed(vars: sig_mod.Vars, sym: Sym, args: []const Term) bool {
    if (sym.op != .payload) return true;
    return membersOf(vars, args[0], &.{}) & (@as(u8, 1) << @intCast(sym.index.?)) != 0;
}

/// A union term a dominating switch decided to be one member.
const Fact = struct { scrutinee: Term, member: u8 };

// The members a union term can be, one bit each: one a dominating switch
// decided, else a variable any, a tag its own, a switch those of the arms
// it can run, each arm of a switch on a union knowing the scrutinee is its member.
fn membersOf(vars: sig_mod.Vars, t: Term, facts: []const Fact) u8 {
    for (facts) |f| if (f.scrutinee.eql(t)) return @as(u8, 1) << @intCast(f.member);
    const x = switch (t) {
        .var_ => return 0xff,
        .app => |x| x,
    };
    return switch (x.sym.op) {
        .tag => @as(u8, 1) << @intCast(x.sym.index.?),
        .switch_ => blk: {
            const on_union = sig_mod.sortOf(vars, x.args[0]) == .union_ab;
            // Only the arms of members the scrutinee can be run.
            const reachable: u8 = if (on_union) membersOf(vars, x.args[0], facts) else 0xff;
            var buf: [16]Fact = undefined;
            @memcpy(buf[0..facts.len], facts);
            var out: u8 = 0;
            for (x.args[1 + (term.litKeys(x) orelse 0) ..], 0..) |arm, key| {
                if (reachable & (@as(u8, 1) << @intCast(key)) == 0) continue;
                buf[facts.len] = .{ .scrutinee = x.args[0], .member = @intCast(key) };
                out |= membersOf(vars, arm, buf[0 .. facts.len + @intFromBool(on_union)]);
            }
            break :blk out;
        },
        .lit, .crash, .derived, .record, .tuple, .list, .wrap, .closure, .field, .index, .payload, .elem, .opt_field, .unwrap, .prim, .call, .and_, .or_, .for_range, .for_list, .loop, .lambda, .apply => unreachable, // signature terms are built only from the enumerated symbols
    };
}

// Whether a term of `sym` over `args` states only laws the signature's
// chains are in scope for (`Signature.chains`, `Signature.chain_lits`).
fn inScope(sig: sig_mod.Signature, sym: Sym, args: []const Term) bool {
    const own: ?reify.prims.Method = if (sym.op == .prim and sig.isChain(sym.method.?)) sym.method.? else null;
    for (args) |a| {
        const chain_lit = a == .app and a.app.sym.op == .lit and a.app.sym.int != null and sig.isChainLit(a.app.sym.int.?);
        if (chain_lit and own == null) return false;
        const inner: ?reify.prims.Method = switch (a) {
            .var_ => null,
            .app => |x| if (x.sym.op == .prim and sig.isChain(x.sym.method.?)) x.sym.method.? else null,
        };
        if (own) |m| {
            const operand_ok = switch (a) {
                .var_ => true,
                .app => |x| x.sym.op == .lit or inner == m,
            };
            if (!operand_ok) return false;
        } else if (inner != null and sym.op == .prim) return false;
    }
    return true;
}

const Enumerator = struct {
    sig: sig_mod.Signature,
    arena: Allocator,
    gpa: Allocator,
    vars: sig_mod.Vars,
    knocked_out: []const bool,
    visitor: Visitor,
    out: *std.ArrayList(Entry),
    by_size: [][@typeInfo(Sort).@"enum".field_names.len]std.ArrayList(Term),

    // Choose argument `i` onward with `left` nodes to share among them.
    fn fill(self: *Enumerator, c: Ctor, args: []Term, i: usize, left: u32, size: u32) reify.eval.Error!void {
        if (i == args.len) {
            if (left != 0 or !wellFormed(self.vars, c.sym, args) or !inScope(self.sig, c.sym, args)) return;
            const built = if (c.key) |k|
                try std.mem.concat(self.arena, Term, &.{ args[0..1], &.{.{ .app = .{ .sym = .{ .op = .lit, .int = k }, .args = &.{} } }}, args[1..] })
            else
                try self.arena.dupe(Term, args);
            try self.consider(.{ .app = .{ .sym = c.sym, .args = built } }, size, c.result);
            return;
        }
        const rest: u32 = @intCast(args.len - i - 1);
        if (left < rest + 1) return;
        var part: u32 = 1;
        while (part <= left - rest) : (part += 1) {
            for (self.by_size[part][@backingInt(c.args[i])].items) |a| {
                args[i] = a;
                try self.fill(c, args, i + 1, left - part, size);
            }
        }
    }

    fn consider(self: *Enumerator, t: Term, size: u32, sort: Sort) reify.eval.Error!void {
        var inst: sig_mod.Instance = undefined;
        try inst.init(self.gpa, self.vars, t, .i64, true, self.knocked_out);
        defer inst.deinit();
        if (inst.fired() != 0) return;
        const entry: Entry = .{ .t = t, .size = size, .sort = sort };
        try self.by_size[size][@backingInt(sort)].append(self.arena, t);
        try self.out.append(self.arena, entry);
        try self.visitor.visit(self.visitor.ctx, entry, &inst);
    }
};

const testing = std.testing;

test "the enumeration keeps well-formed normal forms only" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const s1 = sig_mod.find("S1").?;
    var vars = try sig_mod.Vars.base(testing.allocator, s1);
    defer vars.deinit(testing.allocator);
    const none: [reify.rules.count]bool = @splat(false);
    const Count = struct {
        n: usize = 0,
        fn visit(ctx: *anyopaque, _: Entry, _: *sig_mod.Instance) reify.eval.Error!void {
            const self: *@This() = @ptrCast(@alignCast(ctx));
            self.n += 1;
        }
    };
    var count: Count = .{};
    const entries = try run(arena.allocator(), testing.allocator, s1, vars, 3, &none, .{ .ctx = &count, .visit = Count.visit });
    try testing.expectEqual(entries.len, count.n);
    var saw_not_x0 = false;
    for (entries) |e| {
        var buf: std.Io.Writer.Allocating = .init(arena.allocator());
        try term.write(&buf.writer, e.t);
        // not(not(x)) is a redex of N13h, so size 3 has no double negation.
        try testing.expect(!std.mem.eql(u8, buf.written(), "Bool.not(Bool.not(x0))"));
        if (std.mem.eql(u8, buf.written(), "Bool.not(x0)")) saw_not_x0 = true;
        try testing.expect(!std.mem.eql(u8, buf.written(), "payload#0(tag#1())"));
    }
    try testing.expect(saw_not_x0);
}

test "a chain builtin reads only variables, literals and itself, and only itself or a non-builtin reads it" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const s2 = sig_mod.find("S2").?;
    for ([_]struct { []const u8, bool }{
        .{ "Num.I64.plus_wrap(Num.I64.plus_wrap(x2, 1), x3)", true },
        .{ "Num.I64.plus_wrap(Num.I64.bitwise_xor(x2, 1), x3)", false },
        .{ "Num.I64.plus_wrap(Num.I64.plus(x2, 1), x3)", false },
        .{ "Num.I64.plus(Num.I64.plus_wrap(x2, 1), x3)", false },
        .{ "Num.I64.is_eq(Num.I64.bitwise_and(x2, x3), 0)", false },
        .{ "switch_(x0, Num.I64.times(x2, x3), x2)", true },
        .{ "record(Num.I64.div_trunc(x2, x3), x0)", true },
        .{ "Num.I64.plus(field#0(x6), x3)", true },
        // -1 stands for all ones, which only a chain reads.
        .{ "Num.I64.bitwise_and(x2, -1)", true },
        .{ "Num.I64.times(-1, x2)", true },
        .{ "Num.I64.minus(-1, x2)", false },
        .{ "Num.I64.is_eq(x2, -1)", false },
        .{ "switch_(x0, -1, x2)", false },
    }) |c| {
        const t = (try term.parse(a, c[0])).app;
        try testing.expectEqual(c[1], inScope(s2, t.sym, t.args));
    }
    // S1 has no chains, so every term is in scope.
    const t = (try term.parse(a, "Num.I64.plus(Num.I64.plus(x2, 1), x3)")).app;
    try testing.expect(inScope(sig_mod.find("S1").?, t.sym, t.args));
}

test "a payload read is well formed when its union can be the member it reads" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const vars = try sig_mod.Vars.base(a, sig_mod.find("S1").?);
    for ([_]struct { []const u8, bool }{
        .{ "payload#0(x4)", true },
        .{ "payload#0(switch_(x0, tag#0(x2), tag#1()))", true },
        .{ "payload#0(tag#1())", false },
        .{ "payload#0(switch_(x0, tag#1(), tag#1()))", false },
        // In its `B` arm the switch decided `x4` is `B`.
        .{ "payload#0(switch_(x4, tag#1(), x4))", false },
        .{ "payload#0(switch_(x4, x4, tag#1()))", true },
        // A switch on `B` runs only its `B` arm.
        .{ "payload#0(switch_(tag#1(), x4, tag#1()))", false },
    }) |c| {
        const t = (try term.parse(a, c[0])).app;
        try testing.expectEqual(c[1], wellFormed(vars, t.sym, t.args));
    }
}
