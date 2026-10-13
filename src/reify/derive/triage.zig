//! Triage (`roc-reify-rule-derivation.md` 3.5 and 3.6): the ledger at run
//! time, the search that drops a pair equal modulo the ledger's equations,
//! and the three commands that write the table and the ledger.

const std = @import("std");
const reify = @import("reify");
const term = @import("term.zig");
const generalize = @import("generalize.zig");

const Allocator = std.mem.Allocator;
const Term = term.Term;
const Ledger = reify.ledger.Ledger;
const Entry = reify.ledger.Entry;

/// Where the triage commands write the ledger, relative to the repository root.
pub const ledger_path = "src/reify/rules/ledger.zon";
/// Where `--admit` writes a row, relative to the repository root.
pub const table_path = "src/reify/rules/table.zig";

/// An equation of the ledger, parsed.
pub const Equation = struct {
    lhs: Term,
    rhs: Term,
    /// Whether a step by the equation is normalized after. A rejected entry
    /// relates normal forms that deliberately differ, so its step must land
    /// on a normal form: where the table rewrites the result, the table
    /// misses a row for the other side, such as `plus(x, 0) = x` beside
    /// `plus(0, x) = x` under the rejected commutativity of `plus`. An open
    /// entry stands for an algorithm still to come, which normalizes.
    normalize: bool,
    /// The conditions a step checks on the match; a ledger entry has none.
    conds: []const generalize.Cond = &.{},
};

/// The equations of the rejected and open entries from `sources`. A
/// signature's entries name its sorts' members, such as `tag#1` for `B`, so
/// they do not apply to step 1's pattern terms.
pub fn equations(arena: Allocator, ledger: Ledger, sources: []const []const u8) term.ParseError![]const Equation {
    var out: std.ArrayList(Equation) = .empty;
    for ([_][]const Entry{ ledger.rejected, ledger.open }, [_]bool{ false, true }) |list, normalize| for (list) |e| {
        for (sources) |src| {
            if (std.mem.eql(u8, src, e.source)) break;
        } else continue;
        try out.append(arena, .{ .lhs = try term.parse(arena, e.lhs), .rhs = try term.parse(arena, e.rhs), .normalize = normalize });
    };
    return out.toOwnedSlice(arena);
}

/// Normalizes a term of one source.
pub const Normalizer = struct {
    ctx: *anyopaque,
    /// The normal form of `t`, or null when `t` is not well sorted in the
    /// source. An equation side that is a variable matches a subterm of any
    /// sort, so a step can put the other side where its sort does not fit,
    /// such as `or_(x, x)` for a union `x` by `or_(x0, x0) = x0`.
    run: *const fn (ctx: *anyopaque, arena: Allocator, t: Term) Allocator.Error!?Term,
};

const Match = struct {
    map: std.ArrayList(?Term) = .empty,
    owners: [term.owner_bound]?reify.prims.Owner = @splat(null),

    fn bind(self: *Match, arena: Allocator, v: term.Var, t: Term) Allocator.Error!bool {
        while (self.map.items.len <= v) try self.map.append(arena, null);
        if (self.map.items[v]) |b| return b.eql(t);
        self.map.items[v] = t;
        return true;
    }
};

// One-way matching of an equation side against a term.
fn match(arena: Allocator, m: *Match, pat: Term, t: Term) Allocator.Error!bool {
    const p = switch (pat) {
        .var_ => |v| return m.bind(arena, v, t),
        .app => |p| p,
    };
    const x = switch (t) {
        .var_ => return false,
        .app => |x| x,
    };
    if (p.sym.op != x.sym.op or p.sym.method != x.sym.method or p.sym.lit != x.sym.lit or p.sym.int != x.sym.int or p.sym.index != x.sym.index) return false;
    if (p.sym.owner) |po| {
        const xo = x.sym.owner orelse return false;
        const concrete = switch (xo) {
            .fixed => |o| o,
            .bind => return false,
        };
        switch (po) {
            .fixed => |o| if (o != concrete) return false,
            .bind => |k| {
                if (m.owners[k]) |b| {
                    if (b != concrete) return false;
                } else m.owners[k] = concrete;
            },
        }
    }
    if (p.args.len != x.args.len) return false;
    for (p.args, x.args) |a, b| if (!try match(arena, m, a, b)) return false;
    return true;
}

// `t` with the match applied; null when `t` reads a variable the match did not bind.
fn instantiate(arena: Allocator, m: *const Match, t: Term) Allocator.Error!?Term {
    const x = switch (t) {
        .var_ => |v| return if (v < m.map.items.len) m.map.items[v] else null,
        .app => |x| x,
    };
    var sym = x.sym;
    if (sym.owner) |o| switch (o) {
        .bind => |k| sym.owner = .{ .fixed = m.owners[k] orelse return null },
        .fixed => {},
    };
    const args = try arena.alloc(Term, x.args.len);
    for (x.args, args) |a, *o| o.* = (try instantiate(arena, m, a)) orelse return null;
    return .{ .app = .{ .sym = sym, .args = args } };
}

fn condsHold(m: *const Match, conds: []const generalize.Cond) bool {
    for (conds) |c| {
        const holds = switch (c) {
            .int_owner => if (m.owners[0]) |o| o.int() != null else false,
            // A variable the matched side does not read leaves the step unbuilt.
            .is_lit, .nonzero_lit, .speculatable => |v| if (boundTo(m, v)) |t| switch (c) {
                .is_lit => isLit(t),
                .nonzero_lit => isLit(t) and (t.app.sym.int orelse 0) != 0,
                .speculatable => speculatable(t),
                .int_owner => unreachable,
            } else false,
        };
        if (!holds) return false;
    }
    return true;
}

fn boundTo(m: *const Match, v: term.Var) ?Term {
    return if (v < m.map.items.len) m.map.items[v] else null;
}

fn isLit(t: Term) bool {
    return t == .app and t.app.sym.op == .lit;
}

// Whether `t` never crashes, as the builder's speculatable flag has it: a
// variable is assumed speculatable, and only a builtin can crash in a signature term.
fn speculatable(t: Term) bool {
    const x = switch (t) {
        .var_ => return true,
        .app => |x| x,
    };
    if (x.sym.op == .prim) {
        const owner = switch (x.sym.owner.?) {
            .fixed => |o| o,
            .bind => unreachable,
        };
        if (!reify.prims.get(reify.prims.find(owner, x.sym.method.?).?).speculatable) return false;
    }
    for (x.args) |a| if (!speculatable(a)) return false;
    return true;
}

// The subterm of `t` at `path`, or null where `t` has no such position.
fn subterm(t: Term, path: []const u8) ?Term {
    var cur = t;
    for (path) |i| {
        const x = switch (cur) {
            .var_ => return null,
            .app => |x| x,
        };
        if (i >= x.args.len) return null;
        cur = x.args[i];
    }
    return cur;
}

fn positions(arena: Allocator, t: Term, prefix: []const u8, out: *std.ArrayList([]const u8)) Allocator.Error!void {
    const x = switch (t) {
        .var_ => return,
        .app => |x| x,
    };
    try out.append(arena, prefix);
    for (x.args, 0..) |a, i| {
        const p = try arena.alloc(u8, prefix.len + 1);
        @memcpy(p[0..prefix.len], prefix);
        p[prefix.len] = @intCast(i);
        try positions(arena, a, p, out);
    }
}

/// Whether the normal forms `a` and `b` are equal modulo `eqs`: the terms
/// one ledger step in either direction reaches from `a`, each normalized
/// (or, for a rejected entry, required to be normal already),
/// searched to `depth` steps and to a size bound, which keeps the search
/// finite. The search runs from each side, because normalizing after a step
/// cannot undo a rewrite, so a step can apply to one side and not the other.
pub fn equalModulo(arena: Allocator, a: Term, b: Term, eqs: []const Equation, norm: Normalizer, depth: u32) Allocator.Error!bool {
    if (a.eql(b)) return true;
    if (eqs.len == 0) return false;
    return try reaches(arena, a, b, eqs, norm, depth) or try reaches(arena, b, a, eqs, norm, depth);
}

fn reaches(arena: Allocator, a: Term, b: Term, eqs: []const Equation, norm: Normalizer, depth: u32) Allocator.Error!bool {
    const bound = @max(generalize.size(a), generalize.size(b)) + 3;
    var frontier: std.ArrayList(Term) = .empty;
    var seen: std.ArrayList(Term) = .empty;
    try frontier.append(arena, a);
    try seen.append(arena, a);
    var step: u32 = 0;
    while (step < depth and frontier.items.len > 0) : (step += 1) {
        var next: std.ArrayList(Term) = .empty;
        for (frontier.items) |t| {
            var paths: std.ArrayList([]const u8) = .empty;
            try positions(arena, t, &.{}, &paths);
            for (paths.items) |path| for (eqs) |eq| for ([2][2]Term{ .{ eq.lhs, eq.rhs }, .{ eq.rhs, eq.lhs } }) |dir| {
                var m: Match = .{};
                if (!try match(arena, &m, dir[0], term.at(t, path))) continue;
                const with = (try instantiate(arena, &m, dir[1])) orelse blk: {
                    // A variable only the target side reads, as in
                    // `div_trunc(x0, 0) = div_trunc(x1, 0)`, takes the goal's subterm there.
                    const goal = subterm(b, path) orelse continue;
                    if (!try match(arena, &m, dir[1], goal)) continue;
                    break :blk (try instantiate(arena, &m, dir[1])).?;
                };
                if (!condsHold(&m, eq.conds)) continue;
                const replaced = try term.replaceAt(arena, t, path, with);
                const n = (try norm.run(norm.ctx, arena, replaced)) orelse continue;
                if (!eq.normalize and !n.eql(replaced)) continue;
                if (n.eql(b)) return true;
                if (generalize.size(n) > bound) continue;
                for (seen.items) |s| {
                    if (s.eql(n)) break;
                } else {
                    try seen.append(arena, n);
                    try next.append(arena, n);
                }
            };
        }
        frontier = next;
    }
    return false;
}

/// What reading and writing the tool's files can fail with.
pub const FileError = std.Io.Dir.ReadFileAllocError || std.Io.Dir.WriteFileError || std.Io.Writer.Error || error{ ParseZon, TableNotFound };

/// Parse ZON `text` into the arena.
fn parseZon(comptime T: type, arena: Allocator, text: [:0]const u8) error{ OutOfMemory, ParseZon }!T {
    var diagnostics: std.zon.parse.Diagnostics = .{ .errors = &.{} };
    return std.zon.parse.fromSlice(T, .{ .gpa = arena, .arena = arena, .source = text, .diagnostics = &diagnostics });
}

/// Read the ledger from `ledger_path`.
pub fn load(arena: Allocator, io: std.Io) FileError!Ledger {
    const text = try std.Io.Dir.cwd().readFileAllocOptions(io, ledger_path, arena, .limited(1 << 24), .of(u8), 0);
    return parseZon(Ledger, arena, text);
}

/// Write `ledger` to `ledger_path`.
pub fn save(arena: Allocator, io: std.Io, ledger: Ledger) FileError!void {
    var out: std.Io.Writer.Allocating = .init(arena);
    try out.writer.writeAll("// Written by `zig build reify-rules -- --admit|--ledger|--file`; see ledger.zig.\n");
    try std.zon.stringify.serialize(ledger, .{}, &out.writer);
    try out.writer.writeAll("\n");
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = ledger_path, .data = out.written() });
}

/// A list of the ledger that takes entries.
pub const List = enum { rejected, open };

/// `ledger` with `entry` appended to its rejected or open list.
pub fn withEntry(arena: Allocator, ledger: Ledger, list: List, entry: Entry) Allocator.Error!Ledger {
    var out = ledger;
    switch (list) {
        .rejected => out.rejected = try std.mem.concat(arena, Entry, &.{ ledger.rejected, &.{entry} }),
        .open => out.open = try std.mem.concat(arena, Entry, &.{ ledger.open, &.{entry} }),
    }
    return out;
}

/// Insert `row` as the last row of the table in `table_path`.
pub fn admitRow(arena: Allocator, io: std.Io, row: []const u8) FileError!void {
    const text = try std.Io.Dir.cwd().readFileAlloc(io, table_path, arena, .limited(1 << 24));
    const start = std.mem.find(u8, text, "pub const rules = [_]Rule{") orelse return error.TableNotFound;
    const close = std.mem.findPos(u8, text, start, "\n};\n") orelse return error.TableNotFound;
    const out = try std.mem.concat(arena, u8, &.{ text[0 .. close + 1], row, text[close + 1 ..] });
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = table_path, .data = out });
}

/// Where `--admit` records the witness each admitted row's tests build.
pub const derived_path = "src/reify/derive/derived.zon";

/// The witness of one admitted row (`derived_test.zig`).
pub const DerivedTest = struct {
    step: []const u8,
    signature: []const u8,
    /// A term the row rewrites, over the signature's base variables.
    lhs: []const u8,
    /// A term with the same normal form.
    rhs: []const u8,
};

/// Append `t` to `derived_path`.
pub fn addDerivedTest(arena: Allocator, io: std.Io, t: DerivedTest) FileError!void {
    const source = try std.Io.Dir.cwd().readFileAllocOptions(io, derived_path, arena, .limited(1 << 24), .of(u8), 0);
    const old = try parseZon([]const DerivedTest, arena, source);
    var out: std.Io.Writer.Allocating = .init(arena);
    try out.writer.writeAll("// The witnesses of admitted rows, appended by `--admit`; see derived_test.zig.\n");
    try std.zon.stringify.serialize(try std.mem.concat(arena, DerivedTest, &.{ old, &.{t} }), .{}, &out.writer);
    try out.writer.writeAll("\n");
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = derived_path, .data = out.written() });
}

/// Where counterexamples accumulate (3.3).
pub const inputs_path = "src/reify/derive/inputs.zon";

/// One assignment of `inputs.zon`: a value per base variable of the signature.
pub const Input = struct {
    signature: []const u8,
    values: []const []const u8,
};

/// Read `inputs_path`.
pub fn loadInputs(arena: Allocator, io: std.Io) FileError![]const Input {
    const text = try std.Io.Dir.cwd().readFileAllocOptions(io, inputs_path, arena, .limited(1 << 24), .of(u8), 0);
    return parseZon([]const Input, arena, text);
}

/// Write `inputs` to `inputs_path`.
pub fn saveInputs(arena: Allocator, io: std.Io, inputs: []const Input) FileError!void {
    var out: std.Io.Writer.Allocating = .init(arena);
    try out.writer.writeAll("// Counterexamples step 3 found, appended by `zig build reify-rules`; see fingerprint.zig.\n");
    try std.zon.stringify.serialize(inputs, .{}, &out.writer);
    try out.writer.writeAll("\n");
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = inputs_path, .data = out.written() });
}

/// The two sides of `eq` as text, with variables renamed in order of first occurrence.
pub fn sides(arena: Allocator, lhs: Term, rhs: Term) Allocator.Error![2][]const u8 {
    var order: std.ArrayList(term.Var) = .empty;
    try occurrences(arena, lhs, &order);
    try occurrences(arena, rhs, &order);
    var out: [2][]const u8 = undefined;
    for (&out, [2]Term{ lhs, rhs }) |*o, t| {
        var w: std.Io.Writer.Allocating = .init(arena);
        term.writeRenamed(&w.writer, t, order.items) catch return error.OutOfMemory;
        o.* = w.written();
    }
    return out;
}

fn occurrences(arena: Allocator, t: Term, order: *std.ArrayList(term.Var)) Allocator.Error!void {
    switch (t) {
        .var_ => |v| if (std.mem.findScalar(term.Var, order.items, v) == null) try order.append(arena, v),
        .app => |x| for (x.args) |a| try occurrences(arena, a, order),
    }
}

/// The text of a term.
pub fn textOf(arena: Allocator, t: Term) Allocator.Error![]const u8 {
    var w: std.Io.Writer.Allocating = .init(arena);
    term.write(&w.writer, t) catch return error.OutOfMemory;
    return w.written();
}

const testing = std.testing;

test "a commutativity pair is equal modulo the ledger's commutativity equation, at any position" {
    // The normal form keeps operand order (normal-form 7.2), so the
    // equation is the ledger's to state.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const eqs = [_]Equation{.{ .lhs = try term.parse(a, "and_(x0, x1)"), .rhs = try term.parse(a, "and_(x1, x0)"), .normalize = false }};
    var dummy: u8 = 0;
    const norm: Normalizer = .{ .ctx = &dummy, .run = tableNorm };
    const l = try term.parse(a, "switch_(and_(x0, x66), x130, x131)");
    const r = try term.parse(a, "switch_(and_(x66, x0), x130, x131)");
    try testing.expect(try equalModulo(a, l, r, &eqs, norm, 2));
    try testing.expect(!try equalModulo(a, l, r, &.{}, norm, 2));
}

test "a step binds a variable only its target side reads to the goal's subterm there" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const eqs = [_]Equation{.{ .lhs = try term.parse(a, "o0.div_trunc(x0, 0)"), .rhs = try term.parse(a, "o0.div_trunc(x1, 0)"), .normalize = false }};
    const Same = struct {
        fn run(_: *anyopaque, _: Allocator, t: Term) Allocator.Error!?Term {
            return t;
        }
    };
    var dummy: u8 = 0;
    const norm: Normalizer = .{ .ctx = &dummy, .run = Same.run };
    const l = try term.parse(a, "Num.I64.plus(Num.I64.div_trunc(x2, 0), x3)");
    try testing.expect(try equalModulo(a, l, try term.parse(a, "Num.I64.plus(Num.I64.div_trunc(Num.I64.times(x2, x3), 0), x3)"), &eqs, norm, 1));
    try testing.expect(!try equalModulo(a, l, try term.parse(a, "Num.I64.plus(Num.I64.div_trunc(x2, 1), x3)"), &eqs, norm, 1));
}

test "a step that applies to one side only is found from that side" {
    // The equation's right side drops `x1`, so it rewrites only left to
    // right, and only `and_(x2, x3)` has a position it matches.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const eqs = [_]Equation{.{ .lhs = try term.parse(a, "and_(x0, x1)"), .rhs = try term.parse(a, "x0"), .normalize = true }};
    var dummy: u8 = 0;
    const norm: Normalizer = .{ .ctx = &dummy, .run = tableNorm };
    try testing.expect(try equalModulo(a, try term.parse(a, "x2"), try term.parse(a, "and_(x2, x3)"), &eqs, norm, 2));
}

test "a rejected step must land on a normal form" {
    // T1.9 folds `plus(0, x)` only, so `plus(x, 0)` reaches `x` through the
    // rejected commutativity only by normalizing after it.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var dummy: u8 = 0;
    const norm: Normalizer = .{ .ctx = &dummy, .run = tableNorm };
    const l = try term.parse(a, "Num.I64.plus(x2, 0)");
    const r = try term.parse(a, "x2");
    const lhs = try term.parse(a, "o0.plus(x0, x1)");
    const rhs = try term.parse(a, "o0.plus(x1, x0)");
    try testing.expect(!try equalModulo(a, l, r, &.{.{ .lhs = lhs, .rhs = rhs, .normalize = false }}, norm, 2));
    try testing.expect(try equalModulo(a, l, r, &.{.{ .lhs = lhs, .rhs = rhs, .normalize = true }}, norm, 2));
}

test "a step that puts a side where its sort does not fit is not taken" {
    // `x0 -> or_(x0, x0)` matches the union `tag#1()`, and `payload#0(or_(tag#1(), tag#1()))` does not build.
    const sig_mod = @import("sig.zig");
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const Norm = struct {
        vars: sig_mod.Vars,
        fn run(ctx: *anyopaque, ar: Allocator, t: Term) Allocator.Error!?Term {
            const self: *@This() = @ptrCast(@alignCast(ctx));
            const none: [reify.rules.count]bool = @splat(false);
            return sig_mod.normalizeSorted(ar, testing.allocator, self.vars, t, &none);
        }
    };
    var n: Norm = .{ .vars = try sig_mod.Vars.base(a, sig_mod.find("S1").?) };
    const norm: Normalizer = .{ .ctx = &n, .run = Norm.run };
    const eqs = [_]Equation{.{ .lhs = try term.parse(a, "or_(x0, x0)"), .rhs = try term.parse(a, "x0"), .normalize = true }};
    try testing.expect(!try equalModulo(a, try term.parse(a, "payload#0(tag#1())"), try term.parse(a, "x2"), &eqs, norm, 2));
    try testing.expect(try equalModulo(a, try term.parse(a, "or_(x0, x0)"), try term.parse(a, "x0"), &eqs, norm, 2));
}

test "a step by a conditional equation is taken only where its conditions hold" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const Same = struct {
        fn run(_: *anyopaque, _: Allocator, t: Term) Allocator.Error!?Term {
            return t;
        }
    };
    var dummy: u8 = 0;
    const norm: Normalizer = .{ .ctx = &dummy, .run = Same.run };
    const eqs = [_]Equation{.{ .lhs = try term.parse(a, "o0.minus(x0, x0)"), .rhs = try term.parse(a, "0"), .normalize = true, .conds = &.{ .{ .speculatable = 0 }, .int_owner } }};
    const zero = try term.parse(a, "0");
    try testing.expect(try equalModulo(a, try term.parse(a, "Num.I64.minus(x2, x2)"), zero, &eqs, norm, 1));
    // `plus` crashes on overflow, so its difference with itself is not always 0.
    try testing.expect(!try equalModulo(a, try term.parse(a, "Num.I64.minus(Num.I64.plus(x2, 1), Num.I64.plus(x2, 1))"), zero, &eqs, norm, 1));
}

fn tableNorm(_: *anyopaque, ar: Allocator, t: Term) Allocator.Error!?Term {
    const cp = @import("cp.zig");
    const none: [reify.rules.count]bool = @splat(false);
    return cp.normalizeTyped(ar, testing.allocator, t, &none);
}

test "step 1 on the current table: every unjoined critical pair is equal modulo the ledger" {
    // `roc-reify-rule-derivation.md` 4: the check every `zig build test` runs.
    const cp = @import("cp.zig");
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const none: [reify.rules.count]bool = @splat(false);
    const eqs = try equations(a, reify.ledger.current, &.{"step1"});
    var dummy: u8 = 0;
    const norm: Normalizer = .{ .ctx = &dummy, .run = tableNorm };
    const pairs = try cp.all(a, testing.allocator, &none);
    try testing.expect(pairs.len > 0);
    var left: usize = 0;
    for (pairs) |p| {
        if (p.status != .unjoined) continue;
        if (try equalModulo(a, p.normal[0], p.normal[1], eqs, norm, 2)) continue;
        std.debug.print("unjoined, and not in the ledger: {s} = {s}\n", .{ try textOf(a, p.normal[0]), try textOf(a, p.normal[1]) });
        left += 1;
    }
    try testing.expectEqual(@as(usize, 0), left);
}

test "every rejected and open entry's witnesses still normalize apart" {
    // L3 for the rejected list; for the open list, a pair that now meets
    // names the entry the change that joined it must remove.
    const sig_mod = @import("sig.zig");
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const none: [reify.rules.count]bool = @splat(false);
    for ([_][]const Entry{ reify.ledger.current.rejected, reify.ledger.current.open }, [_][]const u8{ "rejected", "open" }) |list, name| for (list) |e| {
        const l = try term.parse(a, e.witness_left);
        const r = try term.parse(a, e.witness_right);
        const same = if (std.mem.eql(u8, e.source, "step1"))
            (try tableNorm(undefined, a, l)).?.eql((try tableNorm(undefined, a, r)).?)
        else blk: {
            const vars = try sig_mod.Vars.base(a, sig_mod.find(e.source).?);
            break :blk (try sig_mod.normalize(a, testing.allocator, vars, l, &none)).eql(try sig_mod.normalize(a, testing.allocator, vars, r, &none));
        };
        if (same) {
            std.debug.print("the {s} entry `{s} = {s}` now joins; remove it from the ledger\n", .{ name, e.lhs, e.rhs });
            return error.TestUnexpectedResult;
        }
    };
}
