//! Step 3 of the loop and the speculation check of 2.2
//! (`roc-reify-rule-derivation.md` 3.3).
//!
//! | Variables | Proof |
//! |---|---|
//! | `Bool` only | exhaustive over every assignment, ⊥ included: a full proof |
//! | with integers | exhaustive at 8-bit width when at most two integers occur, as a filter; then `z3` at each width asked for |
//!
//! The exhaustive check runs `eval.zig` in both modes; `z3` gets the
//! encoding of `smt.zig`. A `z3` timeout, or a missing `z3` of the pinned
//! version, leaves the pair unproved, never proved.
//!
//! An answer depends only on its script, so the prover runs the scripts a
//! caller will ask for ahead of time, on `jobs` processes at once
//! (`prefetch`), and keeps each answer until it is read. The loop reads the
//! answers in its own order, so a run's report does not depend on `jobs`.
//!
//! Memory is bounded per process: each `z3` runs under `-memory`, and one
//! that reaches it answers `(error "out of memory")`, which leaves the pair
//! unproved. The prover allocates its scripts and outcomes in `arena`, which
//! the loop resets after every candidate, and its answers with `gpa`.

const std = @import("std");
const reify = @import("reify");
const term = @import("term.zig");
const sig_mod = @import("sig.zig");
const smt = @import("smt.zig");

const Allocator = std.mem.Allocator;
const Term = term.Term;
const Value = reify.eval.Value;
const IntTy = reify.types.IntTy;

/// What a proof can fail with, other than an answer of `unknown`.
pub const Error = smt.Error || reify.eval.Error || std.process.SpawnError || std.Io.File.Writer.Error || std.Io.Reader.LimitedAllocError;

/// The `z3` release the tool is pinned to (4).
pub const z3_version = "Z3 version 5.1.0";

/// What one check found.
pub const Outcome = union(enum) {
    proved,
    /// An assignment of every variable of the run, at `width`.
    refuted: struct { width: IntTy, values: []const Value },
    /// Why the check could not decide.
    unknown: []const u8,
};

/// The widths an integer claim is proved at: `I64` for a pair of `S1`
/// terms, every builtin width once the owner is generalized.
pub const Widths = enum {
    i64_only,
    every_int,

    fn list(self: Widths) []const IntTy {
        return switch (self) {
            .i64_only => &.{.i64},
            .every_int => std.enums.values(IntTy),
        };
    }
};

/// The prover of one run.
pub const Prover = struct {
    /// Scripts, models and reasons; the caller may reset or replace it
    /// between proofs, after copying the outcomes it keeps.
    arena: Allocator,
    gpa: Allocator,
    io: std.Io,
    /// Why `z3` is unavailable, or null when the pinned release answered.
    z3_missing: ?[]const u8,
    /// Seconds a query may take.
    timeout_s: u32 = 10,
    queries: usize = 0,
    timeouts: usize = 0,
    /// How many `z3` processes run at once.
    jobs: usize = 12,
    /// The memory one `z3` process may use, in megabytes.
    z3_memory_mb: u32 = 2048,
    /// The answers sent ahead and not read yet, by script, both owned by `gpa`.
    answers: std.StringHashMapUnmanaged([]const u8) = .empty,

    /// One claim of `equation`, for `prefetch`.
    pub const Claim = struct { l: Term, r: Term, assume: []const smt.Assume, widths: Widths };

    /// Check that the pinned `z3` is on `PATH`.
    pub fn init(arena: Allocator, gpa: Allocator, io: std.Io) Prover {
        var p: Prover = .{ .arena = arena, .gpa = gpa, .io = io, .z3_missing = null };
        const r = std.process.run(gpa, io, .{ .argv = &.{ "z3", "--version" } }) catch {
            p.z3_missing = "z3 is not on PATH";
            return p;
        };
        defer gpa.free(r.stdout);
        defer gpa.free(r.stderr);
        if (!std.mem.startsWith(u8, r.stdout, z3_version)) p.z3_missing = std.fmt.allocPrint(arena, "z3 answers `{s}`, the tool is pinned to `{s}`", .{ std.mem.trim(u8, r.stdout, "\n"), z3_version }) catch "z3 is not the pinned release";
        return p;
    }

    /// Free the answers no proof read.
    pub fn deinit(self: *Prover) void {
        var it = self.answers.iterator();
        while (it.next()) |e| {
            self.gpa.free(e.key_ptr.*);
            self.gpa.free(e.value_ptr.*);
        }
        self.answers.deinit(self.gpa);
    }

    /// Whether `l = r` under `assume` in the most-defined semantics.
    pub fn equation(self: *Prover, vars: sig_mod.Vars, l: Term, r: Term, assume: []const smt.Assume, widths: Widths) Error!Outcome {
        return self.check(vars, l, r, assume, widths, .differ);
    }

    /// Whether strict evaluation of `r` never crashes where that of `l` does not.
    pub fn speculation(self: *Prover, vars: sig_mod.Vars, l: Term, r: Term, assume: []const smt.Assume, widths: Widths) Error!Outcome {
        return self.check(vars, l, r, assume, widths, .crashes_more);
    }

    /// Send `z3`, in parallel, every query `equation` would send for each of
    /// `claims`, so that the calls that follow read their answers.
    pub fn prefetch(self: *Prover, vars: sig_mod.Vars, claims: []const Claim) Error!void {
        if (self.z3_missing != null) return;
        var texts: std.ArrayList([]const u8) = .empty;
        for (claims) |c| {
            if (try intAtoms(self.arena, vars, c.l, c.r) == 0) continue;
            for (c.widths.list()) |w| try texts.append(self.arena, try smt.script(self.arena, vars, c.l, c.r, c.assume, w, .differ));
        }
        try self.runAll(texts.items);
    }

    /// Free the answers `prefetch` got for `claims` that no proof read.
    pub fn release(self: *Prover, vars: sig_mod.Vars, claims: []const Claim) Error!void {
        if (self.z3_missing != null) return;
        for (claims) |c| {
            if (try intAtoms(self.arena, vars, c.l, c.r) == 0) continue;
            for (c.widths.list()) |w| self.drop(&.{try smt.script(self.arena, vars, c.l, c.r, c.assume, w, .differ)});
        }
    }

    fn drop(self: *Prover, texts: []const []const u8) void {
        for (texts) |t| if (self.answers.fetchRemove(t)) |kv| {
            self.gpa.free(kv.key);
            self.gpa.free(kv.value);
        };
    }

    // The answer to `text`, read once: it leaves the prover, copied to `arena`.
    fn take(self: *Prover, text: []const u8) Error![]const u8 {
        try self.runAll(&.{text});
        const kv = self.answers.fetchRemove(text).?;
        defer self.gpa.free(kv.key);
        defer self.gpa.free(kv.value);
        return self.arena.dupe(u8, kv.value);
    }

    // Answer every script not answered yet, `jobs` at a time, in order.
    fn runAll(self: *Prover, texts: []const []const u8) Error!void {
        const Running = struct { text: []const u8, child: std.process.Child };
        var running: std.ArrayList(Running) = .empty;
        defer for (running.items) |*r| r.child.kill(self.io);
        var next: usize = 0;
        while (true) {
            while (next < texts.len and running.items.len < self.jobs) : (next += 1) {
                const t = texts[next];
                if (self.answers.contains(t)) continue;
                for (running.items) |r| {
                    if (std.mem.eql(u8, r.text, t)) break;
                } else try running.append(self.arena, .{ .text = t, .child = try self.start(t) });
            }
            if (running.items.len == 0) return;
            var first = running.orderedRemove(0);
            const answer = self.finish(&first.child);
            first.child.kill(self.io);
            const value = try answer;
            errdefer self.gpa.free(value);
            const key = try self.gpa.dupe(u8, first.text);
            errdefer self.gpa.free(key);
            try self.answers.put(self.gpa, key, value);
        }
    }

    fn start(self: *Prover, text: []const u8) Error!std.process.Child {
        self.queries += 1;
        const timeout = try std.fmt.allocPrint(self.arena, "-t:{d}", .{self.timeout_s * 1000});
        const memory = try std.fmt.allocPrint(self.arena, "-memory:{d}", .{self.z3_memory_mb});
        var child = try std.process.spawn(self.io, .{ .argv = &.{ "z3", "-in", timeout, memory }, .stdin = .pipe, .stdout = .pipe, .stderr = .ignore });
        errdefer child.kill(self.io);
        try child.stdin.?.writeStreamingAll(self.io, text);
        child.stdin.?.close(self.io);
        child.stdin = null;
        return child;
    }

    fn finish(self: *Prover, child: *std.process.Child) Error![]const u8 {
        var buf: [4096]u8 = undefined;
        var reader = child.stdout.?.readerStreaming(self.io, &buf);
        return reader.interface.allocRemaining(self.gpa, .unlimited);
    }

    fn check(self: *Prover, vars: sig_mod.Vars, l: Term, r: Term, assume: []const smt.Assume, widths: Widths, query: smt.Query) Error!Outcome {
        const used = try smt.varsOf(self.arena, vars, l, r);
        const int_atoms = try intAtoms(self.arena, vars, l, r);
        if (int_atoms == 0) return self.exhaustive(vars, l, r, used, assume, query);
        // A variable key is an integer atom, and a term with one has no row
        // to evaluate, so `z3` alone decides it.
        if (int_atoms <= 2 and !term.hasVarKey(l) and !term.hasVarKey(r)) {
            const small = try self.exhaustive(vars, l, r, used, assume, query);
            // 8 bits is one of every width, but a refutation there need not
            // hold at 64 bits, where `z3` decides.
            if (small == .refuted and widths == .every_int) return small;
        }
        var texts: std.ArrayList([]const u8) = .empty;
        if (self.z3_missing == null) {
            for (widths.list()) |w| try texts.append(self.arena, try smt.script(self.arena, vars, l, r, assume, w, query));
            try self.runAll(texts.items);
        }
        widths: for (widths.list(), 0..) |w, i| {
            // A width whose script an earlier width sent is proved with it.
            if (i < texts.items.len) for (texts.items[0..i]) |t| {
                if (std.mem.eql(u8, t, texts.items[i])) continue :widths;
            };
            const o = try self.z3(vars, l, r, assume, w, query);
            if (o != .proved) {
                if (texts.items.len > i + 1) self.drop(texts.items[i + 1 ..]);
                return o;
            }
        }
        return .proved;
    }

    fn z3(self: *Prover, vars: sig_mod.Vars, l: Term, r: Term, assume: []const smt.Assume, width: IntTy, query: smt.Query) Error!Outcome {
        if (self.z3_missing) |why| return .{ .unknown = why };
        const text = try smt.script(self.arena, vars, l, r, assume, width, query);
        const answer = try self.take(text);
        const first = std.mem.trim(u8, answer[0 .. std.mem.findScalar(u8, answer, '\n') orelse answer.len], " \r");
        if (std.mem.eql(u8, first, "unsat")) return .proved;
        if (std.mem.eql(u8, first, "sat")) return .{ .refuted = .{ .width = width, .values = try self.model(vars, answer, width) } };
        self.timeouts += 1;
        // Past its memory limit `z3` answers `(error "out of memory")`, or nothing when it cannot start.
        if (first.len == 0) return .{ .unknown = try std.fmt.allocPrint(self.arena, "z3 gave no answer at {s}", .{@tagName(width)}) };
        return .{ .unknown = try std.fmt.allocPrint(self.arena, "z3 answered `{s}` at {s}", .{ first, @tagName(width) }) };
    }

    // The counterexample of a `get-value` answer, over every variable of the
    // run; a variable the terms do not read keeps a defined default.
    fn model(self: *Prover, vars: sig_mod.Vars, answer: []const u8, width: IntTy) Error![]const Value {
        const n = vars.sorts.items.len;
        const parts = try self.arena.alloc([5]?Atom, n);
        @memset(parts, @splat(null));
        var it = std.mem.tokenizeAny(u8, answer, "() \n\r\t");
        _ = it.next();
        while (it.next()) |name| {
            const value = it.next() orelse break;
            if (name.len < 2 or name[0] != 'x') continue;
            const us = std.mem.findScalar(u8, name, '_') orelse continue;
            const k = std.fmt.parseInt(usize, name[1..us], 10) catch continue;
            const part: usize = if (name[us + 1] == 'd') 0 else 1 + (std.fmt.parseInt(usize, name[us + 1 ..], 10) catch continue);
            if (k < n) parts[k][part] = atomOf(value, width);
        }
        const out = try self.arena.alloc(Value, n);
        for (out, vars.sorts.items, parts) |*v, s, p| v.* = try self.valueOf(s, p);
        return out;
    }

    const Atom = union(enum) { b: bool, int: i256 };

    fn atomOf(text: []const u8, width: IntTy) ?Atom {
        if (std.mem.eql(u8, text, "true")) return .{ .b = true };
        if (std.mem.eql(u8, text, "false")) return .{ .b = false };
        const raw: u128 = if (std.mem.startsWith(u8, text, "#x"))
            std.fmt.parseInt(u128, text[2..], 16) catch return null
        else if (std.mem.startsWith(u8, text, "#b"))
            std.fmt.parseInt(u128, text[2..], 2) catch return null
        else
            return null;
        var v: i256 = raw;
        if (width.signed() and v > width.max()) v -= @as(i256, 1) << width.bits();
        return .{ .int = v };
    }

    fn valueOf(self: *Prover, sort: sig_mod.Sort, p: [5]?Atom) Allocator.Error!Value {
        const b = struct {
            fn get(a: ?Atom, default: bool) bool {
                return if (a) |x| x.b else default;
            }
            fn int(a: ?Atom) i256 {
                return if (a) |x| x.int else 0;
            }
        };
        if (!b.get(p[0], true)) return .bottom;
        return switch (sort) {
            .bool => .{ .bool_ = b.get(p[1], false) },
            .i64, .nominal_i64 => .{ .int = b.int(p[1]) },
            .union_ab => if (b.get(p[1], false))
                .{ .tag = .{ .name = sig_mod.tag_a, .payload = try self.arena.dupe(Value, &.{if (b.get(p[2], true)) Value{ .int = b.int(p[3]) } else .bottom}) } }
            else
                .{ .tag = .{ .name = sig_mod.tag_b, .payload = &.{} } },
            .record_xy, .tuple_ib => .{ .agg = try self.arena.dupe(Value, &.{
                if (b.get(p[1], true)) Value{ .int = b.int(p[2]) } else .bottom,
                if (b.get(p[3], true)) Value{ .bool_ = b.get(p[4], false) } else .bottom,
            }) },
            .f64, .str, .union_abc, .list_i64 => unreachable,
        };
    }

    // Every assignment of the used variables at 8 bits, ⊥ included.
    fn exhaustive(self: *Prover, vars: sig_mod.Vars, l: Term, r: Term, used: []const term.Var, assume: []const smt.Assume, query: smt.Query) Error!Outcome {
        const none: [reify.rules.count]bool = @splat(false);
        var li: sig_mod.Instance = undefined;
        try li.init(self.gpa, vars, l, .i8, false, &none);
        defer li.deinit();
        var ri: sig_mod.Instance = undefined;
        try ri.init(self.gpa, vars, r, .i8, false, &none);
        defer ri.deinit();
        var scratch = std.heap.ArenaAllocator.init(self.gpa);
        defer scratch.deinit();

        const domains = try self.arena.alloc([]const Value, used.len);
        for (domains, used) |*d, v| d.* = try domain(self.arena, vars.of(v));
        const args = try self.arena.alloc(Value, vars.sorts.items.len);
        for (args, vars.sorts.items) |*a, s| a.* = (try domain(self.arena, s))[1];
        const index = try self.arena.alloc(usize, used.len);
        @memset(index, 0);
        while (true) {
            for (used, index, domains) |v, i, d| args[v] = d[i];
            if (holds(assume, args)) {
                _ = scratch.reset(.retain_capacity);
                const a = scratch.allocator();
                const differs = switch (query) {
                    .differ => blk: {
                        var el = try reify.eval.Evaluator.init(a, &li.store, &li.types, .most_defined);
                        var er = try reify.eval.Evaluator.init(a, &ri.store, &ri.types, .most_defined);
                        break :blk !(try el.run(li.row, args)).eql(try er.run(ri.row, args));
                    },
                    .crashes_more => (try strictRuns(a, &li, args)) and !(try strictRuns(a, &ri, args)),
                };
                if (differs) return .{ .refuted = .{ .width = .i8, .values = try self.arena.dupe(Value, args) } };
            }
            var k: usize = 0;
            while (k < index.len) : (k += 1) {
                index[k] += 1;
                if (index[k] < domains[k].len) break;
                index[k] = 0;
            }
            if (k == index.len) return .proved;
        }
    }
};

// How many integer atoms the variables of `l` and `r` hold, which picks the proof.
fn intAtoms(arena: Allocator, vars: sig_mod.Vars, l: Term, r: Term) Allocator.Error!usize {
    var n: usize = 0;
    for (try smt.varsOf(arena, vars, l, r)) |v| n += switch (vars.of(v)) {
        .bool => 0,
        .i64, .union_ab, .record_xy, .tuple_ib, .nominal_i64 => 1,
        .f64, .str, .union_abc, .list_i64 => unreachable,
    };
    return n;
}

fn strictRuns(a: Allocator, inst: *sig_mod.Instance, args: []const Value) Error!bool {
    var ev = try reify.eval.Evaluator.init(a, &inst.store, &inst.types, .strict);
    _ = ev.run(inst.row, args) catch |err| switch (err) {
        error.Crash => return false,
        else => return err,
    };
    return true;
}

fn holds(assume: []const smt.Assume, args: []const Value) bool {
    for (assume) |c| switch (c) {
        .defined => |k| if (args[k].hasBottom()) return false,
        .nonzero => |k| if (args[k].hasBottom() or args[k].int == 0) return false,
    };
    return true;
}

// The values of `sort` at 8 bits, ⊥ first.
fn domain(arena: Allocator, sort: sig_mod.Sort) Allocator.Error![]const Value {
    var out: std.ArrayList(Value) = .empty;
    try out.append(arena, .bottom);
    switch (sort) {
        .bool => try out.appendSlice(arena, &.{ .{ .bool_ = false }, .{ .bool_ = true } }),
        .i64 => {
            var i: i256 = -128;
            while (i < 128) : (i += 1) try out.append(arena, .{ .int = i });
        },
        .union_ab => {
            try out.append(arena, .{ .tag = .{ .name = sig_mod.tag_b, .payload = &.{} } });
            for (try domain(arena, .i64)) |v| try out.append(arena, .{ .tag = .{ .name = sig_mod.tag_a, .payload = try arena.dupe(Value, &.{v}) } });
        },
        .nominal_i64 => try out.appendSlice(arena, (try domain(arena, .i64))[1..]),
        .record_xy, .tuple_ib => for (try domain(arena, .i64)) |x| for (try domain(arena, .bool)) |y| {
            try out.append(arena, .{ .agg = try arena.dupe(Value, &.{ x, y }) });
        },
        .f64, .str, .union_abc, .list_i64 => unreachable,
    }
    return out.toOwnedSlice(arena);
}

const testing = std.testing;

fn parseAll(a: Allocator, l: []const u8, r: []const u8) term.ParseError![2]Term {
    return .{ try term.parse(a, l), try term.parse(a, r) };
}

test "exhaustive checks decide Bool equations with bottom among the values" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var vars = try sig_mod.Vars.base(testing.allocator, sig_mod.find("S1").?);
    defer vars.deinit(testing.allocator);
    var p = Prover.init(a, testing.allocator, testing.io);
    defer p.deinit();
    // Parallel And: And(x, False) is False even when x is bottom.
    const t = try parseAll(a, "and_(x0, False)", "False");
    try testing.expectEqual(Outcome.proved, try p.equation(vars, t[0], t[1], &.{}, .i64_only));
    // Bool.is_eq(x, x) is True only where x is defined.
    const u = try parseAll(a, "Bool.is_eq(x0, x0)", "True");
    try testing.expect(try p.equation(vars, u[0], u[1], &.{}, .i64_only) == .refuted);
    try testing.expectEqual(Outcome.proved, try p.equation(vars, u[0], u[1], &.{.{ .defined = 0 }}, .i64_only));
    // Strict And(x, False) crashes at x = bottom; False never does.
    try testing.expectEqual(Outcome.proved, try p.speculation(vars, t[0], t[1], &.{}, .i64_only));
    try testing.expect(try p.speculation(vars, t[1], t[0], &.{}, .i64_only) == .refuted);
}

test "z3 proves an identity at 64 bits and refutes one that overflows" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var vars = try sig_mod.Vars.base(testing.allocator, sig_mod.find("S1").?);
    defer vars.deinit(testing.allocator);
    var p = Prover.init(a, testing.allocator, testing.io);
    defer p.deinit();
    if (p.z3_missing != null) return error.SkipZigTest;
    const t = try parseAll(a, "Num.I64.plus(x2, 0)", "x2");
    try testing.expectEqual(Outcome.proved, try p.equation(vars, t[0], t[1], &.{}, .every_int));
    // (x + 1) - 1 is x only where x + 1 does not overflow.
    const u = try parseAll(a, "Num.I64.minus(Num.I64.plus(x2, 1), 1)", "x2");
    const o = try p.equation(vars, u[0], u[1], &.{}, .i64_only);
    try testing.expect(o == .refuted);
    try testing.expectEqual(@as(i256, std.math.maxInt(i64)), o.refuted.values[2].int);
    // `x * 2` and `x + x` overflow at the same `x`; so do `x // -1` and `0 - x`, at the minimum.
    const m = try parseAll(a, "Num.I64.times(x2, 2)", "Num.I64.plus(x2, x2)");
    try testing.expectEqual(Outcome.proved, try p.equation(vars, m[0], m[1], &.{}, .i64_only));
    const d = try parseAll(a, "Num.I64.div_trunc(x2, -1)", "Num.I64.minus(0, x2)");
    try testing.expectEqual(Outcome.proved, try p.equation(vars, d[0], d[1], &.{}, .i64_only));
    // `x // (y & 2)` fails only where the divisor, 0 or 2, is 0.
    const z = try parseAll(a, "Num.I64.times(Num.I64.div_trunc(x2, Num.I64.bitwise_and(x3, 2)), 0)", "0");
    const zo = try p.equation(vars, z[0], z[1], &.{ .{ .defined = 2 }, .{ .defined = 3 } }, .i64_only);
    try testing.expect(zo == .refuted);
    try testing.expectEqual(@as(i256, 0), zo.refuted.values[3].int & 2);
    // A chain reads all its operands (N15a): a defined x ^ y ^ x is y, and x ^ y ^ y is not y.
    const c = try parseAll(a, "Num.I64.bitwise_xor(x2, x3, x2)", "x3");
    try testing.expectEqual(Outcome.proved, try p.equation(vars, c[0], c[1], &.{.{ .defined = 2 }}, .i64_only));
    const e = try parseAll(a, "Num.I64.bitwise_xor(x2, x3, x3)", "x3");
    try testing.expect(try p.equation(vars, e[0], e[1], &.{.{ .defined = 2 }}, .i64_only) == .refuted);
}

test "prefetched claims are answered in parallel, and the proofs that follow read the answers" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var vars = try sig_mod.Vars.base(testing.allocator, sig_mod.find("S2").?);
    defer vars.deinit(testing.allocator);
    var p = Prover.init(a, testing.allocator, testing.io);
    defer p.deinit();
    if (p.z3_missing != null) return error.SkipZigTest;
    p.jobs = 2;
    const claims = [_]Prover.Claim{
        .{ .l = try term.parse(a, "Num.I64.times(x2, 1)"), .r = try term.parse(a, "x2"), .assume = &.{}, .widths = .i64_only },
        .{ .l = try term.parse(a, "Num.I64.plus(x2, 1)"), .r = try term.parse(a, "x2"), .assume = &.{}, .widths = .i64_only },
        .{ .l = try term.parse(a, "Num.I64.bitwise_or(x2, 0)"), .r = try term.parse(a, "x2"), .assume = &.{}, .widths = .every_int },
    };
    try p.prefetch(vars, &claims);
    // `bitwise_or` and `0` read no sign, so a signed width and the unsigned
    // one of its size send one script.
    const sent = 1 + 1 + std.enums.values(IntTy).len / 2;
    try testing.expectEqual(sent, p.queries);
    for (claims, [_]bool{ true, false, true }) |c, proves| {
        try testing.expectEqual(proves, try p.equation(vars, c.l, c.r, c.assume, c.widths) == .proved);
    }
    try testing.expectEqual(sent, p.queries);
}

test "a z3 process that reaches its memory limit leaves the claim unproved, never proved" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var vars = try sig_mod.Vars.base(testing.allocator, sig_mod.find("S2").?);
    defer vars.deinit(testing.allocator);
    var p = Prover.init(a, testing.allocator, testing.io);
    defer p.deinit();
    if (p.z3_missing != null) return error.SkipZigTest;
    p.z3_memory_mb = 1;
    const t = try parseAll(a, "Num.I64.times(x2, 1)", "x2");
    const o = try p.equation(vars, t[0], t[1], &.{}, .i64_only);
    try testing.expect(o == .unknown);
}
