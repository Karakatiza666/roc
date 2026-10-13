//! `zig build reify-rules`: the offline rule-derivation tool
//! (`roc-reify-rule-derivation.md`). It prints its report to stdout, appends
//! step 3's counterexamples to `inputs.zon`, and runs at most one triage
//! command. It exits with status 1 when a row fails orientation or a group
//! is left, and 2 on a usage error or a signature it does not build yet.

const std = @import("std");
const derive = @import("reify_derive");

const reify = derive.reify;
const triage = derive.triage;
const loop = derive.loop;

/// Compiles the builder's knockout switch and rules-off mode into this program.
pub const reify_rule_hooks = true;

fn usage() noreturn {
    std.debug.print("usage: reify-rules [--sig <S1|S2|S3>] [--k <k>] [--iteration <n>] [--jobs <n>] [--z3-memory <MB>] [--admit <groups> | --ledger <groups> <criterion> | --file <groups> <algorithm> | --recall [<first>-<last>]] [--knockout <row>]\n", .{});
    std.process.exit(2);
}

/// What a run can fail with.
const Error = loop.Error || triage.FileError || derive.fingerprint.ParseError || std.Io.File.Writer.Error;

/// Run the tool.
pub fn main(init: std.process.Init) Error!void {
    const arena = init.arena.allocator();
    const io = init.io;
    const args = try init.minimal.args.toSlice(arena);
    const options = derive.report.parseArgs(arena, @ptrCast(args[1..])) catch usage();
    const sig = derive.sig.find(options.signature) orelse usage();
    if (sig.unbuilt()) |what| {
        std.debug.print("reify-rules: signature {s} needs `{s}`, which the tool does not build yet\n", .{ sig.name, what });
        std.process.exit(2);
    }

    const ledger = try triage.load(arena, io);
    const stored = try triage.loadInputs(arena, io);
    var base = try derive.sig.Vars.base(arena, sig);
    var extra: std.ArrayList([]const reify.eval.Value) = .empty;
    for (stored) |in| {
        if (!std.mem.eql(u8, in.signature, sig.name)) continue;
        const vals = try arena.alloc(reify.eval.Value, in.values.len);
        for (vals, in.values, base.sorts.items) |*v, t, s| v.* = try derive.fingerprint.parseValue(arena, s, t);
        try extra.append(arena, vals);
    }
    base.deinit(arena);

    var prover = derive.prove.Prover.init(arena, init.gpa, io);
    defer prover.deinit();
    prover.jobs = options.jobs;
    prover.z3_memory_mb = options.z3_memory_mb;

    var stdout_buffer: [4096]u8 = undefined;
    var stdout_state = std.Io.File.stdout().writer(io, &stdout_buffer);
    const stdout = &stdout_state.interface;
    if (options.command == .recall) {
        const r = options.command.recall;
        _ = try derive.recall.write(stdout, try derive.recall.run(arena, init.gpa, io, sig, options.k, extra.items, r.first, r.last));
        try stdout.flush();
        return;
    }

    var knocked: [reify.rules.count]bool = @splat(false);
    if (options.knockout) |row| knocked[row] = true;
    const res = try loop.run(arena, init.gpa, &prover, sig, options.k, ledger, extra.items, &knocked);
    const rows = try derive.report.orientTable(arena);
    const clean = try derive.report.write(stdout, options, rows, &res);
    try stdout.print("\nz3: {d} queries, {d} undecided{s}{s}.\n", .{ prover.queries, prover.timeouts, if (prover.z3_missing != null) "; " else "", prover.z3_missing orelse "" });

    if (res.counterexamples.items.len > 0) {
        var all: std.ArrayList(triage.Input) = .empty;
        try all.appendSlice(arena, stored);
        for (res.counterexamples.items) |vals| {
            const texts = try arena.alloc([]const u8, vals.len);
            for (texts, vals, 0..) |*t, v, i| {
                var w: std.Io.Writer.Allocating = .init(arena);
                try derive.fingerprint.writeValue(&w.writer, res.vars.of(@intCast(i)), v);
                t.* = w.written();
            }
            try all.append(arena, .{ .signature = sig.name, .values = texts });
        }
        try triage.saveInputs(arena, io, all.items);
        try stdout.print("{d} counterexamples appended to {s}.\n", .{ res.counterexamples.items.len, triage.inputs_path });
    }

    switch (options.command) {
        .none => {},
        .admit => |ids| {
            // Every group is checked before any is admitted, so a bad id writes nothing.
            for (ids) |id| _ = rowOf(&res, id);
            var next = ledger;
            for (ids) |id| next = try admit(arena, io, stdout, options, sig, next, &res, id);
        },
        .ledger => |c| try record(arena, io, stdout, sig, ledger, &res, c.groups, .rejected, c.criterion),
        .file => |c| try record(arena, io, stdout, sig, ledger, &res, c.groups, .open, c.algorithm),
        .recall => unreachable,
    }
    try stdout.flush();
    if (!clean and options.command == .none) std.process.exit(1);
}

fn groupOf(res: *const loop.Result, id: usize) *const loop.Group {
    if (id == 0 or id > res.groups.items.len) {
        std.debug.print("reify-rules: no group {d}; the report has {d}\n", .{ id, res.groups.items.len });
        std.process.exit(2);
    }
    return &res.groups.items[id - 1];
}

fn entryOf(arena: std.mem.Allocator, sig: derive.sig.Signature, g: *const loop.Group, reason: []const u8) std.mem.Allocator.Error!reify.ledger.Entry {
    const w = g.witnesses.items[0];
    // An entry has no conditions, so a conditional equation is recorded as
    // its witness, which fixes the owner and the literals the conditions name.
    // An integer owner alone is stated by the entry's owner variable.
    var general = true;
    for (g.eq.conds) |c| general = general and c == .int_owner;
    const s: [2][]const u8 = if (general)
        try triage.sides(arena, g.eq.lhs, g.eq.rhs)
    else
        .{ try triage.textOf(arena, w[0]), try triage.textOf(arena, w[1]) };
    return .{
        .source = if (g.source == .step1) "step1" else sig.name,
        .lhs = s[0],
        .rhs = s[1],
        .reason = reason,
        .witness_left = try triage.textOf(arena, w[0]),
        .witness_right = try triage.textOf(arena, w[1]),
    };
}

fn record(arena: std.mem.Allocator, io: std.Io, out: *std.Io.Writer, sig: derive.sig.Signature, ledger: reify.ledger.Ledger, res: *const loop.Result, ids: []const usize, list: triage.List, reason: []const u8) Error!void {
    for (ids) |id| _ = groupOf(res, id);
    var next = ledger;
    for (ids) |id| {
        const entry = try entryOf(arena, sig, groupOf(res, id), reason);
        next = try triage.withEntry(arena, next, list, entry);
        try out.print("group {d} recorded in the ledger's {s} list: `{s} = {s}`, {s}.\n", .{ id, @tagName(list), entry.lhs, entry.rhs, reason });
    }
    try triage.save(arena, io, next);
}

// The row group `id` proposes; a group without one is refused (3.6).
fn rowOf(res: *const loop.Result, id: usize) []const u8 {
    const g = groupOf(res, id);
    const row = blk: {
        const c = g.class orelse break :blk null;
        break :blk switch (c) {
            .f_rule => |f| f.row,
            .unoriented, .context, .out_of_scope, .unproved => null,
        };
    };
    return row orelse {
        std.debug.print("reify-rules: group {d} is not a first-order rule with a row; only such a group is admitted (3.6)\n", .{id});
        std.process.exit(2);
    };
}

/// Admit group `id` into the table and return the ledger after it.
fn admit(arena: std.mem.Allocator, io: std.Io, out: *std.Io.Writer, options: derive.report.Options, sig: derive.sig.Signature, ledger: reify.ledger.Ledger, res: *const loop.Result, id: usize) Error!reify.ledger.Ledger {
    const g = groupOf(res, id);
    const row = rowOf(res, id);
    // Numbered within the iteration: group ids shift after every admission.
    var admitted_here: usize = 0;
    for (ledger.admitted) |e| admitted_here += @intFromBool(e.iteration == options.iteration);
    const step = try std.fmt.allocPrint(arena, "T{d}.{d}", .{ options.iteration, admitted_here + 1 });
    const text = try std.mem.replaceOwned(u8, arena, row, "{step}", step);
    try triage.admitRow(arena, io, text);

    // A rejected entry whose witnesses the new row joins leaves the ledger now.
    const eqs = [_]triage.Equation{.{ .lhs = g.eq.lhs, .rhs = g.eq.rhs, .normalize = true, .conds = g.eq.conds }};
    const none: [reify.rules.count]bool = @splat(false);
    const Norm = struct {
        gpa: std.mem.Allocator,
        vars: derive.sig.Vars,
        fn run(ctx: *anyopaque, a: std.mem.Allocator, t: derive.term.Term) std.mem.Allocator.Error!?derive.term.Term {
            const self: *@This() = @ptrCast(@alignCast(ctx));
            return derive.sig.normalizeSorted(a, self.gpa, self.vars, t, &none);
        }
    };
    var norm: Norm = .{ .gpa = arena, .vars = res.vars };
    var kept: std.ArrayList(reify.ledger.Entry) = .empty;
    for (ledger.rejected) |e| {
        const l = try derive.term.parse(arena, e.witness_left);
        const r = try derive.term.parse(arena, e.witness_right);
        const joinable = !std.mem.eql(u8, e.source, "step1") and sig.includes(derive.sig.find(e.source).?);
        if (joinable and try triage.equalModulo(arena, l, r, &eqs, .{ .ctx = &norm, .run = Norm.run }, 1)) {
            try out.print("rejected entry `{s} = {s}` removed: the new row joins its witnesses.\n", .{ e.lhs, e.rhs });
        } else try kept.append(arena, e);
    }
    var next = ledger;
    next.rejected = kept.items;
    var eq_text: std.Io.Writer.Allocating = .init(arena);
    try derive.report.writeEq(&eq_text.writer, g.eq);
    next.admitted = try std.mem.concat(arena, reify.ledger.Admitted, &.{ ledger.admitted, &.{.{ .step = step, .iteration = options.iteration, .equation = eq_text.written() }} });
    try triage.save(arena, io, next);
    try triage.addDerivedTest(arena, io, .{ .step = step, .signature = sig.name, .lhs = try triage.textOf(arena, g.witnesses.items[0][0]), .rhs = try triage.textOf(arena, g.witnesses.items[0][1]) });
    try out.print("group {d} admitted as row {s} of {s}, with its tests in {s}.\n", .{ id, step, triage.table_path, triage.derived_path });
    return next;
}
