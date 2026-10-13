//! Criterion 1 of the gate (`roc-reify-rule-derivation.md` 6.1), knockout
//! recall: each first-order row is knocked out in turn and steps 1 to 4
//! run without it at k = its left side's size + 1. The row counts as found
//! when the rules of the admissible groups join every term the row
//! rewrites, which is what the row's fires test asks of the admitted rule.
//! The runs start from an empty ledger: its entries were triaged with the
//! row on, and an open entry such as `switch_(x0, x1, x1) = x1` is the
//! equation of a row filed against it, which would hide the row's absence.

const std = @import("std");
const reify = @import("reify");
const term = @import("term.zig");
const sig_mod = @import("sig.zig");
const prove = @import("prove.zig");
const generalize = @import("generalize.zig");
const triage = @import("triage.zig");
const loop = @import("loop.zig");
const report = @import("report.zig");

const Allocator = std.mem.Allocator;
const Term = term.Term;
const Writer = std.Io.Writer;

/// What knocking out one row found.
pub const Row = struct {
    index: usize,
    /// The smallest left side over the row's first-order instances.
    size: u32,
    /// The size bound the row ran at.
    k: u32,
    /// Irreducible terms without the row that the full table rewrites.
    witnesses: usize,
    /// Witnesses the admissible groups' rules join.
    joined: usize,
    admissible: usize,
    groups: usize,
    /// A witness no admissible rule joins, as text.
    missed: ?[]const u8 = null,
    /// The first admissible rule, as text.
    rule: ?[]const u8 = null,

    /// Whether the row counts as found.
    pub fn found(self: Row) bool {
        return self.witnesses > 0 and self.joined == self.witnesses;
    }
};

const Knocked = struct {
    gpa: Allocator,
    vars: *const sig_mod.Vars,
    knocked_out: []const bool,

    fn run(ctx: *anyopaque, arena: Allocator, t: Term) Allocator.Error!?Term {
        const self: *Knocked = @ptrCast(@alignCast(ctx));
        return sig_mod.normalizeSorted(arena, self.gpa, self.vars.*, t, self.knocked_out);
    }
};

/// Knock out each first-order row from `first` to `last` and measure
/// recall, at a size bound of at most `k_max`.
pub fn run(arena: Allocator, gpa: Allocator, io: std.Io, sig: sig_mod.Signature, k_max: u32, extra_inputs: []const []const reify.eval.Value, first: usize, last: usize) loop.Error![]Row {
    const none: [reify.rules.count]bool = @splat(false);
    var out: std.ArrayList(Row) = .empty;
    for (reify.rules.rules[first .. last + 1], first..) |rule, i| {
        if (rule.tier != .first_order) continue;
        // A row's run is large at k = 5; only its row of the table outlives it.
        var row_arena = std.heap.ArenaAllocator.init(gpa);
        defer row_arena.deinit();
        const ra = row_arena.allocator();
        var row_prover = prove.Prover.init(ra, gpa, io);
        defer row_prover.deinit();
        const prover = &row_prover;
        var size: u32 = std.math.maxInt(u32);
        for (try term.instances(ra, rule)) |inst| size = @min(size, generalize.size(inst.lhs));
        var knocked = none;
        knocked[i] = true;
        const k = @min(size + 1, k_max);
        const res = try loop.run(ra, gpa, prover, sig, k, .{}, extra_inputs, &knocked);

        var row: Row = .{ .index = i, .size = size, .k = k, .witnesses = 0, .joined = 0, .admissible = 0, .groups = res.groups.items.len };
        var eqs: std.ArrayList(triage.Equation) = .empty;
        for (res.groups.items) |g| {
            const c = g.class orelse continue;
            switch (c) {
                .f_rule => |f| if (f.row != null) {
                    try eqs.append(ra, .{ .lhs = g.eq.lhs, .rhs = g.eq.rhs, .normalize = true, .conds = g.eq.conds });
                    if (row.rule == null) {
                        var w: Writer.Allocating = .init(arena);
                        try report.writeEq(&w.writer, g.eq);
                        row.rule = w.written();
                    }
                },
                .unoriented, .context, .out_of_scope, .unproved => {},
            }
        }
        row.admissible = eqs.items.len;
        var norm: Knocked = .{ .gpa = gpa, .vars = &res.vars, .knocked_out = &knocked };
        const kn: triage.Normalizer = .{ .ctx = &norm, .run = Knocked.run };
        for (res.explored.entries) |e| {
            const full = try sig_mod.normalize(ra, gpa, res.vars, e.t, &none);
            if (full.eql(e.t)) continue;
            row.witnesses += 1;
            if (try triage.equalModulo(ra, e.t, full, eqs.items, kn, loop.modulo_depth)) {
                row.joined += 1;
            } else if (row.missed == null) {
                var w: Writer.Allocating = .init(arena);
                try term.write(&w.writer, e.t);
                try w.writer.writeAll("` = `");
                try term.write(&w.writer, full);
                row.missed = w.written();
            }
        }
        try out.append(arena, row);
        std.debug.print("recall: row {d} {s}: {d} of {d} witnesses joined, {d} groups\n", .{ i, rule.step, row.joined, row.witnesses, row.groups });
    }
    return out.toOwnedSlice(arena);
}

/// Write the recall table. Returns the number of rows found.
pub fn write(w: *Writer, rows: []const Row) Writer.Error!usize {
    try w.writeAll("# reify-rules knockout recall (criterion 1)\n\n| Row | Step | Left size | k | Witnesses | Joined | Admissible groups | Groups | Found | First admissible rule | Missed witness |\n|---|---|---|---|---|---|---|---|---|---|---|\n");
    var found: usize = 0;
    for (rows) |r| {
        found += @intFromBool(r.found());
        try w.print("| {d} | {s} | {d} | {d} | {d} | {d} | {d} | {d} | {s} | ", .{ r.index, reify.rules.rules[r.index].step, r.size, r.k, r.witnesses, r.joined, r.admissible, r.groups, if (r.found()) "yes" else "no" });
        if (r.rule) |eq| try w.print("`{s}`", .{eq});
        try w.writeAll(" | ");
        if (r.missed) |m| try w.print("`{s}`", .{m});
        try w.writeAll(" |\n");
    }
    try w.print("\n{d} of {d} rows found.\n", .{ found, rows.len });
    return found;
}
