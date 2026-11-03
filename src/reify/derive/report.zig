//! The report of one run of `zig build reify-rules`
//! (`roc-reify-rule-derivation.md` 3): the run's parameters, the orientation
//! of every row, the critical pairs, the counts of steps 2 and 3, and the
//! groups left for triage with the command each one proposes.

const std = @import("std");
const reify = @import("reify");
const term = @import("term.zig");
const order = @import("order.zig");
const cp = @import("cp.zig");
const loop = @import("loop.zig");
const classify = @import("classify.zig");
const generalize = @import("generalize.zig");

const Writer = std.Io.Writer;

/// What a run does after its report.
pub const Command = union(enum) {
    none,
    /// Groups of one report, applied in the order given; a later group's
    /// id is its id in that report, not after the earlier admissions.
    admit: []const usize,
    ledger: struct { groups: []const usize, criterion: []const u8 },
    file: struct { groups: []const usize, algorithm: []const u8 },
    /// Measure knockout recall (6.1, criterion 1) over the rows `first` to
    /// `last`, instead of reporting.
    recall: struct { first: usize = 0, last: usize = reify.rules.count - 1 },
};

/// The parameters of a run.
pub const Options = struct {
    /// The signature of `roc-reify-rule-derivation.md` 5, such as `S1`.
    signature: []const u8 = "S1",
    /// The term size bound.
    k: u32 = 3,
    /// The iteration number, recorded with an admitted row.
    iteration: u32 = 1,
    command: Command = .none,
    /// A row the report runs without, by index, to see what the tool finds in its place.
    knockout: ?usize = null,
    /// How many `z3` processes run at once; the report does not depend on it.
    jobs: usize = 12,
    /// The memory one `z3` process may use, in megabytes; a query that needs
    /// more is left unproved.
    z3_memory_mb: u32 = 2048,
};

fn groupArg(text: []const u8) error{InvalidArgs}!usize {
    return std.fmt.parseInt(usize, text, 10) catch error.InvalidArgs;
}

// A comma-separated list of distinct group ids.
fn groupsArg(arena: std.mem.Allocator, text: []const u8) error{InvalidArgs}![]const usize {
    var out: std.ArrayList(usize) = .empty;
    var it = std.mem.splitScalar(u8, text, ',');
    while (it.next()) |g| {
        const id = try groupArg(g);
        if (std.mem.findScalar(usize, out.items, id) != null) return error.InvalidArgs;
        out.append(arena, id) catch return error.InvalidArgs;
    }
    return out.toOwnedSlice(arena) catch error.InvalidArgs;
}

/// Parse `--sig <S>`, `--k <k>`, `--iteration <n>`, `--jobs <n>`, `--z3-memory <MB>`, and at most one of
/// `--admit <groups>`, `--ledger <groups> <criterion>`, `--file <groups> <algorithm>`, `--recall [<first>-<last>]`; and `--knockout <row>` with no command.
/// `<groups>` is one group id or several, comma-separated.
pub fn parseArgs(arena: std.mem.Allocator, args: []const []const u8) error{InvalidArgs}!Options {
    var o: Options = .{};
    var i: usize = 0;
    while (i < args.len) : (i += 1) {
        const a = args[i];
        const left = args.len - i - 1;
        if (std.mem.eql(u8, a, "--sig") and left >= 1) {
            i += 1;
            o.signature = args[i];
        } else if (std.mem.eql(u8, a, "--k") and left >= 1) {
            i += 1;
            o.k = std.fmt.parseInt(u32, args[i], 10) catch return error.InvalidArgs;
        } else if (std.mem.eql(u8, a, "--jobs") and left >= 1) {
            i += 1;
            o.jobs = std.fmt.parseInt(usize, args[i], 10) catch return error.InvalidArgs;
            if (o.jobs == 0) return error.InvalidArgs;
        } else if (std.mem.eql(u8, a, "--z3-memory") and left >= 1) {
            i += 1;
            o.z3_memory_mb = std.fmt.parseInt(u32, args[i], 10) catch return error.InvalidArgs;
            if (o.z3_memory_mb == 0) return error.InvalidArgs;
        } else if (std.mem.eql(u8, a, "--iteration") and left >= 1) {
            i += 1;
            o.iteration = std.fmt.parseInt(u32, args[i], 10) catch return error.InvalidArgs;
        } else if (std.mem.eql(u8, a, "--admit") and left >= 1 and o.command == .none) {
            i += 1;
            o.command = .{ .admit = try groupsArg(arena, args[i]) };
        } else if (std.mem.eql(u8, a, "--ledger") and left >= 2 and o.command == .none) {
            o.command = .{ .ledger = .{ .groups = try groupsArg(arena, args[i + 1]), .criterion = args[i + 2] } };
            i += 2;
        } else if (std.mem.eql(u8, a, "--knockout") and left >= 1) {
            i += 1;
            const row = std.fmt.parseInt(usize, args[i], 10) catch return error.InvalidArgs;
            if (row >= reify.rules.count) return error.InvalidArgs;
            o.knockout = row;
        } else if (std.mem.eql(u8, a, "--recall") and o.command == .none) {
            o.command = .{ .recall = .{} };
            // An optional `<first>-<last>` splits the rows over several runs.
            if (left >= 1 and !std.mem.startsWith(u8, args[i + 1], "--")) {
                i += 1;
                var it = std.mem.splitScalar(u8, args[i], '-');
                const first = try groupArg(it.first());
                const last = try groupArg(it.next() orelse return error.InvalidArgs);
                if (first > last or last >= reify.rules.count) return error.InvalidArgs;
                o.command = .{ .recall = .{ .first = first, .last = last } };
            }
        } else if (std.mem.eql(u8, a, "--file") and left >= 2 and o.command == .none) {
            o.command = .{ .file = .{ .groups = try groupsArg(arena, args[i + 1]), .algorithm = args[i + 2] } };
            i += 2;
        } else return error.InvalidArgs;
    }
    // A command writes the table and ledger, which a run without a row does not describe.
    if (o.knockout != null and o.command != .none) return error.InvalidArgs;
    return o;
}

/// The orientation of one table row.
pub const RowVerdict = struct {
    index: usize,
    rule: reify.rules.Rule,
    /// Null for an evaluation row, whose result is a literal it computes.
    verdict: ?order.Verdict,
};

/// Check the orientation of every row: of every instance of it, and the
/// verdict shown is the first instance that fails, or the first instance.
pub fn orientTable(arena: std.mem.Allocator) std.mem.Allocator.Error![]RowVerdict {
    const out = try arena.alloc(RowVerdict, reify.rules.count);
    for (reify.rules.rules, out, 0..) |r, *o, i| {
        if (r.tier == .evaluation) {
            o.* = .{ .index = i, .rule = r, .verdict = null };
            continue;
        }
        const all = try term.instances(arena, r);
        const lits = try order.ruleLits(arena, r);
        var verdict = order.orient(all[0].lhs, all[0].rhs, lits);
        for (all[1..]) |rt| {
            if (!verdict.oriented) break;
            verdict = order.orient(rt.lhs, rt.rhs, lits);
        }
        o.* = .{ .index = i, .rule = r, .verdict = verdict };
    }
    return out;
}

/// Write the orientation table. Returns whether every row oriented.
pub fn writeOrientation(w: *Writer, rows: []const RowVerdict) Writer.Error!bool {
    try w.writeAll("## Orientation of the table\n\n| Row | Step | Tier | Root | Oriented | Decided by | Context |\n|---|---|---|---|---|---|---|\n");
    var all = true;
    for (rows) |r| {
        try w.print("| {d} | {s} | {s} | {s} | ", .{ r.index, r.rule.step, @tagName(r.rule.tier), @tagName(r.rule.root) });
        const v = r.verdict orelse {
            try w.writeAll("yes | a computed literal | |\n");
            continue;
        };
        if (!v.oriented) all = false;
        try w.print("{s} | ", .{if (v.oriented) "yes" else "no"});
        switch (v.decided_by) {
            .component => |c| try w.print("{s}", .{@tagName(c)}),
            .variable => |x| try w.print("variable {d} occurs more on the right", .{x}),
            .none => try w.writeAll("nothing"),
        }
        try w.print(" | {s} |\n", .{@tagName(v.context)});
    }
    try w.writeAll("\n");
    return all;
}

/// Write the equation with its variables renamed in order of first
/// occurrence, and its conditions.
pub fn writeEq(w: *Writer, eq: generalize.Equation) Writer.Error!void {
    var buf: [64]term.Var = undefined;
    var seen: std.ArrayList(term.Var) = .initBuffer(&buf);
    occurrences(eq.lhs, &seen);
    occurrences(eq.rhs, &seen);
    try term.writeRenamed(w, eq.lhs, seen.items);
    try w.writeAll(" -> ");
    try term.writeRenamed(w, eq.rhs, seen.items);
    for (eq.conds) |c| switch (c) {
        .int_owner => try w.writeAll(" [o0 integer]"),
        .speculatable, .is_lit, .nonzero_lit => |v| try w.print(" [x{d} {s}]", .{ std.mem.findScalar(term.Var, seen.items, v).?, @tagName(c) }),
    };
}

fn occurrences(t: term.Term, seen: *std.ArrayList(term.Var)) void {
    switch (t) {
        .var_ => |v| if (std.mem.findScalar(term.Var, seen.items, v) == null) seen.appendAssumeCapacity(v),
        .app => |x| for (x.args) |a| occurrences(a, seen),
    }
}

fn className(c: ?classify.Class) []const u8 {
    const x = c orelse return "critical pair";
    return switch (x) {
        .f_rule => "F rule",
        .unoriented => "unoriented",
        .context => "context or binder",
        .out_of_scope => "out of scope",
        .unproved => "unproved",
    };
}

/// The command a group's class proposes.
fn proposal(w: *Writer, id: usize, g: loop.Group) Writer.Error!void {
    const c = g.class orelse return w.print("`--file {d} <algorithm>` or `--ledger {d} <criterion>`", .{ id, id });
    switch (c) {
        .f_rule => |f| if (f.row != null)
            try w.print("`--admit {d}`", .{id})
        else
            try w.print("the pattern language cannot state {s}: a person decides (3.5)", .{f.unstated.?}),
        .unoriented => |why| try w.print("`--ledger {d} \"{s}\"`", .{ id, why }),
        .context => |alg| try w.print("`--file {d} {s}`", .{ id, alg }),
        .out_of_scope => |why| try w.print("`--ledger {d} \"{s}\"`", .{ id, why }),
        .unproved => |why| try w.print("none: {s}", .{why}),
    }
}

/// Write the report. Returns whether every row oriented and no group is left.
pub fn write(w: *Writer, options: Options, rows: []const RowVerdict, res: *const loop.Result) Writer.Error!bool {
    try w.print("# reify-rules report\n\nsignature {s}, k = {d}, iteration {d}, rule-set fingerprint {x}\n\n", .{ options.signature, options.k, options.iteration, reify.rules.fingerprint() });
    const all = try writeOrientation(w, rows);
    _ = try cp.write(w, res.pairs);
    try w.print("{d} unjoined pairs are equal modulo the ledger.\n\n", .{res.step1_covered});
    try w.print(
        \\## Steps 2 and 3
        \\
        \\| Irreducible terms | Fingerprint groups | Candidate pairs | Equal modulo the ledger | Refuted | Counterexamples added | Unproved |
        \\|---|---|---|---|---|---|---|
        \\| {d} | {d} | {d} | {d} | {d} | {d} | {d} |
        \\
        \\
    , .{ res.explored.terms, res.explored.groups, res.explored.candidates.len, res.explore_covered, res.refuted, res.counterexamples.items.len, res.unproved.items.len });
    for (res.unproved.items) |u| {
        try w.writeAll("- unproved: `");
        try term.write(w, u.pair[0]);
        try w.writeAll("` = `");
        try term.write(w, u.pair[1]);
        try w.print("`: {s}\n", .{u.why});
    }
    try w.writeAll("\n## Groups\n\n| Group | Source | Class | Equation | Witness | Proposed |\n|---|---|---|---|---|---|\n");
    for (res.groups.items, 1..) |g, id| {
        try w.print("| {d} | {s} | {s} | `", .{ id, @tagName(g.source), className(g.class) });
        try writeEq(w, g.eq);
        try w.writeAll("` | `");
        try term.write(w, g.witnesses.items[0][0]);
        try w.writeAll("` = `");
        try term.write(w, g.witnesses.items[0][1]);
        try w.writeAll("` | ");
        try proposal(w, id, g);
        try w.writeAll(" |\n");
    }
    try w.print("\n{d} groups.\n", .{res.groups.items.len});
    for (res.groups.items, 1..) |g, id| {
        const c = g.class orelse continue;
        switch (c) {
            .f_rule => |f| if (f.row) |row| try w.print("\n### Row of group {d}\n\n```zig\n{s}```\n", .{ id, row }),
            .unoriented, .context, .out_of_scope, .unproved => {},
        }
    }
    return all and res.groups.items.len == 0;
}

const testing = std.testing;

test "every row orients" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const rows = try orientTable(arena.allocator());
    var out: Writer.Allocating = .init(testing.allocator);
    defer out.deinit();
    try testing.expect(try writeOrientation(&out.writer, rows));
    try testing.expect(std.mem.find(u8, out.written(), "| N13h | first_order | prim | yes |") != null);
}

test "arguments parse, and an unknown one is refused" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const o = try parseArgs(a, &.{ "--sig", "S2", "--k", "4", "--file", "3", "N15b" });
    try testing.expectEqualStrings("S2", o.signature);
    try testing.expectEqual(@as(u32, 4), o.k);
    try testing.expectEqualSlices(usize, &.{3}, o.command.file.groups);
    try testing.expectEqualStrings("N15b", o.command.file.algorithm);
    try testing.expectError(error.InvalidArgs, parseArgs(a, &.{"--frobnicate"}));
    const r = (try parseArgs(a, &.{ "--recall", "3-7" })).command.recall;
    try testing.expectEqual(@as(usize, 3), r.first);
    try testing.expectEqual(@as(usize, 7), r.last);
    try testing.expectEqual(@as(usize, reify.rules.count - 1), (try parseArgs(a, &.{ "--recall", "--k", "4" })).command.recall.last);
    try testing.expectError(error.InvalidArgs, parseArgs(a, &.{ "--recall", "7-3" }));
    try testing.expectEqual(@as(?usize, 5), (try parseArgs(a, &.{ "--knockout", "5" })).knockout);
    try testing.expectError(error.InvalidArgs, parseArgs(a, &.{ "--knockout", "5", "--admit", "1" }));
    try testing.expectError(error.InvalidArgs, parseArgs(a, &.{ "--admit", "1", "--admit", "2" }));
    try testing.expectEqualSlices(usize, &.{ 4, 2, 9 }, (try parseArgs(a, &.{ "--admit", "4,2,9" })).command.admit);
    try testing.expectError(error.InvalidArgs, parseArgs(a, &.{ "--admit", "4,4" }));
    try testing.expectEqual(@as(usize, 3), (try parseArgs(a, &.{ "--jobs", "3" })).jobs);
    try testing.expectError(error.InvalidArgs, parseArgs(a, &.{ "--jobs", "0" }));
    try testing.expectEqual(@as(u32, 512), (try parseArgs(a, &.{ "--z3-memory", "512" })).z3_memory_mb);
    try testing.expectError(error.InvalidArgs, parseArgs(a, &.{ "--ledger", "4,", "reason" }));
}
