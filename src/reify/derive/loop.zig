//! One iteration of the loop (`roc-reify-rule-derivation.md` 3): steps 1 to
//! 5 over the current table, ledger and input set, grouped for triage.
//! The run is deterministic: the same table, ledger, signature, k and input
//! set give the same groups in the same order.

const std = @import("std");
const reify = @import("reify");
const term = @import("term.zig");
const sig_mod = @import("sig.zig");
const cp = @import("cp.zig");
const explore = @import("explore.zig");
const prove = @import("prove.zig");
const generalize = @import("generalize.zig");
const classify = @import("classify.zig");
const triage = @import("triage.zig");

const Allocator = std.mem.Allocator;
const Term = term.Term;
const Value = reify.eval.Value;

/// Where a group's witnesses come from.
pub const Source = enum {
    /// Unjoined critical pairs of step 1, over the table's pattern terms.
    step1,
    /// Candidates of step 2, over the signature's terms.
    explore,
};

/// A group of the report: pairs that generalize to one equation.
pub const Group = struct {
    source: Source,
    key: []const u8,
    eq: generalize.Equation,
    /// Null for a step 1 group whose terms have no signature sorts to prove over.
    class: ?classify.Class,
    witnesses: std.ArrayList([2]Term) = .empty,
};

/// What one iteration found.
pub const Result = struct {
    vars: sig_mod.Vars,
    pairs: []const cp.Pair,
    explored: explore.Result,
    refuted: usize = 0,
    /// Counterexamples at `I64`, over the base variables, for `inputs.zon`.
    counterexamples: std.ArrayList([]const Value) = .empty,
    unproved: std.ArrayList(struct { pair: [2]Term, why: []const u8 }) = .empty,
    groups: std.ArrayList(Group) = .empty,
    /// Unjoined critical pairs that the ledger's equations join.
    step1_covered: usize = 0,
    explore_covered: usize = 0,
};

const S1Norm = struct {
    gpa: Allocator,
    /// The run's variables, which generalization grows while the run reads them.
    vars: *const sig_mod.Vars,
    knocked_out: []const bool,

    fn run(ctx: *anyopaque, arena: Allocator, t: Term) Allocator.Error!?Term {
        const self: *S1Norm = @ptrCast(@alignCast(ctx));
        return sig_mod.normalizeSorted(arena, self.gpa, self.vars.*, t, self.knocked_out);
    }
};

const TableNorm = struct {
    gpa: Allocator,
    knocked_out: []const bool,

    fn run(ctx: *anyopaque, arena: Allocator, t: Term) Allocator.Error!?Term {
        const self: *TableNorm = @ptrCast(@alignCast(ctx));
        return cp.normalizeTyped(arena, self.gpa, t, self.knocked_out);
    }
};

/// What an iteration can fail with.
pub const Error = prove.Error || term.ParseError;

/// Depth of the search modulo the ledger.
pub const modulo_depth = 2;

/// Run steps 1 to 5 with the `knocked_out` rows off.
pub fn run(arena: Allocator, gpa: Allocator, prover: *prove.Prover, sig: sig_mod.Signature, k: u32, ledger: reify.ledger.Ledger, extra_inputs: []const []const Value, knocked_out: []const bool) Error!Result {
    const step1_eqs = try triage.equations(arena, ledger, &.{"step1"});
    var res: Result = .{ .vars = try sig_mod.Vars.base(arena, sig), .pairs = try cp.all(arena, gpa, knocked_out), .explored = undefined };

    var table_norm: TableNorm = .{ .gpa = gpa, .knocked_out = knocked_out };
    const tn: triage.Normalizer = .{ .ctx = &table_norm, .run = TableNorm.run };
    const base_count = res.vars.sorts.items.len;
    for (res.pairs) |p| {
        if (p.status != .unjoined) continue;
        const n = p.normal;
        if (try triage.equalModulo(arena, n[0], n[1], step1_eqs, tn, modulo_depth)) {
            res.step1_covered += 1;
            continue;
        }
        // A pair over the signature's sorts goes through steps 3 to 5 like a
        // candidate of step 2; its reducts are equal where every variable is defined.
        if (try overSignature(arena, gpa, res.vars, n)) |sorted| {
            // The side the measure ranks higher first, as step 2 puts its big term first.
            const oriented = try orient(arena, .{ .lhs = sorted[0], .rhs = sorted[1], .conds = &.{} });
            const pair = [2]Term{ oriented.lhs, oriented.rhs };
            var conds: std.ArrayList(generalize.Cond) = .empty;
            var assume: std.ArrayList(@import("smt.zig").Assume) = .empty;
            for (0..res.vars.sorts.items.len) |v| {
                const x: term.Var = @intCast(v);
                if (!pair[0].occurs(x) and !pair[1].occurs(x)) continue;
                try conds.append(arena, .{ .speculatable = x });
                try assume.append(arena, .{ .defined = x });
            }
            switch (try prover.equation(res.vars, pair[0], pair[1], assume.items, .i64_only)) {
                .proved => {
                    const eq = try generalize.run(arena, arena, prover, &res.vars, pair[0], pair[1], conds.items);
                    const key = try generalize.key(arena, res.vars, eq);
                    if (find(res.groups.items, .step1, key)) |g| {
                        if (g.witnesses.items.len < 3) try g.witnesses.append(arena, pair);
                        continue;
                    }
                    const verdict = try classify.run(arena, prover, res.vars, eq);
                    var g: Group = .{ .source = .step1, .key = key, .eq = verdict.eq, .class = verdict.class };
                    try g.witnesses.append(arena, pair);
                    try res.groups.append(arena, g);
                    continue;
                },
                // Both reducts come from rows the table proved, so a refutation is a wrong row.
                .refuted => std.debug.panic("a step 1 pair is refuted: {f}", .{pairText(n)}),
                .unknown => |why| {
                    try res.unproved.append(arena, .{ .pair = pair, .why = try arena.dupe(u8, why) });
                    continue;
                },
            }
        }
        const eq: generalize.Equation = .{ .lhs = n[0], .rhs = n[1], .conds = &.{} };
        const key = try rawKey(arena, eq);
        if (find(res.groups.items, .step1, key)) |g| {
            try g.witnesses.append(arena, n);
            continue;
        }
        var g: Group = .{ .source = .step1, .key = key, .eq = try orient(arena, eq), .class = null };
        try g.witnesses.append(arena, n);
        try res.groups.append(arena, g);
    }

    // Exploration enumerates over the base variables; generalizing step 1 pairs added more.
    res.explored = try explore.run(arena, gpa, sig, try sig_mod.Vars.base(arena, sig), k, extra_inputs, knocked_out);
    var s1_norm: S1Norm = .{ .gpa = gpa, .vars = &res.vars, .knocked_out = knocked_out };
    const sn: triage.Normalizer = .{ .ctx = &s1_norm, .run = S1Norm.run };
    // Step 1's entries are over pattern terms, which every signature
    // instantiates, and an included signature's hold here as written.
    var sources: std.ArrayList([]const u8) = .empty;
    try sources.append(arena, "step1");
    for (sig_mod.signatures) |other| if (sig.includes(other)) try sources.append(arena, other.name);
    const sig_eqs = try triage.equations(arena, ledger, sources.items);
    // Each candidate's search, proofs and generalization allocate in
    // `scratch`, reset after it; what the result keeps is copied to `arena`.
    var scratch_state = std.heap.ArenaAllocator.init(gpa);
    defer scratch_state.deinit();
    const scratch = scratch_state.allocator();
    const prover_arena = prover.arena;
    defer prover.arena = prover_arena;
    prover.arena = scratch;

    // The first proof of every pair the ledger leaves is sent ahead, in
    // parallel; a pair that joins a group on the way has its answer freed.
    const candidates = res.explored.candidates;
    const claim_of = try arena.alloc(?prove.Prover.Claim, candidates.len);
    var claims: std.ArrayList(prove.Prover.Claim) = .empty;
    for (candidates, claim_of) |c, *claim| {
        _ = scratch_state.reset(.retain_capacity);
        claim.* = null;
        if (try triage.equalModulo(scratch, c.big.t, c.small.t, sig_eqs, sn, modulo_depth)) continue;
        claim.* = .{ .l = c.big.t, .r = c.small.t, .assume = (try claimOf(arena, res.vars, c)).assume, .widths = .i64_only };
        try claims.append(arena, claim.*.?);
    }
    _ = scratch_state.reset(.retain_capacity);
    try prover.prefetch(res.vars, claims.items);

    candidates: for (candidates, claim_of) |c, maybe_claim| {
        _ = scratch_state.reset(.retain_capacity);
        const pair = [2]Term{ c.big.t, c.small.t };
        const claim = maybe_claim orelse {
            res.explore_covered += 1;
            continue;
        };
        // A pair that is an instance of a group's equation joins that group
        // as a witness; only the group's own equation is ever admitted.
        for (res.groups.items) |*g| {
            if (g.source != .explore) continue;
            if (try instanceOf(scratch, g.eq, pair)) {
                if (g.witnesses.items.len < 3) try g.witnesses.append(arena, pair);
                try prover.release(res.vars, &.{claim});
                continue :candidates;
            }
        }
        switch (try prover.equation(res.vars, pair[0], pair[1], claim.assume, .i64_only)) {
            .proved => {},
            .refuted => |r| {
                res.refuted += 1;
                if (r.width == .i64) {
                    const vals = try arena.alloc(Value, base_count);
                    for (vals, r.values[0..base_count]) |*v, x| v.* = try dupeValue(arena, x);
                    try res.counterexamples.append(arena, vals);
                }
                continue;
            },
            .unknown => |why| {
                try res.unproved.append(arena, .{ .pair = pair, .why = try arena.dupe(u8, why) });
                continue;
            },
        }
        // Generalization's new variables outlive the candidate: a group's equation names them.
        const eq = try generalize.run(scratch, arena, prover, &res.vars, pair[0], pair[1], (try claimOf(scratch, res.vars, c)).conds);
        const key = try generalize.key(scratch, res.vars, eq);
        if (find(res.groups.items, .explore, key)) |g| {
            if (g.witnesses.items.len < 3) try g.witnesses.append(arena, pair);
            continue;
        }
        const verdict = try classify.run(scratch, prover, res.vars, eq);
        var g: Group = .{ .source = .explore, .key = try arena.dupe(u8, key), .eq = try dupeEquation(arena, verdict.eq), .class = try dupeClass(arena, verdict.class) };
        try g.witnesses.append(arena, pair);
        try res.groups.append(arena, g);
    }
    return res;
}

fn dupeValue(arena: Allocator, v: Value) Allocator.Error!Value {
    const each = struct {
        fn all(a: Allocator, xs: []const Value) Allocator.Error![]const Value {
            const out = try a.alloc(Value, xs.len);
            for (out, xs) |*o, x| o.* = try dupeValue(a, x);
            return out;
        }
    };
    return switch (v) {
        .bottom, .int, .float, .bool_ => v,
        .str => |x| .{ .str = try arena.dupe(u8, x) },
        .agg => |xs| .{ .agg = try each.all(arena, xs) },
        .list => |xs| .{ .list = try each.all(arena, xs) },
        .tag => |t| .{ .tag = .{ .name = t.name, .payload = try each.all(arena, t.payload) } },
    };
}

fn dupeEquation(arena: Allocator, eq: generalize.Equation) Allocator.Error!generalize.Equation {
    return .{ .lhs = try term.dupe(arena, eq.lhs), .rhs = try term.dupe(arena, eq.rhs), .conds = try arena.dupe(generalize.Cond, eq.conds) };
}

fn dupeClass(arena: Allocator, c: classify.Class) Allocator.Error!classify.Class {
    const text = struct {
        fn of(a: Allocator, t: ?[]const u8) Allocator.Error!?[]const u8 {
            return if (t) |x| try a.dupe(u8, x) else null;
        }
    };
    return switch (c) {
        .f_rule => |f| .{ .f_rule = .{ .row = try text.of(arena, f.row), .unstated = try text.of(arena, f.unstated) } },
        .unoriented => |x| .{ .unoriented = try arena.dupe(u8, x) },
        .context => |x| .{ .context = try arena.dupe(u8, x) },
        .out_of_scope => |x| .{ .out_of_scope = try arena.dupe(u8, x) },
        .unproved => |x| .{ .unproved = try arena.dupe(u8, x) },
    };
}

// A pair equal only where no variable is ⊥ is claimed with every variable
// it reads speculatable; generalization drops the conditions it can.
fn claimOf(arena: Allocator, vars: sig_mod.Vars, c: explore.Candidate) Allocator.Error!struct { conds: []const generalize.Cond, assume: []const @import("smt.zig").Assume } {
    var conds: std.ArrayList(generalize.Cond) = .empty;
    var assume: std.ArrayList(@import("smt.zig").Assume) = .empty;
    if (c.defined) for (0..vars.sorts.items.len) |v| {
        const x: term.Var = @intCast(v);
        if (!c.big.t.occurs(x) and !c.small.t.occurs(x)) continue;
        try conds.append(arena, .{ .speculatable = x });
        try assume.append(arena, .{ .defined = x });
    };
    return .{ .conds = conds.items, .assume = assume.items };
}

// The pair with each variable renamed to a base variable of the sort the
// pair gives it, in order, and each integer owner at `I64`, or null when a
// variable, an owner or a node has no signature sort, or a sort has more
// variables than the base has. Base variables are what witnesses name.
fn overSignature(arena: Allocator, gpa: Allocator, vars: sig_mod.Vars, pair: [2]Term) Allocator.Error!?[2]Term {
    const kinds = (try cp.varKinds(arena, gpa, pair)) orelse return null;
    const map = try arena.alloc(?term.Var, kinds.len);
    var used: std.ArrayList(term.Var) = .empty;
    for (kinds, map) |k, *m| m.* = if (k) |kind| blk: {
        const sort: sig_mod.Sort = switch (kind) {
            .bool_ => .bool,
            .int => .i64,
            .other => return null,
        };
        for (vars.sorts.items, 0..) |s, v| {
            const x: term.Var = @intCast(v);
            if (s != sort or std.mem.findScalar(term.Var, used.items, x) != null) continue;
            try used.append(arena, x);
            break :blk x;
        }
        return null;
    } else null;
    var out: [2]Term = undefined;
    for (pair, &out) |t, *o| {
        o.* = (try renamed(arena, t, map)) orelse return null;
        _ = sig_mod.checkSort(vars, o.*) orelse return null;
    }
    return out;
}

fn renamed(arena: Allocator, t: Term, map: []const ?term.Var) Allocator.Error!?Term {
    switch (t) {
        .var_ => |v| return .{ .var_ = map[v].? },
        .app => |x| {
            var sym = x.sym;
            if (sym.owner) |o| switch (o) {
                .bind => sym.owner = .{ .fixed = .i64 },
                .fixed => |f| if (f != .i64 and f != .bool_) return null,
            };
            const args = try arena.alloc(Term, x.args.len);
            for (x.args, args) |a, *r| r.* = (try renamed(arena, a, map)) orelse return null;
            return .{ .app = .{ .sym = sym, .args = args } };
        },
    }
}

const PairText = struct {
    pair: [2]Term,
    pub fn format(self: PairText, w: *std.Io.Writer) std.Io.Writer.Error!void {
        try term.write(w, self.pair[0]);
        try w.writeAll(" = ");
        try term.write(w, self.pair[1]);
    }
};

fn pairText(pair: [2]Term) PairText {
    return .{ .pair = pair };
}

fn find(groups: []Group, source: Source, key: []const u8) ?*Group {
    for (groups) |*g| if (g.source == source and std.mem.eql(u8, g.key, key)) return g;
    return null;
}

fn orient(arena: Allocator, eq: generalize.Equation) Allocator.Error!generalize.Equation {
    const order = @import("order.zig");
    const lits = try eq.lits(arena);
    if (!order.orient(eq.lhs, eq.rhs, lits).oriented and order.orient(eq.rhs, eq.lhs, lits).oriented) return .{ .lhs = eq.rhs, .rhs = eq.lhs, .conds = eq.conds };
    return eq;
}

// The key of an equation over terms without signature sorts.
fn rawKey(arena: Allocator, eq: generalize.Equation) Allocator.Error![]const u8 {
    var order: std.ArrayList(term.Var) = .empty;
    try occurrences(arena, eq.lhs, &order);
    try occurrences(arena, eq.rhs, &order);
    var out: std.Io.Writer.Allocating = .init(arena);
    term.writeRenamed(&out.writer, eq.lhs, order.items) catch return error.OutOfMemory;
    out.writer.writeAll(" = ") catch return error.OutOfMemory;
    term.writeRenamed(&out.writer, eq.rhs, order.items) catch return error.OutOfMemory;
    return out.written();
}

fn occurrences(arena: Allocator, t: Term, order: *std.ArrayList(term.Var)) Allocator.Error!void {
    switch (t) {
        .var_ => |v| if (std.mem.findScalar(term.Var, order.items, v) == null) try order.append(arena, v),
        .app => |x| for (x.args) |a| try occurrences(arena, a, order),
    }
}

fn instanceOf(arena: Allocator, eq: generalize.Equation, pair: [2]Term) Allocator.Error!bool {
    const eqs = [_]triage.Equation{.{ .lhs = eq.lhs, .rhs = eq.rhs, .normalize = true, .conds = eq.conds }};
    const Same = struct {
        fn run(_: *anyopaque, _: Allocator, t: Term) Allocator.Error!?Term {
            return t;
        }
    };
    var dummy: u8 = 0;
    const id: triage.Normalizer = .{ .ctx = &dummy, .run = Same.run };
    // One ledger step and no normalization: the pair is the equation at a position.
    return triage.equalModulo(arena, pair[0], pair[1], &eqs, id, 1);
}
