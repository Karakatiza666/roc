//! Step 2 of the loop (`roc-reify-rule-derivation.md` 3.2): enumerate the
//! irreducible terms of a signature, fingerprint each, and pair every term
//! of a group of equal sort and fingerprint with the group's smallest term.

const std = @import("std");
const reify = @import("reify");
const sig_mod = @import("sig.zig");
const enumerate = @import("enumerate.zig");
const fingerprint = @import("fingerprint.zig");

const Allocator = std.mem.Allocator;

/// Two irreducible terms with one fingerprint: a candidate equation.
pub const Candidate = struct {
    /// The larger term.
    big: enumerate.Entry,
    /// The group's smallest term.
    small: enumerate.Entry,
    /// Whether the two agree only on the inputs where no variable is ⊥, so
    /// the equation is claimed with every variable speculatable.
    defined: bool = false,
};

/// What step 2 found.
pub const Result = struct {
    /// The irreducible terms, by size.
    entries: []const enumerate.Entry,
    terms: usize,
    groups: usize,
    candidates: []const Candidate,
};

const Keyed = struct {
    print: fingerprint.Prints,
    entry: enumerate.Entry,
    order: usize,
};

const Collector = struct {
    arena: Allocator,
    scratch: std.heap.ArenaAllocator,
    input_set: []const []const reify.eval.Value,
    keyed: std.ArrayList(Keyed) = .empty,

    fn visit(ctx: *anyopaque, entry: enumerate.Entry, inst: *sig_mod.Instance) reify.eval.Error!void {
        const self: *Collector = @ptrCast(@alignCast(ctx));
        defer _ = self.scratch.reset(.retain_capacity);
        const print = try fingerprint.of(self.scratch.allocator(), inst, self.input_set);
        try self.keyed.append(self.arena, .{ .print = print, .entry = entry, .order = self.keyed.items.len });
    }
};

/// Run step 2 over `sig` up to size `k`.
pub fn run(arena: Allocator, gpa: Allocator, sig: sig_mod.Signature, vars: sig_mod.Vars, k: u32, extra_inputs: []const []const reify.eval.Value, knocked_out: []const bool) reify.eval.Error!Result {
    var c: Collector = .{ .arena = arena, .scratch = .init(gpa), .input_set = try fingerprint.inputs(arena, vars, extra_inputs) };
    defer c.scratch.deinit();
    const entries = try enumerate.run(arena, gpa, sig, vars, k, knocked_out, .{ .ctx = &c, .visit = Collector.visit });
    var candidates: std.ArrayList(Candidate) = .empty;
    var groups: usize = 0;
    // First the pairs equal on every input, then those equal only where no
    // variable is ⊥; a pair of the first kind is never one of the second.
    for ([_]bool{ false, true }) |defined| {
        // Sort by sort and fingerprint, then by enumeration order, so each
        // group is contiguous and starts with its smallest term.
        std.mem.sort(Keyed, c.keyed.items, defined, struct {
            fn lt(d: bool, a: Keyed, b: Keyed) bool {
                if (a.entry.sort != b.entry.sort) return @backingInt(a.entry.sort) < @backingInt(b.entry.sort);
                if (printOf(a, d) != printOf(b, d)) return printOf(a, d) < printOf(b, d);
                return a.order < b.order;
            }
        }.lt);
        var i: usize = 0;
        while (i < c.keyed.items.len) {
            const first = c.keyed.items[i];
            var j = i + 1;
            var paired = false;
            while (j < c.keyed.items.len and c.keyed.items[j].entry.sort == first.entry.sort and printOf(c.keyed.items[j], defined) == printOf(first, defined)) : (j += 1) {
                if (defined and c.keyed.items[j].print.all == first.print.all) continue;
                try candidates.append(arena, .{ .big = c.keyed.items[j].entry, .small = first.entry, .defined = defined });
                paired = true;
            }
            groups += @intFromBool(paired);
            i = j;
        }
    }
    return .{ .entries = entries, .terms = entries.len, .groups = groups, .candidates = try candidates.toOwnedSlice(arena) };
}

fn printOf(k: Keyed, defined: bool) fingerprint.Fingerprint {
    return if (defined) k.print.defined else k.print.all;
}

test "a pair equal only where no variable is bottom is a defined candidate" {
    const testing = std.testing;
    const term = @import("term.zig");
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const s1 = sig_mod.find("S1").?;
    var vars = try sig_mod.Vars.base(testing.allocator, s1);
    defer vars.deinit(testing.allocator);
    // With T3.1 off, `Bool.is_eq(x, x)` stays, and differs from `True` only at ⊥.
    var knocked: [reify.rules.count]bool = @splat(false);
    for (reify.rules.rules, 0..) |r, i| knocked[i] = std.mem.eql(u8, r.step, "T3.1");
    const res = try run(a, testing.allocator, s1, vars, 3, &.{}, &knocked);
    const lhs = try term.parse(a, "Bool.is_eq(x0, x0)");
    for (res.candidates) |c| {
        if (c.big.t.eql(lhs) and c.small.t.eql(try term.parse(a, "True"))) {
            try testing.expect(c.defined);
            break;
        }
    } else return error.TestUnexpectedResult;
}
