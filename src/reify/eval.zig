//! The reference evaluator of the normal form (I6), for tests and the
//! derivation tool only.
//!
//! Two modes (`roc-reify-rule-derivation.md` 2.1 and 3.3):
//!
//! | Mode | A crash | Region evaluation |
//! |---|---|---|
//! | `strict` | ends the evaluation with `error.Crash` | every node of a region that runs is evaluated |
//! | `most_defined` | is the value ⊥ | a node is evaluated when its value is read; constructors hold ⊥ components; a `Switch`, `And` or `Or` whose result an undecided test cannot change has that result |
//!
//! The evaluator shares no code with the normalizer beyond the IR.

const std = @import("std");
const ir = @import("ir.zig");
const types_mod = @import("types.zig");
const prims = @import("prims.zig");
const float_bits = @import("builtins").float_bits;

const Allocator = std.mem.Allocator;
const Ref = ir.Ref;
const NodeId = ir.NodeId;
const RegionId = ir.RegionId;
const RowId = ir.RowId;

/// How crashes and region evaluation behave.
pub const Mode = enum { strict, most_defined };

/// A value of the normal form's semantics.
pub const Value = union(enum) {
    /// ⊥: a crash, only in `most_defined` mode.
    bottom,
    int: i256,
    /// Float bits; an `F32` holds its 32 bits zero-extended.
    float: u64,
    bool_: bool,
    str: []const u8,
    /// A record's fields in the type's order, or a tuple's elements.
    agg: []const Value,
    /// A tag carries its name, not its position in a union, so the same
    /// value is the same tag at every union that has it.
    tag: struct { name: types_mod.NameId, payload: []const Value },
    list: []const Value,
    /// A `Closure`: the row it calls and the values it captured, which are
    /// the row's first parameters.
    closure: struct { row: RowId, captures: []const Value },

    /// Structural equality; floats compare by bits, and ⊥ equals only ⊥.
    pub fn eql(a: Value, b: Value) bool {
        return switch (a) {
            .bottom => b == .bottom,
            .int => |x| b == .int and b.int == x,
            .float => |x| b == .float and b.float == x,
            .bool_ => |x| b == .bool_ and b.bool_ == x,
            .str => |x| b == .str and std.mem.eql(u8, x, b.str),
            .agg => |xs| b == .agg and eqlSlice(xs, b.agg),
            .tag => |t| b == .tag and b.tag.name == t.name and eqlSlice(t.payload, b.tag.payload),
            .list => |xs| b == .list and eqlSlice(xs, b.list),
            .closure => |c| b == .closure and b.closure.row == c.row and eqlSlice(c.captures, b.closure.captures),
        };
    }

    /// Whether ⊥ occurs in the value or any component of it.
    pub fn hasBottom(self: Value) bool {
        return switch (self) {
            .bottom => true,
            .int, .float, .bool_, .str => false,
            .agg, .list => |xs| for (xs) |x| {
                if (x.hasBottom()) break true;
            } else false,
            .closure => |c| for (c.captures) |x| {
                if (x.hasBottom()) break true;
            } else false,
            .tag => |t| for (t.payload) |x| {
                if (x.hasBottom()) break true;
            } else false,
        };
    }

    /// Structural equality of two value lists.
    pub fn eqlSlice(xs: []const Value, ys: []const Value) bool {
        if (xs.len != ys.len) return false;
        for (xs, ys) |x, y| {
            if (!x.eql(y)) return false;
        }
        return true;
    }
};

/// Why an evaluation stopped without a value.
pub const Error = error{
    /// A crash, in `strict` mode.
    Crash,
    /// The fuel ran out: a loop that does not end, or a very long one.
    OutOfFuel,
    /// A builtin the evaluator does not implement.
    Unsupported,
} || Allocator.Error;

const Outcome = union(enum) {
    value: []const Value,
    jump: struct { join: RegionId, args: []const Value },
    ret: Value,
    cont: []const Value,
    brk: []const Value,
    bottom,
};

const Frame = struct {
    row: RowId,
    args: []const Value,
    nodes: []?[]const Value,
    params: []?[]const Value,
};

/// The evaluator over one store. Values are allocated in `arena`.
pub const Evaluator = struct {
    arena: Allocator,
    store: *const ir.Store,
    types: *const types_mod.Types,
    mode: Mode,
    fuel: u64 = 1_000_000,
    /// Per region, its nodes in id order, which is a dependency order.
    by_region: [][]NodeId,
    /// The value of each input slot of the store, by slot id (N18). A test
    /// that builds slots sets it before `run`.
    inputs: []const Value = &.{},

    /// Index the store's regions. Call again after adding nodes.
    pub fn init(arena: Allocator, store: *const ir.Store, types: *const types_mod.Types, mode: Mode) Allocator.Error!Evaluator {
        const counts = try arena.alloc(u32, store.regionCount());
        @memset(counts, 0);
        for (store.nodes.items(.region)) |r| counts[r.index()] += 1;
        const by_region = try arena.alloc([]NodeId, store.regionCount());
        for (by_region, counts) |*slot, c| slot.* = try arena.alloc(NodeId, c);
        @memset(counts, 0);
        for (store.nodes.items(.region), 0..) |r, i| {
            by_region[r.index()][counts[r.index()]] = NodeId.of(@intCast(i));
            counts[r.index()] += 1;
        }
        return .{ .arena = arena, .store = store, .types = types, .mode = mode, .by_region = by_region };
    }

    /// Evaluate `row` on `args`. `most_defined` gives ⊥ for a crash; `strict` returns `error.Crash`.
    pub fn run(self: *Evaluator, row: RowId, args: []const Value) Error!Value {
        var frame = try self.newFrame(row, args);
        const out = try self.evalRegion(&frame, self.store.row(row).body);
        return switch (out) {
            .value => |vs| vs[0],
            .ret => |v| v,
            .bottom => .bottom,
            .jump, .cont, .brk => unreachable, // a row body ends in a value, ret or bottom; jumps and loop ends are consumed by their own region
        };
    }

    fn newFrame(self: *Evaluator, row: RowId, args: []const Value) Allocator.Error!Frame {
        const nodes = try self.arena.alloc(?[]const Value, self.store.nodeCount());
        @memset(nodes, null);
        const params = try self.arena.alloc(?[]const Value, self.store.regionCount());
        @memset(params, null);
        return .{ .row = row, .args = args, .nodes = nodes, .params = params };
    }

    fn tick(self: *Evaluator) Error!void {
        if (self.fuel == 0) return error.OutOfFuel;
        self.fuel -= 1;
    }

    fn crash(self: *const Evaluator) Error!Value {
        return switch (self.mode) {
            .strict => error.Crash,
            .most_defined => .bottom,
        };
    }

    fn evalRef(self: *Evaluator, frame: *Frame, ref: Ref) Error!Value {
        return switch (ref.kind) {
            // A row argument holding ⊥ stands for a node that crashed where
            // it was read, so strict evaluation crashes on reading it.
            .row_param => if (self.mode == .strict and frame.args[ref.output].hasBottom()) error.Crash else frame.args[ref.output],
            .region_param => frame.params[ref.target].?[ref.output],
            .input => self.inputs[ref.target],
            .node => (try self.evalNode(frame, ref.nodeId()))[ref.output],
        };
    }

    fn evalRefs(self: *Evaluator, frame: *Frame, span: ir.Span) Error![]const Value {
        const refs = self.store.refSlice(span);
        const out = try self.arena.alloc(Value, refs.len);
        for (refs, out) |r, *o| o.* = try self.evalRef(frame, r);
        return out;
    }

    // Clears the memo of every node in `r` and the regions it owns, so a
    // loop body evaluates afresh on every turn.
    fn forget(self: *Evaluator, frame: *Frame, r: RegionId) void {
        for (self.by_region[r.index()]) |n| {
            frame.nodes[n.index()] = null;
            for (self.store.regionSlice(self.store.nodes.items(.regions)[n.index()])) |sub| self.forget(frame, sub);
        }
    }

    fn evalRegion(self: *Evaluator, frame: *Frame, r: RegionId) Error!Outcome {
        try self.tick();
        const end = self.store.region(r).end;
        switch (self.mode) {
            // The exiting switch a region ends in runs through its `Branch`.
            .strict => for (self.by_region[r.index()]) |n| {
                if (end.kind == .branch and n.index() == end.target) continue;
                _ = try self.evalNode(frame, n);
            },
            .most_defined => {},
        }
        return switch (end.kind) {
            .open => unreachable, // evalRegion runs on closed regions only (verify rejects open ends)
            .value => .{ .value = try self.evalRefs(frame, end.refs) },
            .jump => .{ .jump = .{ .join = RegionId.of(end.target), .args = try self.evalRefs(frame, end.refs) } },
            .return_ => .{ .ret = (try self.evalRefs(frame, end.refs))[0] },
            .continue_ => .{ .cont = try self.evalRefs(frame, end.refs) },
            .break_ => .{ .brk = try self.evalRefs(frame, end.refs) },
            .branch => self.evalExiting(frame, NodeId.of(end.target)),
        };
    }

    fn evalExiting(self: *Evaluator, frame: *Frame, n: NodeId) Error!Outcome {
        const node = self.store.node(n);
        const scrutinee = try self.evalRef(frame, self.store.refSlice(node.args)[0]);
        if (scrutinee == .bottom) return .bottom;
        var out = try self.evalRegion(frame, self.armFor(frame, node, scrutinee));
        while (true) switch (out) {
            .jump => |j| {
                frame.params[j.join.index()] = j.args;
                out = try self.evalRegion(frame, j.join);
            },
            .value, .ret, .cont, .brk, .bottom => return out,
        };
    }

    fn armFor(self: *const Evaluator, frame: *const Frame, node: ir.Node, scrutinee: Value) RegionId {
        const regions = self.store.regionSlice(node.regions);
        const keys = self.store.wordSlice(node.aux);
        const arm: u32 = switch (scrutinee) {
            .bool_ => |b| @intFromBool(b),
            // The arms are the members of the scrutinee's own type, which can
            // be narrower than the type another reader gives the value.
            .tag => |t| self.types.memberIndex(self.store.refTy(frame.row, self.store.refSlice(node.args)[0]), t.name) orelse
                @import("base").invariant("reify eval: a switch scrutinee holds a tag its type lacks", .{}),
            .int, .str, .float => blk: {
                for (keys, 0..) |k, i| {
                    if (litValue(self, ir.LitId.of(k)).eql(scrutinee)) break :blk @intCast(i);
                }
                break :blk node.payload - 1;
            },
            .bottom, .agg, .list, .closure => unreachable, // evalSwitch handles a bottom scrutinee before armFor; aggs, lists and closures are never switched on
        };
        return regions[arm];
    }

    fn evalNode(self: *Evaluator, frame: *Frame, n: NodeId) Error![]const Value {
        if (frame.nodes[n.index()]) |v| return v;
        try self.tick();
        const node = self.store.node(n);
        const out: []const Value = switch (node.op) {
            .switch_ => try self.evalSwitch(frame, node),
            .for_range, .for_list, .loop => try self.evalLoop(frame, node),
            .and_, .or_ => try self.one(try self.evalAndOr(frame, node)),
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .unwrap, .closure, .field, .index, .payload, .elem, .opt_field, .prim, .call, .lambda, .apply => try self.one(try self.evalSimple(frame, node)),
        };
        frame.nodes[n.index()] = out;
        return out;
    }

    fn one(self: *Evaluator, v: Value) Allocator.Error![]const Value {
        const out = try self.arena.alloc(Value, 1);
        out[0] = v;
        return out;
    }

    fn evalSimple(self: *Evaluator, frame: *Frame, node: ir.Node) Error!Value {
        switch (node.op) {
            .lit => return litValue(self, ir.LitId.of(node.payload)),
            .crash => return self.crash(),
            .derived, .lambda, .apply, .opt_field => return error.Unsupported,
            .closure => return .{ .closure = .{ .row = RowId.of(node.payload), .captures = try self.evalRefs(frame, node.args) } },
            .list => return .{ .list = try self.evalRefs(frame, node.args) },
            // A bound the normalizer proved dominates an `Elem`; where it does not hold, the body is not normal.
            .elem => {
                const args = try self.evalRefs(frame, node.args);
                for (args) |a| if (a == .bottom) return .bottom;
                const at = args[1].int;
                if (at < 0 or at >= args[0].list.len) return self.crash();
                return args[0].list[@intCast(at)];
            },
            .record => {
                // A record that leaves a member unset has no value for it, and
                // the evaluator has no value of an absent member.
                const members = self.types.memberSlice(self.types.get(self.store.tySlice(node.tys)[0]).record);
                if (node.args.len != members.len) return error.Unsupported;
                return .{ .agg = try self.evalRefs(frame, node.args) };
            },
            .tuple => return .{ .agg = try self.evalRefs(frame, node.args) },
            .tag => return .{ .tag = .{ .name = types_mod.NameId.of(node.payload), .payload = try self.evalRefs(frame, node.args) } },
            .wrap, .unwrap => return self.evalRef(frame, self.store.refSlice(node.args)[0]),
            .field, .index => {
                const x = try self.evalRef(frame, self.store.refSlice(node.args)[0]);
                return switch (x) {
                    .bottom => .bottom,
                    .agg => |xs| xs[node.payload],
                    .int, .float, .bool_, .str, .tag, .list, .closure => unreachable, // field and index read an aggregate by the typing of the body
                };
            },
            .payload => {
                const x = try self.evalRef(frame, self.store.refSlice(node.args)[0]);
                return switch (x) {
                    .bottom => .bottom,
                    // Reading a payload of another tag is a compiler bug in a
                    // well-formed body, and ⊥ in a candidate the derivation built.
                    .tag => |t| if (t.name.index() == node.payload) t.payload[self.store.wordSlice(node.aux)[0]] else self.crash(),
                    .int, .float, .bool_, .str, .agg, .list, .closure => unreachable, // payload reads a tag by the typing of the body
                };
            },
            .call => {
                const args = try self.evalRefs(frame, node.args);
                for (args) |a| if (a == .bottom) return .bottom;
                return self.callRow(RowId.of(node.payload), args);
            },
            .prim => {
                const args = try self.evalRefs(frame, node.args);
                for (args) |a| if (a == .bottom) return .bottom;
                // A primitive the table does not hold has no semantics here.
                const p = prims.lookup(ir.PrimId.of(node.payload)) orelse return .bottom;
                return self.evalPrim(p, args);
            },
            .switch_, .for_range, .for_list, .loop, .and_, .or_ => unreachable, // control-flow ops are evaluated by evalNode's own prongs, not here
        }
    }

    fn evalSwitch(self: *Evaluator, frame: *Frame, node: ir.Node) Error![]const Value {
        const outputs = node.tys.len;
        const scrutinee = try self.evalRef(frame, self.store.refSlice(node.args)[0]);
        if (scrutinee != .bottom) {
            return switch (try self.evalRegion(frame, self.armFor(frame, node, scrutinee))) {
                .value => |vs| vs,
                .bottom => try self.bottoms(outputs),
                .jump, .ret, .cont, .brk => unreachable, // a switch arm ends in a value or bottom
            };
        }
        // ⊥ scrutinee: each output that every arm gives as one value, none ⊥, has it.
        const arms = self.store.regionSlice(node.regions)[0..node.payload];
        const results = try self.arena.alloc([]const Value, arms.len);
        for (arms, results) |arm, *res| {
            res.* = switch (try self.evalRegion(frame, arm)) {
                .value => |vs| vs,
                .bottom => try self.bottoms(outputs),
                .jump, .ret, .cont, .brk => unreachable, // a switch arm ends in a value or bottom
            };
        }
        const out = try self.arena.alloc(Value, outputs);
        for (out, 0..) |*o, k| {
            o.* = results[0][k];
            for (results[1..]) |res| {
                if (!res[k].eql(o.*)) o.* = .bottom;
            }
        }
        return out;
    }

    fn bottoms(self: *Evaluator, n: usize) Allocator.Error![]const Value {
        const out = try self.arena.alloc(Value, n);
        @memset(out, .bottom);
        return out;
    }

    fn evalAndOr(self: *Evaluator, frame: *Frame, node: ir.Node) Error!Value {
        const decisive = node.op == .or_;
        var saw_bottom = false;
        const first = try self.evalRef(frame, self.store.refSlice(node.args)[0]);
        switch (first) {
            .bool_ => |b| if (b == decisive) return first,
            .bottom => saw_bottom = true,
            .int, .float, .str, .agg, .tag, .list, .closure => unreachable, // And and Or operands are Bool or bottom by the typing of the body
        }
        for (self.store.regionSlice(node.regions)) |r| {
            const v: Value = switch (try self.evalRegion(frame, r)) {
                .value => |vs| vs[0],
                .bottom => .bottom,
                .jump, .ret, .cont, .brk => unreachable, // And and Or operand regions end in a value or bottom
            };
            switch (v) {
                .bool_ => |b| if (b == decisive) return v,
                .bottom => {
                    // Strict evaluation never reaches here; most-defined keeps
                    // looking for an operand that decides the result.
                    saw_bottom = true;
                },
                .int, .float, .str, .agg, .tag, .list, .closure => unreachable, // And and Or operands are Bool or bottom by the typing of the body
            }
        }
        if (saw_bottom) return .bottom;
        return .{ .bool_ = !decisive };
    }

    fn evalLoop(self: *Evaluator, frame: *Frame, node: ir.Node) Error![]const Value {
        const args = try self.evalRefs(frame, node.args);
        for (args) |a| if (a == .bottom) return self.bottoms(node.tys.len);
        const body = self.store.regionSlice(node.regions)[0];
        var slots: []const Value = switch (node.op) {
            .for_range, .for_list => args[@as(usize, 1) + @intFromBool(node.op == .for_range) ..],
            .loop => args,
            .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .unwrap, .closure, .field, .index, .payload, .elem, .opt_field, .prim, .call, .lambda, .apply, .and_, .or_, .switch_ => unreachable, // evalLoop is only called for loop ops
        };
        var turn: i256 = 0;
        while (true) {
            var params: std.ArrayList(Value) = .empty;
            switch (node.op) {
                .for_range => {
                    const i = args[0].int + turn;
                    if (if (node.payload == 1) i > args[1].int else i >= args[1].int) return slots;
                    try params.append(self.arena, .{ .int = i });
                },
                .for_list => {
                    const xs = args[0].list;
                    if (turn >= xs.len) return slots;
                    try params.appendSlice(self.arena, &.{ .{ .int = turn }, xs[@intCast(turn)] });
                },
                .loop => {},
                .lit, .crash, .derived, .record, .tuple, .list, .tag, .wrap, .unwrap, .closure, .field, .index, .payload, .elem, .opt_field, .prim, .call, .lambda, .apply, .and_, .or_, .switch_ => unreachable, // evalLoop is only called for loop ops
            }
            try params.appendSlice(self.arena, slots);
            self.forget(frame, body);
            frame.params[body.index()] = params.items;
            switch (try self.evalRegion(frame, body)) {
                .cont => |next| slots = next,
                .brk => |vs| return vs,
                .bottom => return self.bottoms(node.tys.len),
                .value, .jump, .ret => unreachable, // a loop body ends in cont, brk or bottom
            }
            turn += 1;
        }
    }

    fn evalPrim(self: *Evaluator, p: prims.Prim, args: []const Value) Error!Value {
        if (p.owner.int()) |int| return self.evalInt(int, p.method, args);
        if (p.owner.float()) |float| return evalFloat(float, p.method, args);
        return switch (p.method) {
            .not => .{ .bool_ = !args[0].bool_ },
            .is_eq => .{ .bool_ = args[0].eql(args[1]) },
            // A chain N15a flattened concatenates every operand in order.
            .concat => switch (args[0]) {
                .str => blk: {
                    var out: std.ArrayList(u8) = .empty;
                    for (args) |a| try out.appendSlice(self.arena, a.str);
                    break :blk .{ .str = out.items };
                },
                .list => blk: {
                    var out: std.ArrayList(Value) = .empty;
                    for (args) |a| try out.appendSlice(self.arena, a.list);
                    break :blk .{ .list = out.items };
                },
                .bottom, .int, .float, .bool_, .agg, .tag, .closure => unreachable, // concat's operands are strs or lists by the typing of the body
            },
            .len => .{ .int = args[0].list.len },
            // `Try(elem, [OutOfBounds])`: the tags are found by name.
            .get => blk: {
                const xs = args[0].list;
                const at = args[1].int;
                const ok = self.types.findName("Ok") orelse return error.Unsupported;
                const err = self.types.findName("Err") orelse return error.Unsupported;
                const out_of_bounds = self.types.findName("OutOfBounds") orelse return error.Unsupported;
                const payload = try self.arena.alloc(Value, 1);
                if (at >= 0 and at < xs.len) {
                    payload[0] = xs[@intCast(at)];
                    break :blk .{ .tag = .{ .name = ok, .payload = payload } };
                }
                payload[0] = .{ .tag = .{ .name = out_of_bounds, .payload = &.{} } };
                break :blk .{ .tag = .{ .name = err, .payload = payload } };
            },
            .is_empty => .{ .bool_ = args[0].list.len == 0 },
            .append => blk: {
                const out = try self.arena.alloc(Value, args[0].list.len + 1);
                @memcpy(out[0..args[0].list.len], args[0].list);
                out[args[0].list.len] = args[1];
                break :blk .{ .list = out };
            },
            // The function is called on every element, first to last, as the
            // builtins' loops call it (`Builtin.roc`).
            .map => blk: {
                const out = try self.arena.alloc(Value, args[0].list.len);
                for (args[0].list, out) |x, *o| {
                    o.* = try self.apply(args[1], &.{x});
                    if (o.* == .bottom) break :blk .bottom;
                }
                break :blk .{ .list = out };
            },
            .keep_if => blk: {
                var out: std.ArrayList(Value) = .empty;
                for (args[0].list) |x| switch (try self.apply(args[1], &.{x})) {
                    .bool_ => |keep| if (keep) try out.append(self.arena, x),
                    .bottom => break :blk .bottom,
                    .int, .float, .str, .agg, .tag, .list, .closure => unreachable, // a predicate gives a Bool by the typing of the body
                };
                break :blk .{ .list = out.items };
            },
            .fold => blk: {
                var state = args[1];
                for (args[0].list) |x| {
                    state = try self.apply(args[2], &.{ state, x });
                    if (state == .bottom) break :blk .bottom;
                }
                break :blk state;
            },
            // An iterator has no value here.
            .collect => error.Unsupported,
            .is_lt, .is_lte, .is_gt, .is_gte, .plus, .minus, .times, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor => error.Unsupported,
        };
    }

    /// The value of row `row` over `args`, none of them ⊥.
    fn callRow(self: *Evaluator, row: RowId, args: []const Value) Error!Value {
        var callee = try self.newFrame(row, args);
        const out = try self.evalRegion(&callee, self.store.row(row).body);
        return switch (out) {
            .value => |vs| vs[0],
            .ret => |v| v,
            .bottom => .bottom,
            .jump, .cont, .brk => unreachable, // a called row body ends in a value, ret or bottom
        };
    }

    /// The value of the function `f` over `args`: a closure calls its row
    /// with its captures first.
    fn apply(self: *Evaluator, f: Value, args: []const Value) Error!Value {
        for (args) |a| if (a == .bottom) return .bottom;
        const c = switch (f) {
            .closure => |c| c,
            .bottom => return .bottom,
            .int, .float, .bool_, .str, .agg, .tag, .list => unreachable, // a function argument is a closure by the typing of the body
        };
        for (c.captures) |a| if (a == .bottom) return .bottom;
        const all = try std.mem.concat(self.arena, Value, &.{ c.captures, args });
        return self.callRow(c.row, all);
    }

    fn evalInt(self: *Evaluator, int: types_mod.IntTy, method: prims.Method, args: []const Value) Error!Value {
        const vals = try self.arena.alloc(i256, args.len);
        for (vals, args) |*v, a| v.* = a.int;
        return switch (prims.foldIntAll(int, method, vals) orelse return self.crash()) {
            .bool_ => |v| .{ .bool_ = v },
            .int => |v| .{ .int = v },
            .float, .str => unreachable, // integer builtins fold to a Bool or an integer
        };
    }
};

fn evalFloat(float: types_mod.FloatTy, method: prims.Method, args: []const Value) Error!Value {
    switch (float) {
        .f64 => {
            const a: f64 = @bitCast(args[0].float);
            const b: f64 = if (args.len > 1) @bitCast(args[1].float) else 0;
            return floatResult(f64, method, a, b);
        },
        .f32 => {
            const a: f32 = @bitCast(@as(u32, @truncate(args[0].float)));
            const b: f32 = if (args.len > 1) @bitCast(@as(u32, @truncate(args[1].float))) else 0;
            return floatResult(f32, method, a, b);
        },
    }
}

fn canonicalNan(comptime F: type, bits: @Int(.unsigned, @bitSizeOf(F))) u64 {
    return if (F == f32) float_bits.normalizeF32NanBits(bits) else float_bits.normalizeF64NanBits(bits);
}

fn floatResult(comptime F: type, method: prims.Method, a: F, b: F) Error!Value {
    const Bits = @Int(.unsigned, @bitSizeOf(F));
    return switch (method) {
        .is_eq => .{ .bool_ = a == b },
        .is_lt => .{ .bool_ = a < b },
        .is_lte => .{ .bool_ = a <= b },
        .is_gt => .{ .bool_ = a > b },
        .is_gte => .{ .bool_ = a >= b },
        // A `NaN` result is Roc's canonical `NaN`, as Roc gives one it observes.
        .plus => .{ .float = canonicalNan(F, @as(Bits, @bitCast(a + b))) },
        .minus => .{ .float = canonicalNan(F, @as(Bits, @bitCast(a - b))) },
        .times => .{ .float = canonicalNan(F, @as(Bits, @bitCast(a * b))) },
        .not, .div_trunc, .plus_wrap, .times_wrap, .bitwise_and, .bitwise_or, .bitwise_xor, .concat, .len, .get, .is_empty, .append, .map, .keep_if, .fold, .collect => unreachable, // float prims admit no other methods (prims.admits)
    };
}

fn litValue(self: *const Evaluator, id: ir.LitId) Value {
    const lit = self.store.lit(id);
    return switch (lit.value) {
        .int => |bits| blk: {
            const int = self.types.get(lit.ty).int;
            const raw: i128 = @bitCast(bits);
            break :blk .{ .int = if (int.signed()) raw else @as(i256, bits) };
        },
        .float => |bits| .{ .float = bits },
        .bool_ => |b| .{ .bool_ = b },
        .str => |span| .{ .str = self.store.byteSlice(span) },
        // No builtin the evaluator runs reads a `Dec` or an embedded file.
        .dec, .bytes => .bottom,
    };
}

const testing = std.testing;
const builder_mod = @import("builder.zig");

test "strict evaluation crashes on dead division; most-defined does not" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    const row = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    _ = try b.call(.i64, .div_trunc, &.{ Ref.rowParam(0), Ref.rowParam(1) });
    try b.endRow(.{ .value = &.{Ref.rowParam(0)} });

    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var strict = try Evaluator.init(arena.allocator(), &store, &types, .strict);
    try testing.expectError(error.Crash, strict.run(row, &.{ .{ .int = 7 }, .{ .int = 0 } }));
    try testing.expect((try strict.run(row, &.{ .{ .int = 7 }, .{ .int = 2 } })).eql(.{ .int = 7 }));
    var lazy = try Evaluator.init(arena.allocator(), &store, &types, .most_defined);
    try testing.expect((try lazy.run(row, &.{ .{ .int = 7 }, .{ .int = 0 } })).eql(.{ .int = 7 }));
}

test "a switch whose arms agree has their value even on a bottom scrutinee" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    const row = try b.beginRow(&.{ i64_ty, i64_ty }, i64_ty);
    const zero = try b.litInt(i64_ty, 0);
    const c = try b.call(.i64, .is_lt, &.{ zero, try b.call(.i64, .div_trunc, &.{ Ref.rowParam(0), Ref.rowParam(1) }) });
    const arm0 = try b.openArm(c, 0);
    try b.close(.{ .value = &.{Ref.rowParam(0)} });
    const arm1 = try b.openArm(c, 1);
    try b.close(.{ .value = &.{Ref.rowParam(0)} });
    const sw = try b.switchOn(c, &.{ arm0, arm1 }, &.{}, &.{i64_ty}, &.{});
    try b.endRow(.{ .value = &.{sw} });

    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var lazy = try Evaluator.init(arena.allocator(), &store, &types, .most_defined);
    try testing.expect((try lazy.run(row, &.{ .{ .int = 5 }, .{ .int = 0 } })).eql(.{ .int = 5 }));
    var strict = try Evaluator.init(arena.allocator(), &store, &types, .strict);
    try testing.expectError(error.Crash, strict.run(row, &.{ .{ .int = 5 }, .{ .int = 0 } }));
}

test "a for-range loop sums its indices" {
    var store = ir.Store.init(testing.allocator);
    defer store.deinit();
    var types = types_mod.Types.init(testing.allocator);
    defer types.deinit();
    var b = builder_mod.Builder.init(testing.allocator, &store, &types);
    defer b.deinit();
    const i64_ty = try types.intTy(.i64);
    const row = try b.beginRow(&.{i64_ty}, i64_ty);
    const zero = try b.litInt(i64_ty, 0);
    const body = try b.openRegion(.loop_body, &.{ i64_ty, i64_ty });
    const next = try b.call(.i64, .plus, &.{ Ref.regionParam(body, 1), Ref.regionParam(body, 0) });
    try b.close(.{ .continue_ = &.{next} });
    const loop = try b.loopOf(.for_range, &.{ zero, Ref.rowParam(0), zero }, body, &.{i64_ty});
    try b.endRow(.{ .value = &.{loop} });

    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var strict = try Evaluator.init(arena.allocator(), &store, &types, .strict);
    try testing.expect((try strict.run(row, &.{.{ .int = 5 }})).eql(.{ .int = 10 }));
}

test "wrapping arithmetic wraps at the type's width" {
    try testing.expectEqual(@as(i256, -128), prims.wrapTo(.i8, 128));
    try testing.expectEqual(@as(i256, 0), prims.wrapTo(.u8, 256));
    try testing.expectEqual(@as(i256, 255), prims.wrapTo(.u8, -1));
}
