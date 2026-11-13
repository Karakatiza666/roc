//! Reification normal form: the IR, its builder, and the passes over it.
//!
//! `roc-reify-normalization-plan.md` is the plan this module implements. The
//! module depends on no compiler stage, so its tests build graphs directly.

pub const ir = @import("ir.zig");
pub const types = @import("types.zig");
pub const prims = @import("prims.zig");
pub const rules = @import("rules/table.zig");
pub const ledger = @import("rules/ledger.zig");
pub const builder = @import("builder.zig");
pub const eval = @import("eval.zig");
pub const verify = @import("verify.zig");
pub const dump = @import("dump.zig");
pub const polarity = @import("polarity.zig");
pub const measure = @import("measure.zig");
pub const digest = @import("digest.zig");
pub const identity = @import("identity.zig");
pub const equal = @import("equal.zig");
pub const driver = @import("driver.zig");
pub const rows = @import("rows.zig");
pub const views = @import("views.zig");
pub const provenance = @import("provenance.zig");
pub const live = @import("live.zig");
pub const place = @import("place.zig");
pub const match = @import("match.zig");
pub const rebuild = @import("rebuild.zig");
pub const number = @import("number.zig");
pub const loops = @import("loops.zig");
pub const scalar = @import("scalar.zig");
pub const ranges = @import("ranges.zig");
pub const laws = @import("laws.zig");
pub const lists = @import("lists.zig");
pub const fuzz_gen = @import("fuzz_gen.zig");

/// The normal-form version (I11). The rules, the speculatable lists and the
/// builtin table change only with it, so a `Code` value carries it and a
/// translator can put it in a cache key. `recorded` pins the fingerprint
/// each version was recorded with.
pub const normal_form_version: u32 = 45;

/// A fingerprint of what the normal-form version covers: the rule table,
/// the builtin table with its speculatable list, the speculatable list of
/// the ops, the kinds of value a node reads, the kinds of crash, and the
/// rules that are algorithms.
pub fn fingerprint() u64 {
    var h = std.hash.Wyhash.init(0);
    h.update(std.mem.asBytes(&rules.fingerprint()));
    h.update(std.mem.asBytes(&prims.fingerprint()));
    for (std.enums.values(ir.Op)) |op| {
        h.update(@tagName(op));
        h.update(@tagName(builder.opSpeculatable(op)));
    }
    for (std.enums.values(ir.Ref.Kind)) |kind| h.update(@tagName(kind));
    for (std.enums.values(ir.RecordForm)) |form| h.update(@tagName(form));
    for (std.enums.values(ir.CrashKind)) |kind| h.update(@tagName(kind));
    for (std.enums.values(builder.Algorithm)) |a| h.update(@tagName(a));
    for (loops.steps) |step| h.update(step);
    for (scalar.steps) |step| h.update(step);
    // The conditions `speculatable` and `speculatable_rest` read the cone.
    h.update("speculatable reads the operand cone");
    // V3: the `outline` view, its K, its selection order and its hole numbering.
    h.update("outline: cones, shapes by first-occurrence holes, (occurrences x (size - 1)) then size then shape");
    h.update(std.mem.asBytes(&views.outline_min_size));
    // V3b: places grouped by keys to depth D and generalized by
    // anti-unification, under the rules that keep meaning.
    h.update("outline: keys to depth D, then at depth D with literal values, least general generalization, a hole moves only a speculatable value, literals that differ are a hole, c(s - 1) - ch then s then shape then place then depth");
    h.update(std.mem.asBytes(&views.outline_key_depth));
    // M10: layer L, the laws a `Code.Lawful(f)` site opts into.
    for (laws.steps) |step| h.update(step);
    // A region's loops that can return, read or not, are in its digest and
    // its structural comparison (`live.exits`).
    h.update("a region's digest and comparison read its loops that can return");
    // M11: N13u's sources and the rules that read them, N8k's result ranges,
    // N11l on `while $i <= n` under a bounded `n`, a checked `plus` chain,
    // and N15c's parameter half with N7b over two root parameters.
    h.update("N13u: literals, tests against a literal, ForRange indices, interval arithmetic, N8k result ranges; decided comparisons, proved checked arithmetic speculatable within its facts, checked plus chains, inclusive ForRange; root parameters in parameter order in N15c and N7b");
    // M13: the translator's declared cut (I14). A function in it is a `Prim`
    // by its qualified name (N8h); every other function, in any package, is
    // walked by its body (N8l), and so is a computed value of any package.
    h.update("N8h: a function in the cut of the site's translator, code_primitives, is a Prim named by the nominal it is an item of and the item; N8l: every other function and computed value, in any package, is walked by its body");
    // I14: the translator of a site is the function the call it is an
    // argument of names, a direct call's callee or a method call's target.
    h.update("I14: a site's translator is the callee of the direct call or the target of the method call the site is an argument of");
    // M17: known lists (N17), and B.
    for (lists.steps) |step| h.update(step);
    h.update(std.mem.asBytes(&lists.max_unrolled));
    // 2.1: one spelling per type.
    h.update("T1: a nominal is Recursive exactly where the nearest enclosing Named of its name is the same type; T2: a node's type, and the backing an Unwrap gives, are spelled from their own root");
    // N15a over a checked `plus`: monotone in the intervals.
    h.update("N15a: an operand with an empty interval adds nothing to a checked plus chain's bounds");
    // 2.1 over instances: T1 closes a nominal only under its own instance.
    h.update("T1: a nominal closes only where the nearest enclosing nominal of its name is the same instance, and expands again under another; a type whose T1 tree is infinite is refused");
    // F2, F3: identity. A package function is a primitive by its definition,
    // and the builtin table names builtins only; a nominal is a type by its
    // declaration as well as its name.
    h.update("N8h: a Prim of a package function is its definition, and only a builtin's export name reads the builtin table; a Named or Opaque type of a declared nominal is its declaration and its name");
    // Rule L (opaque proposal Stage 0.4, F9): a structural tag union that a
    // `row_coerce` lifts into a nominal is a `Wrap`; a lift below a payload
    // is the `match` that does it.
    h.update("L: a lift into a nominal is a Wrap of the value at its own type; a lift below a tag payload or a nominal's backing is a Switch whose arms rebuild each tag at the destination; [False, True] at Bool is a Switch to the two literals");
    // D1, D3 (opaque proposal Stage 1): one classification of every callee
    // and constant, the same in each path.
    h.update("N8h D1: a function or top-level constant whose checked type mentions a :: nominal its module declares is a Prim by its qualified name in every call form, a constant one with no arguments; a constant in the cut is a Prim with no arguments; a cut lists no primitive");
    // D4, Q10 (opaque proposal Stage 1): a `Prim` carries its `PrimId` and
    // an `Opaque` its `TypeId`; a builtin `Opaque` is named as its
    // functions' `Prim` owner is.
    h.update("D4: a Prim carries the PrimId of its definition and an Opaque the TypeId of its nominal; Q10: a builtin Opaque is named as its Prim owner, without Builtin.");
    // Q10: a nominal of the builtin module is a builtin, by the module's
    // role, whether or not the checker marks it as one (`Hasher`).
    h.update("Q10: every nominal the builtin module declares is a builtin type, named as its Prim owner, by the role of the module its identity names");
    // D7 (opaque proposal Stage 1.10, F8): a `Prim` carries the evidence
    // the checker recorded for each `where` requirement of its scheme.
    h.update("D7: a Prim carries, per where requirement of its scheme in checked order, the method the checker chose: a Prim with its own evidence, a Row of the site, Derived, or Unreachable; an answer the checker left to a later stage is refused");
    // D7 after Stage 1.10: a primitive the compiler's own derivation reached
    // has no recorded evidence by construction, and the method registry
    // answers each requirement at the dispatcher its receiver fixes.
    h.update("D7: a Prim a derivation reached carries, per where requirement, the registry's answer at the dispatcher the receiver fixes, by the checker's rule: a nominal's target, Derived for a structural target or for equality or hash on a structural shape; a type variable, a composite dispatcher, an undeclared method and a codec or map on a structural shape are refused");
    // D7, a forwarded requirement whose shared slot names a walked target:
    // the dispatcher fixes the target row's instance.
    h.update("D7: a forwarded requirement that shares its slot's target builds a Row target at the instance the dispatcher fixes; a row variable stays unbound; a variable only the rest of the callable fixes is refused");
    // N11j over N5b: a value outside the loop is one N5b hoists out of it,
    // a speculatable node that owns regions included.
    h.update("N11j: a Break value is outside the loop where N5b hoists it, and a speculatable node that owns regions moves with them when what they read from outside them is outside the loop");
    // D5 (structural proposal Stage 3): a record field's presence carries
    // its default, and the default is part of the type.
    h.update("D5: a field with a default is Default(value) where the walk describes the default as a literal or an aggregate, tag or nominal of literals, and DefaultComputed otherwise; the default is part of the record type");
    // Q18 (structural proposal): a record literal that leaves out a field
    // with a default the type carries is the record with that field set to
    // the default's literal; one whose default is computed is refused.
    h.update("Q18: a record literal that leaves out a field whose presence is Default(value) sets the field to the literal of the value; one whose default is computed is refused");
    // A default that is an embedded file fills as one Lit(Bytes), the same
    // literal that the file gives where it is written.
    h.update("Q18 bytes: a default that is an embedded List(U8) fills as one Lit(Bytes), as the file does where it is written; Code.Ty spells it as a List of Int");
    // Y8 (structural proposal): a `Named` carries its nominal's type
    // arguments, inside it as its backing is, so they are part of the type.
    h.update("T1 args: a Named carries the type arguments of its nominal, in declaration order, inside the nominal as its backing is; two nominals that differ only in an argument differ, and an argument widens as the backing does");
    // A derived `==` over a record compares its fields in label order, and
    // an optional field through its `OptField`, as the compiler compares
    // the field's tagged slot. A derived hash of a record with an optional
    // field is `Derived`.
    h.update("N1k fields: a derived == over a record is And over its fields in label order; an optional field is a Switch on the OptField of each operand, Ok and Ok compare the values, Err and Err are True, the other arms False; a derived to_hash over a record that holds an optional field is Derived");
    // N18e: a captured value the root reads whole is one slot, and its
    // projections are nodes over that slot.
    h.update("N18e: among the slots the root reads, a slot that is a projection of another is no slot; the outermost slot it is a projection of is read whole, and Field, Index and Unwrap of a whole slot are nodes over its Input");
    // The kinds of literal. The operand the compiler hands to a
    // `from_numeral` conversion is one `Numeral` literal, at a row's
    // parameter and at a `Prim`'s alike.
    for (std.enums.values(std.meta.Tag(ir.LitValue))) |kind| h.update(@tagName(kind));
    h.update("N1i numeral: the operand of a from_numeral conversion is one Numeral literal of the sign and digits the source spells, at the type of the conversion's parameter, for a row and a Prim alike");
    // N5 in the number stage: a literal is placed by the readers it has.
    h.update("N5: in the number stage a literal is one copy per region that reads it and that no other such region encloses, hoisted and merged by N5c as any node");
    // N15a over a checked `plus` reads the operands of the settle round.
    h.update("N15a: a checked plus chain flattens only in the settle round, the round after one that changed nothing in the component");
    // N13d through a negation: an earlier operand `Bool.not(x)` decides `x`.
    h.update("N13d: an earlier And or Or operand that is Bool.not(x) decides x the other way; an arm of a switch on Bool.not(x) does not");
    return h.final();
}

/// One released normal-form version and the fingerprint it was recorded with.
const Recorded = struct { version: u32, fingerprint: u64 };

/// Every version, oldest first. A change to the rules, the builtin table or
/// the ops' speculatable list adds an entry here with a new
/// `normal_form_version`; an entry is never edited.
const recorded = [_]Recorded{
    .{ .version = 1, .fingerprint = 0x5a5d7334dda2ac80 },
    // M2: `Payload` and `Elem` are not speculatable, and placement and
    // numbering are canonical.
    .{ .version = 2, .fingerprint = 0x12998df01d3edf85 },
    // M3: `Apply`, rows finalized before their callers with digests and
    // first-read parameters, and the `graph` view.
    .{ .version = 3, .fingerprint = 0x8b7cdb45472514a6 },
    // M4: input slots, the captured run-time values a root reads (N18), and
    // the kinds of value a node reads in the fingerprint.
    .{ .version = 4, .fingerprint = 0xc85b7416400dd35c },
    // M5: a `Record` node may leave an optional member unset, and says which
    // members it sets (`ir.RecordForm`).
    .{ .version = 5, .fingerprint = 0x087a981c03021a8a },
    // M4: a switch on `Str` equality against a literal is a literal switch
    // keyed by the string (N13n over `Str`), so the arms of a `match` on
    // string literals meet in any order (N7a, `match.zig`).
    .{ .version = 6, .fingerprint = 0x4664538352b123b1 },
    // M5 of the plan: literals of floats, `Str` and chains fold (N13j, N13k),
    // chains of `Str.concat` and `List.concat` flatten (N15a), a `Str`
    // literal goes last in an equality (N15c), and the hand-written
    // algorithms N7b, N13m, N13r and N13d over `Bool.not` run.
    .{ .version = 7, .fingerprint = 0x27ea5d8c8ceef391 },
    // M6 of the plan: three canonical loop forms. A row whose every call to
    // itself is a tail call is a `Loop` (N12); a loop's invariant, dead and
    // equal slots and unread outputs go (N11g to N11j); a loop over
    // `List.iter(xs)` is `ForList(xs)` (N11k); a counter `Loop` is a
    // `ForRange` and `ForRange(0, List.len(xs))` is `ForList(xs)` (N11l). A
    // general `Loop` has outputs of its own, apart from its slots.
    .{ .version = 8, .fingerprint = 0x97ad1e35a8feb8fb },
    // M7 of the plan: a record or tuple that a non-root row only reads by
    // field or index is one parameter per component, and a loop slot the
    // body only reads that way and every `Continue` gives as a construction
    // is one slot per component (N14a, N14b).
    .{ .version = 9, .fingerprint = 0x2255e015149a57ec },
    // Fix of T1.11: the speculatable conditions of the rules hold only when
    // the operand and every node it reads are speculatable, so `x - x` over
    // a field of a loop output keeps the loop.
    .{ .version = 10, .fingerprint = 0xb436a740a244c612 },
    // N13w: a crash records who wrote it (`ir.CrashKind`), and a switch on
    // the output of a value switch whose every value but one reaches a
    // rejected literal's crash switches on the one value. The rules that are
    // algorithms are in the fingerprint.
    .{ .version = 11, .fingerprint = 0xd2ffdfc061a21e95 },
    // M9 of the plan: the `outline` view (V3), which makes a row of every
    // computation of at least K nodes that repeats, and its K.
    .{ .version = 12, .fingerprint = 0x111ad83eee8dde24 },
    // M10 of the plan: layer L (N16a to N16f), which a `Code.Lawful(f)` site
    // opts into, the builtins its laws read in the builtin table, with
    // `List.is_empty` speculatable, and the `Iter.map` role.
    .{ .version = 13, .fingerprint = 0x2fc706afc0671f11 },
    // Fix: a region's digest and its structural comparison read the loops
    // in it that can return, read or not, so a helper with such a loop no
    // longer merges with one without it, an `if` whose arms differ only in
    // such a loop keeps both arms, and two merged rows pair their nodes for
    // provenance by the comparison (N8g, N10).
    .{ .version = 14, .fingerprint = 0xcbb8426dfd39556b },
    // V3b: `outline` matches places by anti-unification, so places that
    // differ in a value, a differing literal among them, are one row whose
    // parameter is that value, and a hole moves only a speculatable value
    // out of an arm or a loop body. Places are grouped by keys to depth D.
    .{ .version = 15, .fingerprint = 0xf9ae43f95561a55e },
    // M11 of the plan: literal intervals (N13u) from literals, tests against
    // a literal, `ForRange` indices, interval arithmetic and the result
    // ranges of finalized rows (N8k). A comparison an interval decides is a
    // literal, a checked op proved to fit is speculatable within its facts,
    // a checked `plus` chain proved to fit is one `Prim`, and `while $i <= n`
    // with `n` below its type's highest value is an inclusive `ForRange`.
    // Two root parameters go in parameter order (N15c), in an operation and
    // in a decision tree (N7b).
    .{ .version = 16, .fingerprint = 0xe01423990801bff4 },
    // M12 of the plan: facts across loop turns. A general `Loop`'s leading
    // `Bool` test that every edge decides is gone (N11n), and a counter
    // stepped with a bounded loop's index is the index plus its start
    // (N11o). N11l raises a loop whose `Break` gives some of the other
    // slots, and the number stage merges what the hoist brings into every
    // arm (N5c).
    .{ .version = 17, .fingerprint = 0x666aa601711352db },
    // M13 of the plan: a translator declares its cut with the item
    // `code_primitives` of its type (I14). A function in the cut is a `Prim`
    // named by its qualified name, in any package (N8h), and every other
    // function and computed value, in any package, is walked by its body
    // (N8l).
    .{ .version = 18, .fingerprint = 0xcd9bd93efff0ff8c },
    // Fix: a site passed to a translator called as a method takes the cut
    // of the method's type, as its direct call does (I14).
    .{ .version = 19, .fingerprint = 0x9c643e7520951391 },
    // M17 of the plan: known lists (N17). A list builtin over a `List` node
    // is what its body in `Builtin.roc` computes: a literal length, the
    // element or the `Err` tag, a literal switch on an index that is not a
    // literal, the `List` node of the result, the calls of a known function,
    // or the `plus` chain of a sum. A `ForList` over a `List` node of at most
    // B = 16 elements whose every path continues is its body once per
    // element. The builtin table holds the list builtins N17 reads.
    .{ .version = 20, .fingerprint = 0x8a67c5235ae7e495 },
    // Fix: one recursive type has one spelling (2.1, T1 and T2). A cycle
    // through two nominals closes where the nearest enclosing nominal of the
    // name is the same type, however the walk entered the cycle, and the
    // backing an `Unwrap` gives is spelled from its own root.
    .{ .version = 21, .fingerprint = 0x36f06b3039448e99 },
    // Fix: N15a's condition on a checked `plus` chain is monotone in the
    // intervals. An operand with an empty interval, which always crashes
    // where it is read, adds nothing to the chain's bounds.
    .{ .version = 22, .fingerprint = 0x032a7bb4ace86414 },
    // Fix: a nominal closes only where the nearest enclosing nominal of its
    // name is the same instance (2.1, T1). Under another instance of its
    // name it expands again, and a type whose T1 tree is infinite, such as
    // `Pair(a, b) := [Leaf(a), Node(Pair(b, a))]`, is refused.
    .{ .version = 23, .fingerprint = 0x8737202fc6def1b1 },
    // After M17: interpolated literals. N17f takes `List.fold_with_index`
    // with a known function, and N13c decides `Try.ok_or` of a known tag.
    // The builtin table holds both, with the owner `Try`.
    .{ .version = 24, .fingerprint = 0x9898752b433f4708 },
    // Opaque proposal Stage 0 (F2, F3): a function of a package is a `Prim`
    // keyed by its definition, so two packages' functions of one name are
    // two primitives, and the builtin table is read only for a builtin's
    // export name. A `Named` or `Opaque` type of a nominal a module declares
    // is keyed by that declaration, so two packages' `Time` are two types.
    // Their digests differ.
    .{ .version = 25, .fingerprint = 0x2cf5f3900fc6d33d },
    // Opaque proposal Stage 0.4 (F9), rule L: where a `row_coerce` lifts a
    // structural tag union into a nominal, the value keeps its own type and
    // a `Wrap` of the nominal stands around it. A lift below a tag payload
    // or a nominal's backing is the `match` that does it.
    .{ .version = 26, .fingerprint = 0x3d9982e373199a84 },
    // Opaque proposal Stage 1 (D1, D3): a function or a top-level constant of
    // a module that declares an opaque type, whose type mentions that type,
    // is a `Prim` named by its qualified name whichever path reaches it; a
    // constant can be in a cut, and is then a `Prim` with no arguments.
    .{ .version = 27, .fingerprint = 0xd77b4d804e8284b8 },
    // Opaque proposal Stage 1 (D4, D6, Q10): a `Prim` carries the `PrimId` of
    // its definition and an `Opaque` the `TypeId` of its nominal, the ids
    // `Code.prim` and `Code.type_id` give. A builtin `Opaque` is named as the
    // owner of its functions' `Prim`s: `Dict`, not `Builtin.Dict`.
    .{ .version = 28, .fingerprint = 0xab98f95421034f8a },
    // Opaque proposal Q10: every nominal the builtin module declares, known
    // by the role of its module, is a builtin type. `Hasher` and
    // `Code.PrimId`, which the checker marks as no builtin, are named
    // `Hasher` and `Code.PrimId` and carry the builtin `TypeId`.
    .{ .version = 29, .fingerprint = 0xbdbe87f49c03182e },
    // Opaque proposal Stage 1.10 (D7, F8): a `Prim` carries `evidence`, the
    // method the checker chose for each `where` requirement of its scheme,
    // so `List.sort` over `I64`, over an opaque type and over a nominal with
    // a written order are three descriptions. A row the evidence names is a
    // row of the site.
    .{ .version = 30, .fingerprint = 0x3d0a61a98f41bee0 },
    // D7 after Stage 1.10: a `==` the compiler derives over a record that
    // holds a `List`, a `Dict` or a `Try` reaches that type's `is_eq` with no
    // recorded evidence. Its requirements are answered by the method
    // registry at the element types the receiver fixes, where 30 refused it.
    .{ .version = 31, .fingerprint = 0xf11a44fc65aa8aa0 },
    // D7: a generic helper's `List.sort` that forwards `item.Sort` to the
    // order its caller supplied names a written order's row, built at the
    // instance the dispatcher fixes, where 31 refused it.
    .{ .version = 32, .fingerprint = 0x4a1c5394adbf5ffb },
    // Fix: N11j reads a `Break` value as outside the loop exactly where N5b
    // hoists it. A speculatable switch over values outside the loop, such as
    // a `match` on a parameter in the exiting arm of a tail-recursive helper,
    // is the loop's output, so the number stage leaves no loop N11j matches.
    .{ .version = 33, .fingerprint = 0x9754e6b9238e28af },
    // Structural proposal Stage 3 (D5): `Code.Ty` record presence is
    // `[Required, Optional, Default(Value), DefaultComputed]`. A default the
    // walk describes as a literal, or as a list, record, tuple, tag or
    // nominal of literals, is `Default` of its `Code.Value`; any other is
    // `DefaultComputed`. Two types that differ only in a default differ.
    .{ .version = 34, .fingerprint = 0x0b6e0eebee7c2c75 },
    // Structural proposal Q18: a record literal that leaves out a field
    // whose presence is `Default(value)` is described with the field set to
    // the literal of the value, where 34 refused it; a field whose default
    // is computed stays refused, with a report that says so.
    .{ .version = 35, .fingerprint = 0xc6662b1789c6782e },
    // Structural proposal Y8: `Code.Ty.Named(name, args, backing)` carries
    // the nominal's type arguments, inside it as its backing is. A type
    // argument the backing does not hold (`Id(row) := { table : Str, key :
    // Str }`) is part of the type, so `Id(Customer)` and `Id(Product)` are
    // two types, and a captured `Id` holds no value of its row.
    .{ .version = 36, .fingerprint = 0xd6db7f7fa9425675 },
    // A derived `==` over a record compares the fields in label order,
    // whatever links the checker made in the row, and an optional field
    // through its `OptField`: equal where both records hold it with equal
    // values and where neither holds it, as the compiler's derived `is_eq`
    // compares the field's tagged slot. 36 read an optional field as a
    // required one. A derived hash of a record that holds an optional field
    // is `Derived`.
    .{ .version = 37, .fingerprint = 0x50552bd86a9ae2e9 },
    // N18e: a captured value that the root reads whole, by an `OptField`,
    // as a call argument or as a value it builds or returns, is one slot,
    // and the root reads each field, item or backing of it as `Field`,
    // `Index` or `Unwrap` of that slot's `Input`. 37 bound such a value once
    // whole and again once per path it read.
    .{ .version = 38, .fingerprint = 0x1726bd1adee3761e },
    // `Code.Lit.Numeral`: the operand the compiler hands to a `from_numeral`
    // conversion is one literal of the `Num.Numeral` the source spells, at
    // the type of the conversion's parameter. 38 built a row's operand as a
    // `Wrap` of the `Literal` tag of its record, and gave a `Prim` an `I128`
    // or an `F64` literal, which rounded a fraction.
    .{ .version = 39, .fingerprint = 0xbfb96608d365d5e4 },
    // The builtin table holds each integer type's `from_numeral` and the
    // accessors of `Num.Numeral` (`is_negative`, `digits_before_pt`,
    // `digits_after_pt`, `digits_after_pt_count`). None is speculatable and
    // no rule folds them; 39 named them as primitives the table lacked.
    .{ .version = 40, .fingerprint = 0x7d6e4eba36cde9bd },
    // N17h: known iterators. `Iter.fold` with a known function and
    // `List.from_iter` over `List.iter` of a `List` node, through
    // `Iter.iter`, `Iter.with_index` and `Iter.map` with a known function,
    // are the chain of calls and the `List` node of the items, and
    // `Iter.with_index` of `List.iter` of a `List` node is `List.iter` of
    // the index and element tuples. The builtin table holds `Iter.fold`,
    // `Iter.with_index` and `List.from_iter`.
    .{ .version = 41, .fingerprint = 0xd772a3d839ba0ad4 },
    // Q18 bytes: a field default that is an embedded file fills a record
    // literal that leaves out the field as one `Lit(Bytes)`, the same
    // literal that the file gives where it is written. 41 built a `List` of
    // one `Lit(Int)` per byte.
    .{ .version = 42, .fingerprint = 0x3428c8ade88a95ae },
    // Fix: the number stage places a literal by the readers that remain,
    // one copy per region that reads it and that no other such region
    // encloses, and N5c merges the copies every arm holds. A literal the
    // walk merged into a node a later round removed kept that node's place.
    .{ .version = 43, .fingerprint = 0xfe5b05583d6d4e6a },
    // Fix: N15a flattens a checked `plus` chain only in the settle round,
    // the round after one that changed nothing. 43 flattened it in any
    // round, over an inner `plus` that a later round folds to a literal.
    .{ .version = 44, .fingerprint = 0xc5ea50df69ce9583 },
    // Fix: an earlier `And` or `Or` operand `Bool.not(x)` decides `x` the
    // other way (N13d), so `!c and c` is `False` and `!c or c` is `True`, as
    // `if c False else c` and `if c True else !c` are.
    .{ .version = 45, .fingerprint = 0xd9e3a2de85a63c68 },
};

const std = @import("std");

test "the normal-form version changes exactly when the rules, the builtin table or the ops' speculatable list do" {
    const last = recorded[recorded.len - 1];
    try std.testing.expectEqual(normal_form_version, last.version);
    try std.testing.expectEqual(last.fingerprint, fingerprint());
    for (recorded[1..], recorded[0 .. recorded.len - 1]) |later, earlier| {
        try std.testing.expect(later.version > earlier.version);
        try std.testing.expect(later.fingerprint != earlier.fingerprint);
    }
}

test "reify tests" {
    std.testing.refAllDecls(@import("ir.zig"));
    std.testing.refAllDecls(@import("types.zig"));
    std.testing.refAllDecls(@import("prims.zig"));
    std.testing.refAllDecls(@import("identity.zig"));
    std.testing.refAllDecls(@import("rules/table.zig"));
    std.testing.refAllDecls(@import("rules/ledger.zig"));
    std.testing.refAllDecls(@import("builder.zig"));
    std.testing.refAllDecls(@import("eval.zig"));
    std.testing.refAllDecls(@import("verify.zig"));
    std.testing.refAllDecls(@import("dump.zig"));
    std.testing.refAllDecls(@import("polarity.zig"));
    std.testing.refAllDecls(@import("measure.zig"));
    std.testing.refAllDecls(@import("digest.zig"));
    std.testing.refAllDecls(@import("equal.zig"));
    std.testing.refAllDecls(@import("driver.zig"));
    std.testing.refAllDecls(@import("rows.zig"));
    std.testing.refAllDecls(@import("views.zig"));
    std.testing.refAllDecls(@import("provenance.zig"));
    std.testing.refAllDecls(@import("live.zig"));
    std.testing.refAllDecls(@import("place.zig"));
    std.testing.refAllDecls(@import("match.zig"));
    std.testing.refAllDecls(@import("rebuild.zig"));
    std.testing.refAllDecls(@import("number.zig"));
    std.testing.refAllDecls(@import("loops.zig"));
    std.testing.refAllDecls(@import("scalar.zig"));
    std.testing.refAllDecls(@import("ranges.zig"));
    std.testing.refAllDecls(@import("laws.zig"));
    std.testing.refAllDecls(@import("lists.zig"));
    std.testing.refAllDecls(@import("fuzz_gen.zig"));
}
