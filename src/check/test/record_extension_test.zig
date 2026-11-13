//! Tests for Record Extension Well-Formedness (design.md): a record extension
//! slot `..r` accepts a record, a row variable, an alias of a record, or a
//! record-backed `:=` nominal. It refuses a `::` opaque type in every module
//! and every other type, whether an annotation writes the type into the slot
//! or unification brings it there. Both sides are pinned here.

const TestEnv = @import("./TestEnv.zig");

fn expectRefused(source: []const u8, title: []const u8) TestEnv.TestEnvError!void {
    var test_env = try TestEnv.init("Test", source);
    defer test_env.deinit();
    try test_env.assertOneTypeError(title);
}

fn expectAccepted(source: []const u8) TestEnv.TestEnvError!void {
    var test_env = try TestEnv.init("Test", source);
    defer test_env.deinit();
    try test_env.assertNoErrors();
}

const record_row_hint = "stands in a record extension";

// Record-row parameters of a declaration

test "record extension: the record-row parameters of a declaration" {
    var test_env = try TestEnv.init("Test",
        \\Ref(r) := { ..r }
        \\P(a, r) := { x : a, ..r }
        \\W(a) := Ref(a)
        \\Box2(a) := { inner : a }
    );
    defer test_env.deinit();
    try test_env.assertNoErrors();
    try test_env.assertNominalRecordRowFormals("Ref", &.{true});
    try test_env.assertNominalRecordRowFormals("P", &.{ false, true });
    try test_env.assertNominalRecordRowFormals("W", &.{true});
    try test_env.assertNominalRecordRowFormals("Box2", &.{false});
}

// Refused: an annotation writes a type that is not a record row

test "record extension: Str in a nominal's extension is refused" {
    try expectRefused(
        \\Ref(r) := { ..r }
        \\
        \\show : Ref(Str) -> Str
        \\show = |_x| "ok"
    , "Not A Record Extension");
}

test "record extension: a tag union in a nominal's extension is refused" {
    try expectRefused(
        \\Ref(r) := { ..r }
        \\
        \\show : Ref([A, B]) -> Str
        \\show = |_x| "ok"
    , "Not A Record Extension");
}

test "record extension: a builtin opaque type in a nominal's extension is refused" {
    try expectRefused(
        \\Ref(r) := { ..r }
        \\
        \\show : Ref(Dict(Str, Str)) -> Str
        \\show = |_x| "ok"
    , "Not A Record Extension");
}

test "record extension: a nominal whose backing is not a record is refused" {
    try expectRefused(
        \\Ref(r) := { ..r }
        \\U := U64
        \\
        \\show : Ref(U) -> Str
        \\show = |_x| "ok"
    , "Not A Record Extension");
}

test "record extension: an opaque type is refused in its own module" {
    var test_env = try TestEnv.init("Test",
        \\Ref(r) := { ..r }
        \\Own :: { id : Str, name : Str }
        \\
        \\name_of : Ref(Own) -> Str
        \\name_of = |o| o.name
    );
    defer test_env.deinit();
    try test_env.assertOneTypeProblemMsgContains("Not A Record Extension", "This is an opaque type");
}

test "record extension: an opaque type of another module is refused" {
    var opq_env = try TestEnv.init("Opq",
        \\Opq :: { id : Str, name : Str }.{
        \\    mk : Str -> Opq
        \\    mk = |n| { id: "1", name: n }
        \\}
    );
    defer opq_env.deinit();
    try opq_env.assertNoErrors();

    var test_env = try TestEnv.initWithImport("Test",
        \\import Opq
        \\
        \\Ref(r) := { ..r }
        \\
        \\name_of : Ref(Opq) -> Str
        \\name_of = |o| o.name
    , "Opq", &opq_env);
    defer test_env.deinit();
    try test_env.assertOneTypeProblemMsgContains("Not A Record Extension", "This is an opaque type");
}

test "record extension: a local annotation is refused" {
    try expectRefused(
        \\Ref(r) := { ..r }
        \\
        \\show : I64 -> Str
        \\show = |_n| {
        \\    x : Ref(Str)
        \\    x = crash "never"
        \\    _y = x
        \\    "ok"
        \\}
    , "Not A Record Extension");
}

test "record extension: a nominal that forwards its parameter to an extension is refused at Str" {
    try expectRefused(
        \\Ref(r) := { ..r }
        \\W(a) := Ref(a)
        \\
        \\show : W(Str) -> Str
        \\show = |_x| "ok"
    , "Not A Record Extension");
}

test "record extension: an alias whose extension is Str is refused" {
    try expectRefused(
        \\Ext(r) : { z : I64, ..r }
        \\
        \\show : Ext(Str) -> Str
        \\show = |_x| "ok"
    , "Not A Record Extension");
}

// Refused: unification brings a type that is not a record row into the slot

test "record extension: a call that fixes a row variable to Str is refused" {
    var test_env = try TestEnv.init("Test",
        \\wrap : r -> { z : I64, ..r }
        \\wrap = |_x| crash "never"
        \\
        \\use_str : Str -> I64
        \\use_str = |s| wrap(s).z
    );
    defer test_env.deinit();
    try test_env.assertOneTypeProblemMsgContains("Type Mismatch", record_row_hint);
}

test "record extension: a call that fixes a nominal's record-row argument to Str is refused" {
    var test_env = try TestEnv.init("Test",
        \\Ref(r) := { ..r }
        \\
        \\wrap : r -> Ref(r)
        \\wrap = |_x| crash "never"
        \\
        \\use_str : Str -> Str
        \\use_str = |s| {
        \\    _y = wrap(s)
        \\    s
        \\}
    );
    defer test_env.deinit();
    try test_env.assertOneTypeProblemMsgContains("Type Mismatch", record_row_hint);
}

test "record extension: a literal in a row slot is refused" {
    var test_env = try TestEnv.init("Test",
        \\wrap : r -> { z : I64, ..r }
        \\wrap = |_x| crash "never"
        \\
        \\use_lit : I64 -> I64
        \\use_lit = |_n| wrap("x").z
    );
    defer test_env.deinit();
    try test_env.assertOneTypeProblemMsgContains("Type Mismatch", record_row_hint);
}

test "record extension: a rigid variable that is not a row is refused in a row slot" {
    var test_env = try TestEnv.init("Test",
        \\wrap : r -> { z : I64, ..r }
        \\wrap = |_x| crash "never"
        \\
        \\k : a -> I64
        \\k = |x| wrap(x).z
    );
    defer test_env.deinit();
    try test_env.assertOneTypeProblemMsgContains("Type Mismatch", record_row_hint);
}

// Accepted

test "record extension: a record-backed nominal extends a record" {
    try expectAccepted(
        \\Ref(r) := { ..r }
        \\Owner := { id : Str, name : Str }
        \\
        \\name_of : Ref(Owner) -> Str
        \\name_of = |o| o.name
        \\
        \\ada : Str
        \\ada = name_of(Ref.{ id: "a", name: "Ada" })
    );
}

test "record extension: a record-backed nominal extends a record with head fields" {
    try expectAccepted(
        \\Ref2(r) := { z : I64, ..r }
        \\Owner := { id : Str, name : Str }
        \\
        \\name_of : Ref2(Owner) -> Str
        \\name_of = |o| "${o.name} ${o.z.to_str()}"
    );
}

test "record extension: an alias extended by a record-backed nominal" {
    try expectAccepted(
        \\Ext(r) : { z : I64, ..r }
        \\A(r) : { ..r }
        \\Owner := { id : Str, name : Str }
        \\
        \\name_of : Ext(Owner) -> Str
        \\name_of = |o| o.name
        \\
        \\name_of_a : A(Owner) -> Str
        \\name_of_a = |o| o.name
    );
}

test "record extension: a record, an alias of a record and a row variable extend a record" {
    try expectAccepted(
        \\Ref(r) := { ..r }
        \\OwnerAlias : { id : Str, name : Str }
        \\
        \\id_of : Ref({ id : Str }) -> Str
        \\id_of = |o| o.id
        \\
        \\name_of : Ref(OwnerAlias) -> Str
        \\name_of = |o| o.name
        \\
        \\open_id : Ref({ id : Str, ..r }) -> Str
        \\open_id = |o| o.id
    );
}

test "record extension: a self link through a nominal extension" {
    try expectAccepted(
        \\Ref(r) := { ..r }
        \\Owner := { id : Str, name : Str, boss : [None, Some(Ref(Owner))] }
        \\
        \\boss_name : Owner -> Str
        \\boss_name = |o| match o.boss {
        \\    None => "none"
        \\    Some(b) => b.name
        \\}
    );
}

test "record extension: a nominal that forwards its parameter to an extension accepts a record nominal" {
    try expectAccepted(
        \\Ref(r) := { ..r }
        \\W(a) := Ref(a)
        \\Owner := { id : Str }
        \\
        \\show : W(Owner) -> Str
        \\show = |_x| "ok"
    );
}

test "record extension: a call that fixes a row variable to a record or a record nominal" {
    try expectAccepted(
        \\P := { a : I64 }
        \\
        \\wrap : r -> { z : I64, ..r }
        \\wrap = |_x| crash "never"
        \\
        \\use_rec : { a : I64 } -> I64
        \\use_rec = |s| wrap(s).z
        \\
        \\use_nom : P -> I64
        \\use_nom = |p| wrap(p).z
    );
}

test "record extension: a record update of an opaque type in its own module is unchanged" {
    try expectAccepted(
        \\P :: { x : I64, y : I64 }
        \\
        \\bump : P -> P
        \\bump = |p| { ..p, x: p.x + 1 }
    );
}

test "record extension: an unannotated record update of a record nominal is unchanged" {
    try expectAccepted(
        \\P := { x : I64, y : I64 }
        \\
        \\bump = |p| { ..p, x: 10 }
        \\
        \\q : P
        \\q = bump({ x: 1, y: 2 })
    );
}
