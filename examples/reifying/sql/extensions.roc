# A translator extension (D6 of roc-reify-opaque-proposal.md). `Stamp` is an
# opaque type of another module, so `Sql.roc` has no SQL form for its
# operations or a column type for it. An `Sql.Extension` names both by the
# identity the compiler gives them, and a captured `Stamp` is bound as the
# bytes its derived encoder writes in `Sql.Param`.
import Sql
import Stamp
import Bool as Flag

Event : { id : I64, at : Stamp }

events : Sql.Table(Event)
events = Sql.table("events")

stamp_proxy : Code.Proxy(Stamp)
stamp_proxy = Code.proxy()

## What a glue package for `Stamp` would export. `Sql.Param` writes a `Stamp`
## as bytes that sort as the stamp does, so `<` on the column is `is_lt`.
stamp_sql : Sql.Extension
stamp_sql = Sql.extension({
	prims: [{ prim: Code.prim(Stamp.is_lt), render: binary("<") }],
	types: [{ type: Code.type_id(stamp_proxy), column: "BLOB" }],
})

binary : Str -> ({ args : List(Str), evidence : List(Code.Evidence) } -> Try(Str, Str))
binary = |op| |call| match call.args {
	[a, b] => Ok("(${a} ${op} ${b})")
	_ => Err("`${op}` takes two operands")
}

## The extensions are an argument of the translator's call, so they are
## fixed while the compiler runs, as every argument but the captures is.
before : Stamp -> Try(Sql.Statement, Sql.Error)
before = |cutoff| Sql.bind_captured(Sql.select_where(events, [stamp_sql], |e| e.at < cutoff))

# The extension covers `is_lt`, and the captured stamp is a blob: 5 as an
# I128 with its sign bit flipped.
expect {
	match before(Stamp.from_nanos(5)) {
		Ok(statement) => statement.sql == "SELECT *\nFROM events\nWHERE events.at < ?1" and statement.inlined == "SELECT *\nFROM events\nWHERE events.at < X'80000000000000000000000000000005'"
		Err(_) => Bool.False
	}
}

# Without it, `Stamp.is_lt` is refused, not read as the builtin `<`.
unextended : Stamp -> Try(Sql.Statement, Sql.Error)
unextended = |cutoff| Sql.bind_captured(Sql.select_where(events, [], |e| e.at < cutoff))

expect refusal(unextended(Stamp.from_nanos(5))) == "`Stamp.is_lt` has no SQL form; pass an extension that covers it"

# An operation the extension does not cover is refused by name.
equal : Stamp -> Try(Sql.Statement, Sql.Error)
equal = |cutoff| Sql.bind_captured(Sql.select_where(events, [stamp_sql], |e| e.at == cutoff))

expect refusal(equal(Stamp.from_nanos(5))) == "`Stamp.is_eq` has no SQL form; pass an extension that covers it"

# A module's own `Bool` has a `not`, and the builtin `Bool.not` is `NOT`.
# The translator looks a call up by its id, not by its name, so the user's
# `not` is refused, not read as `NOT`.
Switch : { id : I64, on : Flag, live : Bool }

switches : Sql.Table(Switch)
switches = Sql.table("switches")

expect Sql.from(switches).select(|s| { off: s.on.not() }).to_sql() == Err(Unsupported("`Bool.not` has no SQL form; pass an extension that covers it"))

# `Flag.not` names the module's own `not`, not the builtin: the two ids
# differ, so an extension can cover the one without the other.
expect Code.prim(Flag.not) != Code.prim(Bool.not)

flag_sql : Sql.Extension
flag_sql = Sql.extension({
	prims: [
		{ prim: Code.prim(Flag.not), render: |call| Ok("(1 - ${Str.join_with(call.args, "")})") },
		{ prim: Code.prim(Flag.level), render: |call| Ok(Str.join_with(call.args, "")) },
	],
	types: [],
})

off : I64 -> Try(Sql.Statement, Sql.Error)
off = |level| Sql.bind_captured(Sql.select_where(switches, [flag_sql], |s| s.on.not().level() == level))

expect off(0).map_ok(|statement| statement.inlined) == Ok("SELECT *\nFROM switches\nWHERE (1 - switches.on) = 0")

# The builtin `not` is still `NOT` with the extension.
dead : {} -> Try(Sql.Statement, Sql.Error)
dead = |{}| Sql.bind_captured(Sql.select_where(switches, [flag_sql], |s| !s.live))

expect dead({}).map_ok(|statement| statement.inlined) == Ok("SELECT *\nFROM switches\nWHERE NOT switches.live")

# `==` on a float is `=`. `F64` derives its `is_eq`, and `Code.prim(F64.is_eq)`
# in `Sql.builtins` gives the id the call carries.
Reading : { id : I64, value : F64 }

readings : Sql.Table(Reading)
readings = Sql.table("readings")

at_half : {} -> Try(Sql.Statement, Sql.Error)
at_half = |{}| Sql.bind_captured(Sql.select_where(readings, [], |r| r.value == 0.5))

expect at_half({}).map_ok(|statement| statement.sql) == Ok("SELECT *\nFROM readings\nWHERE readings.value = 0.5")

refusal : Try(Sql.Statement, Sql.Error) -> Str
refusal = |result| match result {
	Err(Unsupported(message)) => message
	Err(BadSchema(message)) => message
	Ok(_) => ""
}

# A transparent capture next to it is bound as before.
after_id : I64, Stamp -> Try(Sql.Statement, Sql.Error)
after_id = |least, cutoff| Sql.bind_captured(Sql.select_where(events, [stamp_sql], |e| e.id >= least and e.at < cutoff))

expect {
	match after_id(7, Stamp.from_nanos(-1)) {
		Ok(statement) => statement.inlined == "SELECT *\nFROM events\nWHERE (7 <= events.id) AND (events.at < X'7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF')"
		Err(_) => Bool.False
	}
}

# A column of an opaque type takes its SQL type from the extension.
create_events : List(Sql.Extension) -> Sql.Migration
create_events = |extensions| Sql.migration("001_events", [events.create_with(extensions, |e| { id: e.id, at: e.at }).primary_key(|e| e.id).done()])

expect Sql.migrate([create_events([stamp_sql])]).map_ok(|script| script.contains("at BLOB NOT NULL")) == Ok(Bool.True)

expect Sql.migrate([create_events([])]) == Err(BadSchema("`Stamp` has no column type; pass an extension that covers it"))

# `Sql.Param` writes values that sort as Roc sorts them.
param : I64 -> List(U8)
param = |n| {
	Ok(bytes) = Sql.Param.encode_i64(n, [])
	bytes
}

expect param(-2) == [127, 255, 255, 255, 255, 255, 255, 254]

expect param(1) == [128, 0, 0, 0, 0, 0, 0, 1]

## Whether `a` sorts before `b` byte by byte, as a database compares blobs.
bytes_before : List(U8), List(U8) -> Bool
bytes_before = |a, b| match (a, b) {
	([], []) => Bool.False
	([], _) => Bool.True
	(_, []) => Bool.False
	([x, .. as xs], [y, .. as ys]) => if (x == y) bytes_before(xs, ys) else x < y
}

## Whether every value's bytes sort before the next value's.
ascending : List(List(U8)) -> Bool
ascending = |encoded| List.map2(encoded, encoded.drop_first(1), |a, b| bytes_before(a, b)).all(|ok| ok)

expect ascending([-1.5, -0.25, 0, 0.000000000000000001, 2.5].map(Sql.param_bytes))

expect ascending([-170141183460469231731687303715884105728.I128, -1, 0, 1].map(Sql.param_bytes))

# A zero byte inside a `Str` is escaped, and a `0, 0` ends it, so a shorter
# string sorts before every longer one it starts.
expect ascending(["", "a", "a\u(0)", "a\u(0)b", "ab", "b"].map(Sql.param_bytes))

# A record is its fields in name order, and the end of a `Str` keeps the
# next field from deciding the order: ("a", "z") is before ("ab", "").
expect ascending([{ x: "a", y: "z" }, { x: "ab", y: "" }].map(Sql.param_bytes))

main! = |_args| Ok({})
