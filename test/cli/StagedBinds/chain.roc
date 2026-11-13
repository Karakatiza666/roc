# Captured values bound at the end of a chain of calls (compiler-gaps.md
# Gap 1, acceptance test 3): a record with an optional field, read whole, at
# a `Code` place, and a value of an opaque type at a `Code.Binds` place. The
# chain binds the slots of both lambdas at `ready`, and each value is the one
# a translator that binds them at its own call (`Stage`) receives: `Absent`
# for a field the record does not hold, and the bytes of the type's encoder
# in the translator's format.
app [main!] { pt: "pt/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdin
import pf.Stdout
import pt.Time

# The translator's format: it writes each number as its decimal digits.
Fmt := [Default].{
	default : () -> Fmt
	default = || Default

	encode_i128 : I128, List(U8) -> Try(List(U8), [])
	encode_i128 = |n, out| Ok(out.concat(n.to_str().to_utf8()))

	encode_i64 : I64, List(U8) -> Try(List(U8), [])
	encode_i64 = |n, out| Ok(out.concat(n.to_str().to_utf8()))
}

Place : { city : Str, zip ?: Str }
Event : { at : Time, id : I64 }

Q := [Q(Str)].{
	from : Str -> Q
	from = |table| Q("FROM ${table}")

	at_place : Q, Code(Place -> Bool) -> Q
	at_place = |Q(text), code| Q("${text} WHERE ${Q.slots(code)}")

	before : Q, Code.Binds(Code(Event -> Bool), Fmt) -> Q
	before = |Q(text), code| Q("${text} AND ${Q.slots(code)}")

	ready : Q -> Code.Bound(Str)
	ready = |Q(text)| Code.Bound.of(text)

	slots : Code(f) -> Str
	slots = |code| "slots ${code.graph().slots().len().to_str()} from ${code.first_slot().to_str()}"
}

# The same lambdas, each bound at the call that takes it.
Stage := {}.{
	place : Code(Place -> Bool) -> Code.Bound(Str)
	place = |code| Code.bound(code, Q.slots(code))

	before : Code.Binds(Code(Event -> Bool), Fmt) -> Code.Bound(Str)
	before = |code| Code.bound(code, Q.slots(code))

	show : Code.Value -> Str
	show = |value| match value {
		Str(s) => "\"${s}\""
		Int(n) => "Int(${n.to_str()})"
		Record(items) => "{${Str.join_with(items.map(Stage.show), ", ")}}"
		Encoded(bytes) => "Encoded(${Str.from_utf8_lossy(bytes)})"
		Absent => "Absent"
		_ => "other"
	}

	run : Code.Bound(Str) -> Str
	run = |bound| "${bound.value()}: ${Str.join_with(bound.inputs().map(Stage.show), ", ")}"
}

chained : Place, Time, I64 -> Str
chained = |place, cutoff, least| Q.from("events").at_place(|p| p == place).before(|e| e.at.is_before(cutoff) and e.id > least).ready() |> Stage.run()

direct : Place, Time, I64 -> Str
direct = |place, cutoff, least| "${Stage.run(Stage.place(|p| p == place))} | ${Stage.run(Stage.before(|e| e.at.is_before(cutoff) and e.id > least))}"

main! = || {
	typed = Stdin.line!().count_utf8_bytes()
	with_zip : Place
	with_zip = { city: "Oslo", zip: "0150" }
	no_zip : Place
	no_zip = { city: "Lyon" }
	cutoff = Time.from_nanos(typed.to_i128())
	least = typed.to_i64_wrap()
	Stdout.line!("chained: ${chained(with_zip, cutoff, least)}")
	Stdout.line!("direct: ${direct(with_zip, cutoff, least)}")
	Stdout.line!("chained: ${chained(no_zip, cutoff, least)}")
	Stdout.line!("direct: ${direct(no_zip, cutoff, least)}")
}
