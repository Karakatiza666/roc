# A translator that names a format with `Code.Binds` binds a captured value of
# an opaque type (D5 of roc-reify-opaque-proposal.md). The type lives in a
# path package, so the site's module cannot read its fields: the program
# writes the value with the type's `encoder_for` in the translator's format,
# and the translator receives the bytes as `Code.Value.Encoded`. A captured
# value of a transparent type is bound as before.
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

Event : { at : Time, id : I64 }

Stage := {}.{
	render : Code.Binds(Code(Event -> Bool), Fmt) -> Code.Bound(Str)
	render = |code| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")

	show : Code.Value -> Str
	show = |value| match value {
		Encoded(bytes) => "Encoded(${Str.from_utf8_lossy(bytes)})"
		Int(n) => "Int(${n.to_str()})"
		_ => "other"
	}
}

before : Time -> Str
before = |cutoff| {
	bound = Stage.render(|e| e.at.is_before(cutoff))
	"${bound.value()}: ${Str.join_with(bound.inputs().map(Stage.show), ", ")}"
}

mixed : Time, I64 -> Str
mixed = |cutoff, least| {
	bound = Stage.render(|e| e.at.is_before(cutoff) and e.id > least)
	"${bound.value()}: ${Str.join_with(bound.inputs().map(Stage.show), ", ")}"
}

fields : Event -> Str
fields = |order| {
	bound = Stage.render(|e| e.at.is_before(order.at) and e.id != order.id)
	"${bound.value()}: ${Str.join_with(bound.inputs().map(Stage.show), ", ")}"
}

# A captured function is described as code, not bound: the format has no
# encoder for a function and needs none. The captured `Time` next to it is
# still bound as its encoder's bytes.
compared : Time -> Str
compared = |cutoff| {
	earlier = |a, b| a.is_before(b)
	bound = Stage.render(|e| earlier(e.at, cutoff))
	"${bound.value()}: ${Str.join_with(bound.inputs().map(Stage.show), ", ")}"
}

# The first calls may run while the compiler runs. The last reads a line
# from the input, so its values exist only when the program runs.
main! = || {
	Stdout.line!("before: ${before(Time.from_nanos(41))}")
	Stdout.line!("mixed: ${mixed(Time.from_nanos(42), 7)}")
	Stdout.line!("fields: ${fields({ at: Time.from_nanos(43), id: 8 })}")
	Stdout.line!("compared: ${compared(Time.from_nanos(44))}")
	typed = Stdin.line!().count_utf8_bytes()
	Stdout.line!("read: ${mixed(Time.from_nanos(typed.to_i128()), typed.to_i64_wrap())}")
}
