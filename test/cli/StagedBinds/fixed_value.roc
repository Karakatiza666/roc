# A fixed value at a `Code.Binds` position whose type holds an opaque type
# (R12). It has no literal, so it is one input slot, as a run-time value is:
# the program computes it where the call stands and writes it with the
# type's `encoder_for` in the translator's format. A fixed value whose type
# holds no opaque type stays a literal, with no slot. At a plain `Code`
# position the same fixed value is refused (see
# ../StagedValueSites/opaque_refused.roc).
app [main!] { pt: "pt/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pt.Time

# The translator's format: it writes each number as its decimal digits.
Fmt := [Default].{
	default : () -> Fmt
	default = || Default

	encode_i128 : I128, List(U8) -> Try(List(U8), [])
	encode_i128 = |n, out| Ok(out.concat(n.to_str().to_utf8()))
}

Stage := {}.{
	since : Code.Binds(Code(Time), Fmt) -> Code.Bound(Str)
	since = |code| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")

	limit : Code.Binds(Code(U64), Fmt) -> Code.Bound(Str)
	limit = |code| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")

	show : Code.Value -> Str
	show = |value| match value {
		Encoded(bytes) => "Encoded(${Str.from_utf8_lossy(bytes)})"
		Int(n) => "Int(${n.to_str()})"
		_ => "other"
	}
}

shown : Code.Bound(Str) -> Str
shown = |bound| "${bound.value()}: ${Str.join_with(bound.inputs().map(Stage.show), ", ")}"

literal : {} -> Str
literal = |{}| shown(Stage.since(Time.from_nanos(41)))

named : {} -> Str
named = |{}| {
	start = Time.from_nanos(42)
	shown(Stage.since(start))
}

plain : {} -> Str
plain = |{}| shown(Stage.limit(10))

local : {} -> Str
local = |{}| {
	at = |n| Time.from_nanos(n)
	shown(Stage.since(at(43)))
}

main! = || {
	Stdout.line!("literal: ${literal({})}")
	Stdout.line!("named: ${named({})}")
	Stdout.line!("plain: ${plain({})}")
	Stdout.line!("local: ${local({})}")
}
