# The typing side of `Code.Binds` (rule "Bound Capture Encoding"): each value
# the function captures whose type holds an opaque type, or a type variable,
# must be encodable in the translator's format, and the format must have
# `default`. Each failure is a type error.
app [main!] { pt: "pt/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pt.Time

# A format that writes `I64` and nothing else, so it cannot write a `Time`.
Fmt := [Default].{
	default : () -> Fmt
	default = || Default

	encode_i64 : I64, List(U8) -> Try(List(U8), [])
	encode_i64 = |n, out| Ok(out.concat(n.to_str().to_utf8()))
}

# A format whose encoder can fail, which a bound call cannot report.
Fallible := [Default].{
	default : () -> Fallible
	default = || Default

	encode_i128 : I128, List(U8) -> Try(List(U8), [TooBig])
	encode_i128 = |n, out| if n > 100 Err(TooBig) else Ok(out.concat(n.to_str().to_utf8()))
}

# A format with no `default`.
Nameless := [Only].{
	encode_i64 : I64, List(U8) -> Try(List(U8), [])
	encode_i64 = |n, out| Ok(out.concat(n.to_str().to_utf8()))
}

# An opaque type with no encoder.
Celsius :: F32

Stage := {}.{
	render : Code.Binds(Code(I64 -> Bool), Fmt) -> Code.Bound(Str)
	render = |code| Code.bound(code, "render")

	fallible : Code.Binds(Code(I64 -> Bool), Fallible) -> Code.Bound(Str)
	fallible = |code| Code.bound(code, "fallible")

	nameless : Code.Binds(Code(I64 -> Bool), Nameless) -> Code.Bound(Str)
	nameless = |code| Code.bound(code, "nameless")
}

opaque : Time -> Str
opaque = |cutoff| Stage.render(|x| {
	_ = cutoff
	x > 0
}).value()

nominal : Celsius -> Str
nominal = |limit| Stage.render(|x| {
	_ = limit
	x > 0
}).value()

fails : Time -> Str
fails = |cutoff| Stage.fallible(|x| {
	_ = cutoff
	x > 0
}).value()

unnamed : I64 -> Str
unnamed = |limit| Stage.nameless(|x| x < limit).value()

# An unannotated helper whose captured value has a type variable: the
# requirement enters the helper's type, since a call could fix the variable
# to an opaque type. A call that fixes it to a type the format cannot encode
# is the error, with the rule's own text, though the type is `Str`.
generic = |limit| Stage.render(|x| {
	_ = limit
	x > 0
}).value()

# A captured record that holds an opaque type is bound as its encoder's
# bytes: its encoder needs one for each field, and no format has one for the
# function it holds too.
holds : { check : I64 -> Bool, at : Time } -> Str
holds = |h| Stage.render(|x| {
	_ = h
	x > 0
}).value()

main! = || {
	Stdout.line!(opaque(Time.from_nanos(1)))
	Stdout.line!(nominal(Celsius.(2.5)))
	Stdout.line!(fails(Time.from_nanos(3)))
	Stdout.line!(unnamed(4))
	Stdout.line!(generic("five"))
	Stdout.line!(holds({ check: |n| n > 0, at: Time.from_nanos(6) }))
}
