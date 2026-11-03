# The typing side of `Code.Binds` (rule "Bound Capture Encoding"): each value
# the function captures must be encodable in the translator's format, and the
# format must have `default`. Each failure is a type error.
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout

# A format that writes integers and nothing else.
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

	encode_i64 : I64, List(U8) -> Try(List(U8), [TooBig])
	encode_i64 = |n, out| if n > 100 Err(TooBig) else Ok(out.concat(n.to_str().to_utf8()))
}

# A format with no `default`.
Nameless := [Only].{
	encode_i64 : I64, List(U8) -> Try(List(U8), [])
	encode_i64 = |n, out| Ok(out.concat(n.to_str().to_utf8()))
}

# A nominal type with no encoder.
Celsius := F32

Stage := {}.{
	render : Code.Binds(Code(I64 -> Bool), Fmt) -> Code.Bound(Str)
	render = |code| Code.bound(code, "render")

	fallible : Code.Binds(Code(I64 -> Bool), Fallible) -> Code.Bound(Str)
	fallible = |code| Code.bound(code, "fallible")

	nameless : Code.Binds(Code(I64 -> Bool), Nameless) -> Code.Bound(Str)
	nameless = |code| Code.bound(code, "nameless")
}

float : F32 -> Str
float = |limit| Stage.render(|x| x.to_f32() < limit).value()

nominal : Celsius -> Str
nominal = |limit| Stage.render(|x| {
	Celsius.(c) = limit
	x.to_f32() < c
}).value()

fails : I64 -> Str
fails = |limit| Stage.fallible(|x| x < limit).value()

unnamed : I64 -> Str
unnamed = |limit| Stage.nameless(|x| x < limit).value()

# An unannotated helper whose captured value has a type variable: the
# requirement enters the helper's type, and a call that fixes the variable
# to a type the format cannot encode is the error, with the rule's own text.
generic = |limit| Stage.render(|x| {
	_ = limit
	x > 0
}).value()

# A captured function is described as code and needs no encoder, but a
# captured record that holds a function is a value to bind: its encoder needs
# one for the function, which no format has.
holds : { check : I64 -> Bool } -> Str
holds = |h| Stage.render(|x| {
	_ = h
	x > 0
}).value()

main! = || {
	Stdout.line!(float(1.5))
	Stdout.line!(nominal(Celsius.(2.5)))
	Stdout.line!(fails(3))
	Stdout.line!(unnamed(4))
	Stdout.line!(generic("five"))
	Stdout.line!(holds({ check: |n| n > 0 }))
}
