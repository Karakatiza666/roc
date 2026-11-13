# A generic function whose captured value has a type variable keeps the
# requirement of rule "Bound Capture Encoding" in its type. A call that fixes
# the variable to a function satisfies it (rule "Function Capture
# Resolution"): a captured function needs no encoder. The call that fixes it
# to an opaque type uses the encoder. The function the program passes exists
# only when the program runs, so the walk still refuses to describe it, as
# it refuses such a function in a function that is not generic: it is a
# function parameter (see function_parameter_refused.roc).
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

Rendered(r) := [Rendered(Str)].{
	text : Rendered(r) -> Str
	text = |Rendered(t)| t
}

Stage := {}.{
	keep : Code.Binds(Code(I64 -> r), Fmt) -> Code.Bound(Rendered(r))
	keep = |code| Code.bound(code, Rendered("slots ${Code.graph(code).slots().len().to_str()}"))
}

# Unannotated: the type of `value` is a variable of this function.
kept = |value| Stage.keep(|_| value)

main! = || {
	f : Code.Bound(Rendered(I64 -> I64))
	f = kept(|x| x + 1)
	Stdout.line!("function: ${f.value().text()} ${Str.inspect(f.inputs())}")
	t : Code.Bound(Rendered(Time))
	t = kept(Time.from_nanos(5))
	Stdout.line!("opaque: ${t.value().text()} ${Str.inspect(t.inputs())}")
}
