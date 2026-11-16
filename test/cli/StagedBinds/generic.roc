# A generic function whose captured value has a type variable keeps the
# requirement of rule "Bound Capture Encoding" in its type (R7 of the Gap 1
# design): the call that fixes the variable to the opaque `Time` discharges
# it, and the translator receives the value as its encoder's bytes.
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
	render : Code.Binds(Code(r -> Bool), Fmt) -> Code.Bound(Rendered(r))
	render = |code| Code.bound(code, Rendered("slots ${Code.graph(code).slots().len().to_str()}"))
}

# Unannotated: the type of `cutoff` is a variable of this function.
before = |cutoff| Stage.render(|x| x.at.is_before(cutoff))

main! = || {
	a : Code.Bound(Rendered({ at : Time }))
	a = before(Time.from_nanos(5))
	Stdout.line!("${a.value().text()} ${Str.inspect(a.inputs())}")
}
