# A nominal whose backing uses its argument holds what the argument holds.
# So a captured `Held(Time)` holds the opaque `Time`, and a format with no
# encoder cannot bind it (see phantom.roc for an argument the backing does
# not use).
app [main!] { pt: "pt/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pt.Time

# A format with no encoder.
Plain := [Default].{
	default : () -> Plain
	default = || Default
}

Held(a) := { value : a, id : I64 }.{
	id_of : Held(a) -> I64
	id_of = |h| h.id
}

Stage := {}.{
	render : Code.Binds(Code(I64 -> Bool), Plain) -> Code.Bound(Str)
	render = |code| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")
}

held : Held(Time) -> Str
held = |key| Stage.render(|x| {
	x == key.id_of()
}).value()

main! = || {
	Stdout.line!(held({ value: Time.from_nanos(1), id: 7 }))
}
