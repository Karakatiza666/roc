# A nominal type whose argument its backing does not use (a phantom
# argument) holds what its backing holds at that argument. So a captured
# `Tagged(Time)` holds no opaque type, and its read needs no encoder: a
# format with no encoder binds it. A nominal whose backing uses the
# argument still needs one (see phantom_refused.roc).
app [main!] { pt: "pt/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pt.Time

# A format with no encoder.
Plain := [Default].{
	default : () -> Plain
	default = || Default
}

Tagged(a) := { id : I64 }.{
	id_of : Tagged(a) -> I64
	id_of = |t| t.id
}

Stage := {}.{
	render : Code.Binds(Code(I64 -> Bool), Plain) -> Code.Bound(Str)
	render = |code| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")
}

tagged : Tagged(Time) -> Str
tagged = |key| {
	bound = Stage.render(|x| {
		x == key.id_of()
	})
	"${bound.value()}: ${Str.inspect(bound.inputs())}"
}

main! = || {
	t : Tagged(Time)
	t = { id: 7 }
	Stdout.line!("tagged: ${tagged(t)}")
}
