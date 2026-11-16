# A captured value of an opaque type in a top-level value is judged at the
# end of the module, after number literals take their default types (see
# numeral.roc). It still holds the opaque type, so a format with no encoder
# cannot bind it.
app [main!] { pt: "pt/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pt.Time

# A format with no encoder.
Plain := [Default].{
	default : () -> Plain
	default = || Default
}

Stage := {}.{
	render : Code.Binds(Code(I64 -> Bool), Plain) -> Code.Bound(Str)
	render = |code| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")
}

top : Str
top = {
	start = Time.from_nanos(5)
	Stage.render(|x| {
		_ = start
		x > 0
	}).value()
}

main! = || {
	Stdout.line!("top: ${top}")
}
