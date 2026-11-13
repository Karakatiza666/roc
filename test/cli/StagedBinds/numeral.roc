# A captured value whose type is a number literal's type variable takes the
# literal's default type, `Dec`, before its read is judged. So it holds no
# opaque type, and a format with no encoder binds it.
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout

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
	limit = 5
	Stage.render(|x| {
		_ = limit
		x > 0
	}).value()
}

main! = || {
	Stdout.line!("top: ${top}")
}
