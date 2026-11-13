# A `var` read from around a lambda at a `Code.Binds` place. The value of a
# `var` at the call is not always the value the description reads, so it
# cannot be an input slot.
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout

# A format with no encoder at all.
Bare := [Default].{
	default : () -> Bare
	default = || Default
}

Stage := {}.{
	render : Code.Binds(Code(U64 -> U64), Bare) -> Code.Bound(Str)
	render = |code| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")
}

wobble : U64 -> Str
wobble = |n| {
	var $total = n
	$total = $total + 1
	Stage.render(|x| x + $total).value()
}

main! = || {
	Stdout.line!(wobble(3))
}
