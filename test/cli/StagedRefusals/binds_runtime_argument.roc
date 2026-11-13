# A translator that receives captured inputs runs while the compiler runs, so
# the other arguments of its call must be fixed then. `name` is known only
# when the program runs.
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout

Bare := [Default].{
	default : () -> Bare
	default = || Default
}

Stage := {}.{
	render : Str, Code.Binds(Code(U64 -> U64), Bare) -> Code.Bound(Str)
	render = |name, code| Code.bound(code, "${name} ${Code.graph(code).slots().len().to_str()}")
}

labelled : Str, U64 -> Str
labelled = |name, n| Stage.render(name, |x| x + n).value()

main! = || {
	Stdout.line!(labelled("a", 3))
}
