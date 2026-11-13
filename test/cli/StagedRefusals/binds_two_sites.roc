# One call that holds two sites whose lambdas both read captured values.
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout

Bare := [Default].{
	default : () -> Bare
	default = || Default
}

Stage := {}.{
	both : Code.Binds(Code(U64 -> U64), Bare), Code.Binds(Code(U64 -> U64), Bare) -> Code.Bound(Str)
	both = |a, b| Code.bound(a, "slots ${Code.graph(a).slots().len().to_str()} ${Code.graph(b).slots().len().to_str()}")
}

pair : U64, U64 -> Str
pair = |n, m| Stage.both(|x| x + n, |x| x + m).value()

main! = || {
	Stdout.line!(pair(3, 4))
}
