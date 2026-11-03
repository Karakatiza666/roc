app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import Util

# Item 2, imported side: `Util.id(code)` returns the Code it was given. Expected
# after fix: runs. Before: recorded as template_call/template_callee and the
# walk looks for a template body in Util.
Stage := {}.{
	shape : Code(f) -> Str
	shape = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

double : I32 -> I32
double = |x| x * 2

hold : Code(I32 -> I32) -> Str
hold = |c| Stage.shape(Util.id(c))

main! = || Stdout.line!(hold(double))
