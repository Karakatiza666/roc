# A generic `Code.Bound` function of a package, used from the app (R7 of the
# Gap 1 design). Each use of the app fixes the row and binds the input.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.F

show = |bound| {
	text = match bound.value() {
		Ok(t) => t
		Err(_) => "err"
	}
	"${text} inputs ${Str.inspect(bound.inputs())}"
}

main! = || {
	a : Code.Bound(Try(Str, [NotFound, Other]))
	a = F.fetch(3)
	b : Code.Bound(Try(Str, [NotFound]))
	b = F.fetch(4)
	Stdout.line!(show(a))
	Stdout.line!(show(b))
}
