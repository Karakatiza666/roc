# A site whose translator lives in another package. `Expr.twice` is outside
# the translator's cut, so its body is part of the description and the
# translator prints it inline. `Expr.clamp` is in the cut, so it stays a call.
app [main!] { lib: "lib/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import lib.Expr

area : F64 -> F64
area = |w| Expr.twice(w) + Expr.clamp(w)

main! = || {
	Stdout.line!(Expr.to_text(area))
}
