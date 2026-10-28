# The same translator after its package changed `Expr.norm` to take a square
# root, which the translator has no form for. `norm` is outside the cut, so
# its body is part of the description, and the build stops at the site.
app [main!] { lib: "lib/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import lib.Expr

root : F64 -> F64
root = |x| Expr.norm(x) + 1.0

text = Expr.to_text_or_stop(root)

main! = || {
	Stdout.line!(text)
}
