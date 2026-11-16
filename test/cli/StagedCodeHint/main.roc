# A method call on a receiver whose type is not known when the lambda is
# checked takes a plain function, not a `Code`. The type mismatch says how to
# fix it (structural proposal Q10, 3.5): annotate the receiver, or call the
# method on its type.
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import Q

named_only = |q| q.filter(|x| x.name != "")

main! = || {
	_r = named_only(Q.{ n: 0 })
	Stdout.line!("done")
}
