# A fixed value at a `Code` position whose type holds an opaque type has no
# literal, so it is refused, also when an operation of the type computes it
# (R12).
app [main!] { st: "st/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import st.Stage
import st.Table

main! = || {
	Stdout.line!(Stage.shown(Table.named("vet")))
}
