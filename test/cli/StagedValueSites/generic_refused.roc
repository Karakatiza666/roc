# What a generic function still cannot bind (R7). A call that also reads a
# run-time value outside its sites has no one value to run with while the
# compiler runs, so it binds nothing in a generic function.
app [main!] { st: "st/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import st.Stage

labeled = |k, label| Stage.bind_with(k + 0, label)

main! = || {
	Stdout.line!(labeled(1.U64, "a").value())
}
