# A fixed value at a `Code` position is described as the literal it is fixed
# to (R12). A value the compiler cannot compute into a literal is refused.
app [main!] { st: "st/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import st.Stage

main! = || {
	Stdout.line!("inspect: ${Stage.shown(Str.inspect(3.U8))}")
}
