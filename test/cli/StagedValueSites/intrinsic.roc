# A value at a `Code` position is computed by the program, so it cannot
# reach an intrinsic (R12). The report says to use a lambda, which the
# translator describes instead.
app [main!] { st: "st/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import st.Stage

Text :: {}.{
	count : Str -> U64
}

counted : Str -> Str
counted = |s| Stage.bind_u64(Text.count(s)).value()

main! = || {
	Stdout.line!("fixed: ${Stage.show_u64(Text.count("x"))}")
	Stdout.line!("counted: ${counted("y")}")
}
