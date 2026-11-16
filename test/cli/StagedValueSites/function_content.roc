# A type variable at a `Code(a)` position whose `a` is a function is decided
# as a `Code` value that is passed on (R12). So `code` is a `Code(U64 -> U64)`,
# and a call of it is a type mismatch.
app [main!] { st: "st/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import st.Stage

relay_fn = |code| {
	shown = Stage.show_fn(code)
	_called = code(1)
	shown
}

main! = || {
	Stdout.line!("called: ${relay_fn(|x| x * 3)}")
}
