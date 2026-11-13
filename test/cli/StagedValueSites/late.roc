# A value at a `Code` position that reads a parameter is decided when its
# expression is checked (R12). Here `code` is still a type variable at
# `Stage.show_u64(code)`, so it is decided as a value, a `U64`. A later line
# that uses `code` as a `Code(U64)` is a type mismatch.
app [main!] { st: "st/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import st.Stage

late : Bool, Code(U64) -> Str
late = |flag, known| {
	inner = |code| {
		shown = Stage.show_u64(code)
		_chosen = if flag code else known
		shown
	}
	inner(known)
}

main! = || {
	Stdout.line!("late: ${late(True, 6)}")
}
