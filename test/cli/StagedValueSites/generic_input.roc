# A value that reads a parameter, at a `Code(a)` position whose `a` the
# translator leaves free, in a generic function (R12, R7). The call's
# function type names a type variable of the function, so the call is a
# generic bound call: each use that fixes the variable binds the value at
# its own type. A lambda at a `Code({} -> a)` position whose result names the
# variable is the same, and so is a call in a function that a block in a
# generic function holds.
app [main!] { st: "st/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdin
import pf.Stdout
import st.Stage

shown_bound : Code.Bound(Str) -> Str
shown_bound = |b| "${b.value()} inputs ${Str.inspect(b.inputs())}"

twice = |k| Stage.bind(k * 2)

plus = |k| Stage.bind_thunk(|_| k + 1)

pair = |n, m| {
	inner = |k| Stage.bind(k + 0)
	"${shown_bound(inner(n))}, ${shown_bound(inner(m))}"
}

main! = || {
	Stdout.line!("value u64: ${shown_bound(twice(1.U64))}")
	Stdout.line!("value i32: ${shown_bound(twice(3.I32))}")
	Stdout.line!("lambda u8: ${shown_bound(plus(4.U8))}")
	Stdout.line!("lambda i64: ${shown_bound(plus(5.I64))}")
	Stdout.line!("local: ${pair(7.U16, 8.I8)}")
	typed = Stdin.line!().count_utf8_bytes()
	Stdout.line!("read: ${shown_bound(twice(typed))}")
}
