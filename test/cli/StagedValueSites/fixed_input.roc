# A value that reads a parameter, at a `Code(a)` position whose `a` the
# translator leaves free, is one input slot of the call that binds it, at
# the value's type (R12).
app [main!] { st: "st/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdin
import pf.Stdout
import st.Stage

shown_bound : Code.Bound(Str) -> Str
shown_bound = |b| "${b.value()} inputs ${Str.inspect(b.inputs())}"

twice : U64 -> Code.Bound(Str)
twice = |k| Stage.bind(k * 2)

main! = || {
	Stdout.line!("fixed: ${shown_bound(twice(1))}")
	typed = Stdin.line!().count_utf8_bytes()
	Stdout.line!("read: ${shown_bound(twice(typed))}")
}
