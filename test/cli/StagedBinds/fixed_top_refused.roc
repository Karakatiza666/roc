# A fixed value at a `Code.Binds` position whose type holds an opaque type is
# an input slot that the program computes (see fixed_value.roc). The body of
# a top-level constant is computed while the compiler runs, so it has no
# place to compute the slot, and the value is refused as it is at a plain
# `Code` position (R12).
app [main!] { pt: "pt/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pt.Time

Fmt := [Default].{
	default : () -> Fmt
	default = || Default

	encode_i128 : I128, List(U8) -> Try(List(U8), [])
	encode_i128 = |n, out| Ok(out.concat(n.to_str().to_utf8()))
}

Stage := {}.{
	since : Code.Binds(Code(Time), Fmt) -> Code.Bound(Str)
	since = |code| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")
}

top : Str
top = Stage.since(Time.from_nanos(44)).value()

main! = || {
	Stdout.line!(top)
}
