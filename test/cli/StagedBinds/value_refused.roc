# A value at a plain `Code` position whose type holds an opaque type (R12).
# The position names no format, so the site has no way to send the value
# to the translator as an input slot, and the compiler refuses it.
app [main!] { pt: "pt/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pt.Time

Stage := {}.{
	since : Code(Time) -> Code.Bound(Str)
	since = |code| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")
}

after : I128 -> Str
after = |nanos| Stage.since(Time.from_nanos(nanos)).value()

main! = || {
	Stdout.line!("refused: ${after(41)}")
}
