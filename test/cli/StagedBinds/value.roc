# A value at a `Code` position whose type holds an opaque type (R12). At a
# `Code.Binds` position the program writes the value with the type's
# `encoder_for` in the translator's format, and the translator receives the
# bytes as `Code.Value.Encoded`. At a plain `Code` position the site cannot
# send the value, and the compiler refuses it (see value_refused.roc).
app [main!] { pt: "pt/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdin
import pf.Stdout
import pt.Time

# The translator's format: it writes each number as its decimal digits.
Fmt := [Default].{
	default : () -> Fmt
	default = || Default

	encode_i128 : I128, List(U8) -> Try(List(U8), [])
	encode_i128 = |n, out| Ok(out.concat(n.to_str().to_utf8()))
}

Stage := {}.{
	since : Code.Binds(Code(Time), Fmt) -> Code.Bound(Str)
	since = |code| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")

	show : Code.Value -> Str
	show = |value| match value {
		Encoded(bytes) => "Encoded(${Str.from_utf8_lossy(bytes)})"
		_ => "other"
	}
}

after : I128 -> Str
after = |nanos| {
	bound = Stage.since(Time.from_nanos(nanos))
	"${bound.value()}: ${Str.join_with(bound.inputs().map(Stage.show), ", ")}"
}

main! = || {
	Stdout.line!("fixed: ${after(41)}")
	typed = Stdin.line!().count_utf8_bytes()
	Stdout.line!("read: ${after(typed.to_i128())}")
}
