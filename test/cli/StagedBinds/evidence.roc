# A captured value of an opaque type whose encoder takes `where` evidence
# that selects a method of the translator's format, which holds a Code site
# at its own type variable. The program runs the encoder where it binds the
# site's inputs; the evidence edge describes the method at the captured
# value's type (design.md "Code Instance Tables").
app [main!] { pt: "pt/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pt.Tagged

Db := {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} | filter ${Str.inspect(code.graph().root_row().params)}" })

		show : Q(row) -> Str
		show = |q| q.log
	}

	of : row -> Q(row)
	of = |_row| Q.({ log: "of" })
}

# The translator's format: it writes a tagged value as the description of
# a filter at the value's type.
Fmt := [Default].{
	default : () -> Fmt
	default = || Default

	encode_tagged : a, List(U8) -> Try(List(U8), [])
	encode_tagged = |v, out| Ok(out.concat(Db.of(v).filter(|_x| Bool.True).show().to_utf8()))
}

Stage := {}.{
	render : Code.Binds(Code(I64 -> Bool), Fmt) -> Code.Bound(Str)
	render = |code| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")

	show : Code.Value -> Str
	show = |value| match value {
		Encoded(bytes) => "Encoded(${Str.from_utf8_lossy(bytes)})"
		_ => "other"
	}
}

tagged : Tagged(Str) -> Str
tagged = |tag| {
	bound = Stage.render(|n| n > 0 and tag.is_set())
	"${bound.value()}: ${Str.join_with(bound.inputs().map(Stage.show), ", ")}"
}

main! = || {
	Stdout.line!("tagged: ${tagged(Tagged.of("x"))}")
}
