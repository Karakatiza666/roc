# A lambda at a `Code.Bound` translator that returns a record literal
# (compiler-gaps.md row 4, R6).
#
# The kind of the literal's field is quantified with `renamed`, but the type
# of `renamed` does not hold it, so no use fixes it. It is `required` where
# the root is evaluated and where the program reads it, and the call binds the
# captured `name`.
Patch(b) := [Patch(Str)].{
	text : Patch(b) -> Str
	text = |Patch(t)| t
}

Stage := {}.{
	bind : Code(U16 -> b) -> Code.Bound(Patch(b))
	bind = |code| Code.bound(code, Patch("slots ${Code.graph(code).slots().len().to_str()}"))
}

renamed : Str -> Str
renamed = |name| {
	bound = Stage.bind(|_| { name: name })
	inputs = bound.inputs().map(
		|value| match value {
			Str(s) => s
			_ => "other"
		},
	)
	"${bound.value().text()} inputs [${Str.join_with(inputs, ", ")}]"
}

main! = |_args| {
	echo!("${renamed("ada")}\n${renamed("bo")}\n")
	Ok({})
}
