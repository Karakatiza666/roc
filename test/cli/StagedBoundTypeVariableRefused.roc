# A `Code.Bound` translator whose result type holds a type variable
# (compiler-gaps.md R6, the negative side).
#
# `c` stands only in the result, so neither the lambda nor the call fixes it.
# The call is no compile-time root and does not bind the captured `name`.
Patch(c) := [Patch(Str)].{
	text : Patch(c) -> Str
	text = |Patch(t)| t
}

Stage := {}.{
	loose : Code(U16 -> b) -> Code.Bound(Patch(c))
	loose = |code| Code.bound(code, Patch("slots ${Code.graph(code).slots().len().to_str()}"))
}

unfixed : Str -> Str
unfixed = |name| Stage.loose(|_| { name: name }).value().text()

main! = |_args| {
	echo!("${unfixed("ada")}\n")
	Ok({})
}
