# A `Code.Bound` translator in a function whose type holds the kind of a
# record literal's field (compiler-gaps.md R6).
#
# `mk` returns the call, so each use of `mk` fixes the kind again: `a` makes
# the field optional. The call is a generic bound call, and each use binds
# its inputs at its own instance (R7 of the Gap 1 design).
Patch(b) := [Patch(Str)].{
	text : Patch(b) -> Str
	text = |Patch(t)| t
}

Stage := {}.{
	bind : Code(U16 -> b) -> Code.Bound(Patch(b))
	bind = |code| Code.bound(code, Patch("slots ${Code.graph(code).slots().len().to_str()}"))
}

mk = |name| {
	n = Str.concat(name, "")
	Stage.bind(|_| { name: n })
}

main! = |_args| {
	a : Code.Bound(Patch({ name ?: Str }))
	a = mk("x")
	b = mk("y")
	echo!("${a.value().text()}\n${b.value().text()}\n")
	Ok({})
}
