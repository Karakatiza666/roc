# A block name bound to a function that is picked when the program runs.
#
# `f` is bound to an `if`, not to a lambda, so no body stands behind the name
# for the walk to read. The report says so, rather than the type mismatch the
# checker meets between a function and a `Code(U16 -> U16)`.
Stage := {}.{
	describe : Code(U16 -> U16) -> Str
	describe = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

picked : Str
picked = {
	a = |x| x + 1
	b = |x| x + 2
	f = if 1 > 2 a else b
	Stage.describe(f)
}

main! = |_args| {
	echo!("${picked}\n")
	Ok({})
}
