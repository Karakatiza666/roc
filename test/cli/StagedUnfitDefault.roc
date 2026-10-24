# A lambda whose parameter takes the numeric default where it is reified, and
# whose default does not fit how the parameter is used.
#
# `x` is constrained only by `*`, so it has the numeric default `Dec`, the way
# it would in a compiled function. `Dec` has no `*` that takes the `U8` it is
# multiplied by, so nothing fixes `x` and the description is refused, with
# the reason.
Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

narrowed : Str
narrowed = Stage.describe(|x| x * 2.U8)

main! = |_args| {
	echo!("${narrowed}\n")
	Ok({})
}
