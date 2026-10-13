# A polymorphic function named where a `Code` is expected.
#
# A description is one concrete type at a time, so `twice` has none. The report
# has to arrive before the constant holding the site is evaluated: evaluating
# it instantiates the `f` of the `Code(f)`, and an `f` still holding a type
# variable has no instantiation.
Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

twice : a -> (a, a)
twice = |x| (x, x)

staged : Str
staged = Stage.describe(twice)

main! = |_args| {
	echo!("${staged}\n")
	Ok({})
}
