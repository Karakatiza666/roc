# A lambda that fails to check at a `Code` position reports its type error.
#
# `(n)` is a one-element tuple pattern, so this lambda takes a tuple where the
# `Code` asks for a `U64`. Checking replaces the lambda with a runtime error,
# and the site it stood at is left to that error rather than reified.
Stage := {}.{
	shape : Code(U64 -> Bool) -> Str
	shape = |code| match code.ir() {
		Lambda(_, _, _) => "lambda"
		_ => "other"
	}
}

staged : Str
staged = Stage.shape(|(n)| n > 0)

main! = |_args| {
	echo!("${staged}\n")
	Ok({})
}
