# A template's function argument has to name a definition, because a call on
# the parameter is a `Call` of the row the argument leads to.
# A function read out of a record names none, so the argument is refused.
Stage := {}.{
	shape : Code(f) -> Str
	shape = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

twice : (U16 -> U16) -> Code(U16 -> U16)
twice = |g| |x| g(g(x))

inc : U16 -> U16
inc = |n| n + 1

table : { step : U16 -> U16 }
table = { step: inc }

main! = |_args| {
	echo!("${Stage.shape(twice(table.step))}\n")
	Ok({})
}
