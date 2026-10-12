# A template's function argument has to name a definition, because the `Ir` is
# first order and a call on the parameter names the row the argument leads to.
# A function read out of a record names none, so the argument is refused.
Stage := {}.{
	shape : Code(f) -> Str
	shape = |code| match Code.ir(code) {
		Lambda(_, _, _) => "lambda"
		_ => "other"
	}
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
