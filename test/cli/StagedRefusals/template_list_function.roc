# A template's function argument read out of a list. The argument has to name a
# definition, and an item of a list names none.
Stage := {}.{
	shape : Code(f) -> Str
	shape = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

twice : (U16 -> U16) -> Code(U16 -> U16)
twice = |g| |x| g(g(x))

inc : U16 -> U16
inc = |n| n + 1

main! = |_args| {
	match [inc].first() {
		Ok(f) => echo!("${Stage.shape(twice(f))}\n")
		Err(_) => echo!("none\n")
	}
	Ok({})
}
