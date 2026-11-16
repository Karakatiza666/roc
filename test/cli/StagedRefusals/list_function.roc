# A function taken from a list that the program builds, and then called inside
# a described function. Simplifying does not read a closure back out of a list,
# so the call stays a call of a function value.
Stage := {}.{
	shape : Code(f) -> Str
	shape = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

pick : List(U16 -> U16), U16 -> U16
pick = |fs, x| match fs.first() {
	Ok(g) => g(x)
	Err(_) => x
}

main! = |_args| {
	echo!("${Stage.shape(pick)}\n")
	Ok({})
}
