# A method call in a described function on a value whose type no argument
# fixes.
Stage := {}.{
	shape : Code(f) -> Str
	shape = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

show = |x| x.to_str()

main! = |_args| {
	echo!("${Stage.shape(show)}\n")
	Ok({})
}
