# A derived equality over a function type inside a described function.
Stage := {}.{
	shape : Code(f) -> Str
	shape = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

same : { f : U16 -> U16 }, { f : U16 -> U16 } -> Bool
same = |a, b| a == b

main! = |_args| {
	echo!("${Stage.shape(same)}\n")
	Ok({})
}
