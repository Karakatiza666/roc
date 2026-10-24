# Item 1 (positive side): an alias at a parameter position still stages.
Stage := {}.{
	shape : Code(f) -> Str
	shape = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

MyCode : Code(I32 -> I32)

double : I32 -> I32
double = |x| x * 2

via_alias : MyCode -> Str
via_alias = |c| Stage.shape(c)

main! = |_args| {
	echo!(via_alias(double))
	Ok({})
}
