# Item 2: a generic that merely returns a Code it was handed is not a template.
# Expected after fix: runs, prints lambda/1. Before: "cannot reach this
# definition" at the pick call.
Stage := {}.{
	shape : Code(f) -> Str
	shape = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

double : I32 -> I32
double = |x| x * 2

triple : I32 -> I32
triple = |x| x * 3

pick : Bool, a, a -> a
pick = |first, a, b| if first a else b

pick_one : Code(I32 -> I32), Code(I32 -> I32) -> Str
pick_one = |a, b| Stage.shape(pick(Bool.True, a, b))

main! = |_args| {
	echo!(pick_one(double, triple))
	Ok({})
}
