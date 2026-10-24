# Item 5: the user page says a Code is a function parameter or a template's
# return. A callback that takes a Code is neither. Expected: "code is not allowed
# here" on each Code below (run's callback, and the record field's function).
Stage := {}.{
	shape : Code(f) -> Str
	shape = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

run : (Code(I32 -> I32) -> Str) -> Str
run = |_cb| "x"

holder : { handler : Code(I32 -> I32) -> Str } -> Str
holder = |_r| "y"

main! = |_args| Ok({})
