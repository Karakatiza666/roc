# Item 1: a transparent alias of a Code is a Code position. Expected: check fails
# with "code is not allowed here" at `MyCode` inside the record; before the fix it
# is accepted and a description-less Code reaches lowering.
Stage := {}.{
	shape : Code(f) -> Str
	shape = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

MyCode : Code(I32 -> I32)

holder : { c : MyCode } -> Str
holder = |_r| "x"

main! = |_args| Ok({})
