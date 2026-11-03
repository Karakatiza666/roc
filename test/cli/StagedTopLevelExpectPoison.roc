# Item 4: a staged site inside a top-level expect whose f is erroneous. Same
# shape as StagedErroneousType.roc but the site is in an expect, not a def.
# Expected: only the alias error, no panic / invariant failure.
Stage := {}.{
	shape : Code(f) -> Str
	shape = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

Twig : List(Rose)
Rose := [Tip, Fan(Twig)]

count : Rose -> F32
count = |_r| 1.0

expect Stage.shape(count) == "lambda/1"

main! = |_args| Ok({})
