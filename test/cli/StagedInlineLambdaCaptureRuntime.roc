# A lambda written at a `Code` position that reads a value known only while the
# program runs.
#
# The walk replays the statement that bound `k`, and that statement reads the
# parameter `n`. A description is written while the compiler runs, when no call
# has supplied `n`, so the report names the parameter rather than `k`.
Stage := {}.{
	render : Code(U16 -> U16) -> Str
	render = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

scaled : U16 -> Str
scaled = |n| {
	k = n * 2
	Stage.render(|x| x + k)
}

main! = |_args| {
	echo!("${scaled(3)}\n")
	Ok({})
}
