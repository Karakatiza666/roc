# A lambda written at a `Code` position that reads a value known only while the
# program runs.
#
# The walk replays the statement that bound `k`, and that statement reads the
# parameter `n`. The translator returns a `Code.Bound`, so `n` is an input
# slot: the translator runs once, while the compiler runs, and each call of
# `scaled` gives the program the value of its own `n`.
Stage := {}.{
	render : Code(U16 -> U16) -> Code.Bound(Str)
	render = |code| {
		graph = Code.graph(code)
		Code.bound(code, "lambda/${graph.root_row().params.len().to_str()} slots/${graph.slots().len().to_str()}")
	}
}

scaled : U16 -> Str
scaled = |n| {
	k = n * 2
	bound = Stage.render(|x| x + k)
	values = bound.inputs().map(
		|value| match value {
			Int(i) => i.to_str()
			_ => "not an integer"
		},
	)
	"${bound.value()} n=${Str.join_with(values, ",")}"
}

# The first call is folded while the compiler runs. The second reads the
# arguments, so its `n` exists only when the program runs.
main! = |args| {
	echo!("${scaled(3)}\n")
	echo!("${scaled(args.len().to_u16_wrap() * 0 + 5)}\n")
	Ok({})
}
