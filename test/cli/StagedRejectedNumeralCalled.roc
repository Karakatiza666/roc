# The same rejected numeral in a function the program also calls.

Stage := {}.{
	render : Code(f) -> Str
	render = |code| "rows ${Code.graph(code).rows().len().to_str()}"
}

Meters := { m : F64 }.{
	from_numeral : Numeral -> Try(Meters, [InvalidNumeral(Str)])
	from_numeral = |_n| Err(InvalidNumeral("never"))

	scale : Meters, F64 -> F64
	scale = |me, f| me.m * f
}

stretch : F64 -> F64
stretch = |x| 3.0.Meters.scale(x)

main! = |_args| {
	echo!("${Stage.render(stretch)} ${stretch(1.0).to_str()}\n")
	Ok({})
}
