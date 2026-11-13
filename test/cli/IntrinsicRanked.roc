# A function name written as a `Code` argument is described, not run. The
# same name used as a value in code that runs is an error at the name.
Db := {}.{
	select : Code(f) -> Str
	select = |code| code.graph().rows().len().to_str()
}

Hit := { s : U64 }.{
	## The score of the row. An intrinsic.
	score : Hit -> U64
}

ranked : Hit -> U64
ranked = |hit| hit.score() + 1

main! = |args| {
	seed : List(Hit)
	seed = [{ s: 1 }]
	echo!("select: ${Db.select(ranked)}\n")
	if args.len() > 100 {
		echo!("map: ${Str.inspect(seed.map(ranked))}\n")
	}
	Ok({})
}
