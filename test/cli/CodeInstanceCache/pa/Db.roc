# A translator that writes the string literals of each row it filters.
Db := {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} | ${Db.literals(code)}" })

		show : Q(row) -> Str
		show = |q| q.log
	}

	from : Str -> Q(row)
	from = |name| Q.({ log: name })

	literals : Code(f) -> Str
	literals = |code| {
		graph = Code.graph(code)
		found = graph.rows().map(|row| row.nodes.keep_oks(|node| match node.op {
			Lit(Str(text)) => Ok(text)
			_ => Err(NotAStr)
		}))
		Str.join_with(List.join(found), ",")
	}
}
