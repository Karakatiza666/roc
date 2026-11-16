Db :: {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} | ${Str.inspect(code.graph().root_row().params.len())}" })

		show : Q(row) -> Str
		show = |q| q.log
	}

	of : row -> Q(row)
	of = |_| Q.({ log: "q" })

	empty : {} -> Q(row)
	empty = |{}| Q.({ log: "q" })
}
