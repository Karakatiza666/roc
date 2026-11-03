# A small translator: each step writes the fields of the row it filters.
Db := {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} | ${Db.fields(code.graph().root_row().params)}" })

		show : Q(row) -> Str
		show = |q| q.log
	}

	from : Str -> Q(row)
	from = |name| Q.({ log: name })

	fields = |params| match params {
		[Record(fields)] => Str.join_with(fields.map(|f| "${f.name}:${Str.inspect(f.ty)}"), ",")
		_ => "other"
	}
}
