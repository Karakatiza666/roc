Frag := {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} ${Code.graph(code).root_row().params.len().to_str()}" })

		show : Q(row) -> Str
		show = |q| q.log
	}

	from : Str -> Q(row)
	from = |name| Q.({ log: name })

	named_only : Q({ name : Str, ..r }) -> Q({ name : Str, ..r })
	named_only = |q| q.filter(|x| x.name != "")
}
