# A value that computes a query fragment, with no annotation. Nothing in this
# module fixes its row, so the app's use fixes it, and the value's entry
# wrapper describes the fragment's site at that row.
Lib := {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} | ${Lib.fields(code.graph().root_row().params)}" })
	}

	fields = |params| match params {
		[Record(fields)] => Str.join_with(fields.map(|f| "${f.name}:${Str.inspect(f.ty)}"), ",")
		_ => "other"
	}

	named_only : Lib.Q({ name : Str, ..r }) -> Lib.Q({ name : Str, ..r })
	named_only = |q| q.filter(|x| x.name != "")

	pick = if Bool.True Lib.named_only else Lib.named_only
}
