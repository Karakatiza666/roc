# A `to_inspect` that inspection does not call, because its type is not
# `Rows(r) -> Str` for each `r` (design.md "Inspect Overrides"). It holds a
# Code site at the owner's argument (Q17). Inspection renders the default
# form, so no type occurrence describes the method. A written call of the
# method is described as usual.
Db := {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} | ${Str.inspect(code.graph().root_row().params)}" })

		show : Q(row) -> Str
		show = |q| q.log
	}

	from : Str -> Q(row)
	from = |name| Q.({ log: name })
}

Rows(r) := { q : Db.Q(r) }.{
	to_inspect : Rows(I64) -> Str
	to_inspect = |rows| rows.q.filter(|_x| Bool.True).show()
}

main! = |_args| {
	rows : Rows(I64)
	rows = Rows.({ q: Db.from("nums") })
	echo!("written: ${rows.to_inspect()}\n")
	echo!("inspect: ${Str.inspect(rows)}\n")
	Ok({})
}
