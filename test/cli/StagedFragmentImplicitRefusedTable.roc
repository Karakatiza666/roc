# A `to_inspect` whose site captures a value, so its table at the owner type
# is refused (Q17). The refusal is reported once, and the call that
# inspection makes of the method is a runtime error.
Db := {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} | ${Str.inspect(code.graph().root_row().params.len())}" })

		show : Q(row) -> Str
		show = |q| q.log
	}

	from : Str -> Q(row)
	from = |name| Q.({ log: name })
}

Rows(r) := { q : Db.Q(r) }.{
	to_inspect : Rows(r) -> Str
	to_inspect = |rows| rows.q.filter(|_x| rows.q.show() == "").show()
}

main! = |_args| {
	pets : Db.Q({ id : Str })
	pets = Db.from("pet")
	echo!("before\n")
	echo!("local: ${Str.inspect(Rows.({ q: pets }))}\n")
	Ok({})
}
