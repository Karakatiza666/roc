# A method of a type declared in a function body, with a Code site at the
# enclosing function's type variable (Q17). The site is described at each
# use of the enclosing function, and a use that does not fix the variable is
# refused at the site. The refused use is a runtime error.
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

describe : Db.Q(r) -> Str
describe = |q| {
	Rows := { q : Db.Q(r) }.{
		to_inspect : Rows -> Str
		to_inspect = |rows| rows.q.filter(|_x| Bool.True).show()
	}
	Str.inspect(Rows.({ q: q }))
}

main! = |_args| {
	echo!("local: ${describe(Db.from("pet"))}\n")
	Ok({})
}
