# A Code site at the type variables of a method the compiler calls with no
# written use (Q17 of roc-reify-structural-proposal.md). Str.inspect calls
# `to_inspect`, and `==` on a record that holds the type calls `is_eq`, so
# no written use fixes the method's types. The site in `to_inspect`, and the
# use in `is_eq` of a function that holds one, are refused at the method.
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

Pet : { id : Str, name : Str, age : U8 }

named_only : Db.Q({ name : Str, ..r }) -> Db.Q({ name : Str, ..r })
named_only = |q| q.filter(|x| x.name != "")

Rows(r) := { q : Db.Q(r) }.{
	to_inspect : Rows(r) -> Str
	to_inspect = |rows| rows.q.filter(|_x| Bool.True).show()
}

Named(r) := { q : Db.Q(r) }.{
	is_eq : Named({ name : Str, ..r }), Named({ name : Str, ..r }) -> Bool
	is_eq = |a, b| named_only(a.q).show() == b.q.show()
}

main! = |_args| {
	pets : Db.Q(Pet)
	pets = Db.from("pet")
	rows : Rows(Pet)
	rows = Rows.({ q: pets })
	named : Named(Pet)
	named = Named.({ q: pets })
	echo!("direct: ${named_only(pets).show()}\n")
	echo!("inspect: ${Str.inspect(rows)} ${Str.inspect({ r: rows })}\n")
	echo!("eq: ${Str.inspect(named == named)} ${Str.inspect({ n: named } == { n: named })}\n")
	Ok({})
}
