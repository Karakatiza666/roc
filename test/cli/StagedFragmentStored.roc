# A query fragment reached as a stored function value or through a method
# the program calls by its syntax (Q16 of roc-reify-structural-proposal.md).
# A constant that holds a fragment, an alias of a fragment used as a value,
# and a `for` loop over a type whose `iter` holds a site each describe the
# site at the types they fix.
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

# A constant that holds the fragment at a fixed type.
ops : { f : Db.Q(Pet) -> Db.Q(Pet) }
ops = { f: named_only }

# An alias at a fixed type, and an alias at the fragment's own type.
for_pets : Db.Q(Pet) -> Db.Q(Pet)
for_pets = named_only

any_alias = named_only

# `for` calls `iter`, which holds a site at the type's row.
Rows(r) := { q : Db.Q(r) }.{
	iter : Rows({ name : Str, ..r }) -> Iter(Str)
	iter = |rows| [rows.q.filter(|x| x.name != "").show()].iter()
}

main! = |_args| {
	pets : Db.Q(Pet)
	pets = Db.from("pet")
	rows : Rows(Pet)
	rows = Rows.({ q: pets })
	echo!("constant: ${(ops.f)(pets).show()}\n")
	echo!("alias call: ${for_pets(pets).show()}\n")
	echo!("alias value: ${[pets].map(for_pets).map(|q| q.show()).first().ok_or("")}\n")
	echo!("generic alias value: ${[pets].map(any_alias).map(|q| q.show()).first().ok_or("")}\n")
	for line in rows {
		echo!("iter: ${line}\n")
	}
	Ok({})
}
