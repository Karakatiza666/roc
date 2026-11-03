# A query fragment: a generic function that holds a `Code` site whose
# function type names the fragment's own type variables (D1 of
# roc-reify-structural-proposal.md). The fragment has no description of its
# own. Each use that fixes its types describes the site at those types.
Db := {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} | ${Db.fields(code.graph().root_row().params)}" })

		## A method whose own annotation names the row's field.
		only_named : Q({ name : Str, ..r }) -> Q({ name : Str, ..r })
		only_named = |q| q.filter(|x| x.name != "")

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
Owner : { id : Str, name : Str, city : Str }
Pair : { a : U8, b : U8 }
Words : { a : Str, b : Str }

named_only : Db.Q({ name : Str, ..r }) -> Db.Q({ name : Str, ..r })
named_only = |q| q.filter(|x| x.name != "")

# Unannotated, with a direct call.
named_direct = |q| Db.Q.filter(q, |x| x.name != "")

# A fragment that calls a fragment.
card : Db.Q({ id : Str, name : Str, ..r }) -> Db.Q({ id : Str, name : Str, ..r })
card = |q| named_only(q).filter(|x| x.id != "")

# The site's lambda dispatches on a variable of the fragment's `where`.
same_ab : Db.Q({ a : t, b : t, ..r }) -> Db.Q({ a : t, b : t, ..r }) where [t.is_eq : t, t -> Bool]
same_ab = |q| q.filter(|x| x.a == x.b)

# No use fixes this fragment's types, so it has no description.
never : Db.Q({ name : Str, ..r }) -> Db.Q({ name : Str, ..r })
never = |q| q.filter(|x| x.name == "never")

# A site whose function type names no variable of the generic function that
# holds it is described once.
tagged : a -> (a, Str)
tagged = |x| {
	pets : Db.Q(Pet)
	pets = Db.from("fixed")
	(x, pets.filter(|p| p.age > 3).show())
}

main! = |_args| {
	pets : Db.Q(Pet)
	pets = Db.from("pet")
	owners : Db.Q(Owner)
	owners = Db.from("owner")
	pairs : Db.Q(Pair)
	pairs = Db.from("pair")
	words : Db.Q(Words)
	words = Db.from("words")
	as_value : Db.Q(Pet) -> Db.Q(Pet)
	as_value = named_only
	(_, one) = tagged(1)
	(_, two) = tagged("two")
	echo!("annotated: ${named_only(pets).show()}\n")
	echo!("annotated: ${named_only(owners).show()}\n")
	echo!("direct: ${named_direct(owners).show()}\n")
	echo!("value: ${as_value(pets).show()}\n")
	echo!("card: ${card(owners).show()}\n")
	echo!("method: ${pets.only_named().show()}\n")
	echo!("method: ${owners.only_named().show()}\n")
	echo!("where: ${same_ab(pairs).show()}\n")
	echo!("where: ${same_ab(words).show()}\n")
	echo!("once: ${one} ${two}\n")
	Ok({})
}
