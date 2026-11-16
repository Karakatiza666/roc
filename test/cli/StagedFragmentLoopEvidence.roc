# A `for` loop whose `iter` method takes `where` evidence that selects a
# method holding a Code site at its own type variables. The evidence edge
# describes the method at the loop's types (design.md "Code Instance
# Tables"), and both lowerings pass that table.
Db := {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} | filter ${Str.inspect(code.graph().root_row().params)}" })

		show : Q(row) -> Str
		show = |q| q.log
	}

	from : Str -> Q(row)
	from = |name| Q.({ log: name })
}

Wrap(a) := { q : a }.{
	tidy : Wrap(Db.Q({ name : Str, ..r })) -> Wrap(Db.Q({ name : Str, ..r }))
	tidy = |w| Wrap.({ q: w.q.filter(|x| x.name != "") })

	show : Wrap(Db.Q(r)) -> Str
	show = |w| w.q.show()
}

Rows(w) := { item : w }.{
	iter : Rows(w) -> Iter(w) where [w.tidy : w -> w]
	iter = |rows| [rows.item.tidy()].iter()
}

Owner : { id : Str, name : Str }

Pet : { name : Str }

main! = |_args| {
	owners : Db.Q(Owner)
	owners = Db.from("owner")
	pets : Db.Q(Pet)
	pets = Db.from("pet")
	for owner in Rows.({ item: Wrap.({ q: owners }) }) {
		echo!("${owner.show()}\n")
	}
	for pet in Rows.({ item: Wrap.({ q: pets }) }) {
		echo!("${pet.show()}\n")
	}
	Ok({})
}
