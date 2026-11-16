# A method a `where` requirement selects, which holds a Code site at its
# own type variables (Q14 of roc-reify-structural-proposal.md). The
# evidence edge that selects the method describes it at the edge's types
# (design.md "Code Instance Tables"). An edge at the variables of a
# generic function is an entry of that function's table, which each
# closing use of the function fixes. A use of that function at the
# variables of another (`outer`) gives the callee the entry of its own
# table.
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
}

tidy_twice : w -> w where [w.tidy : w -> w]
tidy_twice = |w| w.tidy().tidy()

## The edge that selects `Wrap.tidy` is at this function's `r`.
tidy_rows : Db.Q({ name : Str, ..r }) -> Str
tidy_rows = |q| tidy_twice(Wrap.({ q: q })).q.show()

## A use of `tidy_rows` at this function's `r`.
outer : Db.Q({ name : Str, ..r }) -> Str
outer = |q| tidy_rows(q)

Owner : { id : Str, name : Str, city : Str }

Pet : { name : Str }

main! = |_args| {
	owners : Db.Q(Owner)
	owners = Db.from("owner")
	pets : Db.Q(Pet)
	pets = Db.from("pet")
	echo!("${tidy_twice(Wrap.({ q: owners })).q.show()}\n")
	echo!("${tidy_rows(owners)}\n")
	echo!("${tidy_rows(pets)}\n")
	echo!("${outer(owners)}\n")
	echo!("${outer(pets)}\n")
	Ok({})
}
