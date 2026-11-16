# A use at the type variables of a generic function, whose evidence
# selects a method with a Code site from a type alone (Q14 of
# roc-reify-structural-proposal.md). The recursive `is_even` and `is_odd`
# select `describe` from the type of their argument, and `g` calls them at
# its own `a`. The methods derived evidence selects are those of the
# dispatchers' owners, which `g`'s types already name, so the use in `g`
# is refused by name (design.md "Code Instance Tables"), and runs as a
# crash at every closing use of `g`.
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

W(a) := { q : Db.Q(a), n : U64 }.{
	n_of = |W.(w)| w.n
	pred = |W.(w)| W.({ q: w.q, n: w.n - 1 })
	describe = |W.(w)| w.q.filter(|_r| Bool.True).show()
	is_even = |x| if x.n_of() == 0 x.describe() else x.pred().is_odd()
	is_odd = |x| if x.n_of() == 0 x.describe() else x.pred().is_even()
}

g : W(a) -> Str
g = |w| W.is_even(w)

Owner : { id : Str, name : Str }

main! = |_args| {
	owners : Db.Q(Owner)
	owners = Db.from("owner")
	pets : Db.Q(Str)
	pets = Db.from("pet")
	echo!("${g(W.({ q: owners, n: 4 }))}\n")
	echo!("${g(W.({ q: pets, n: 3 }))}\n")
	Ok({})
}
