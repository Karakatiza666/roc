# A method the compiler selects from a type alone, which holds a Code site
# at its own type variables (Q14 of roc-reify-structural-proposal.md). The
# recursive `is_even` and `is_odd` select `describe` from the type of
# their argument while the compiler specializes them, and no checked
# evidence node names it, so no edge keys its instance table. The use is
# refused by name (design.md "Code Instance Tables"), and runs as a
# crash.
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

Owner : { id : Str, name : Str }

main! = |_args| {
	owners : Db.Q(Owner)
	owners = Db.from("owner")
	echo!("${W.is_even(W.({ q: owners, n: 4 }))}\n")
	Ok({})
}
