# A recursive method with no annotation, which holds a Code site at a type
# variable that only its `where` requirements reach (Q14 of
# roc-reify-structural-proposal.md). The recursive dispatch
# `x.pred().count_where()` is closed at the use's types, so its evidence is
# derived from its callable: the compiler selects `count_where` again from
# the type `pred` returns, and no checked evidence node names that
# selection, so no edge keys its instance table. Each use is refused by
# name (design.md "Code Instance Tables"), and runs as a crash.
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
	query = |W.(w)| w.q
	count_where = |x| if x.n_of() == 0 Db.Q.filter(x.query(), |_r| Bool.True).show() else x.pred().count_where()
}

Owner : { id : Str, name : Str }

main! = |_args| {
	owners : Db.Q(Owner)
	owners = Db.from("owner")
	pets : Db.Q(Str)
	pets = Db.from("pet")
	echo!("${W.({ q: owners, n: 2 }).count_where()}\n")
	echo!("${W.count_where(W.({ q: pets, n: 1 }))}\n")
	Ok({})
}
