# A method that holds a Code site at its own type variables, called by a
# direct dispatch (Q14 of roc-reify-structural-proposal.md). The dispatch
# `W.({ .. }).count_down()` at fixed types hands the method the table of
# the use, as a call `W.count_down(..)` does, and the recursive dispatch
# in the method's body is an entry of the method's own table (design.md
# "Code Instance Tables").
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
	count_down : W(a) -> Str
	count_down = |x| if x.n_of() == 0 x.query().filter(|_r| Bool.True).show() else x.pred().count_down()
}

Owner : { id : Str, name : Str }

main! = |_args| {
	owners : Db.Q(Owner)
	owners = Db.from("owner")
	pets : Db.Q(Str)
	pets = Db.from("pet")
	echo!("${W.count_down(W.({ q: owners, n: 3 }))}\n")
	echo!("${W.({ q: pets, n: 2 }).count_down()}\n")
	Ok({})
}
