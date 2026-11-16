# A refusal inside a site that a `for` loop's `iter` call reaches is
# reported at the loop's iterable, and the loop becomes a runtime error
# (D1 of roc-reify-structural-proposal.md).
Db := {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} | ${code.graph().root_row().params.len().to_str()}" })

		show : Q(row) -> Str
		show = |q| q.log
	}

	from : Str -> Q(row)
	from = |name| Q.({ log: name })
}

Stamp :: { n : U8 }.{
	n_of : Stamp -> U8
	n_of = |s| s.n
}

shifted : U8 -> U8
shifted = |n| Stamp.n_of(Stamp.{ n }) + 1

Pet : { id : Str, name : Str, age : U8 }

Rows(r) := { q : Db.Q(r) }.{
	iter : Rows({ age : U8, ..r }) -> Iter(Str)
	iter = |rows| [rows.q.filter(|x| shifted(x.age) > 3).show()].iter()
}

main! = |_args| {
	pets : Db.Q(Pet)
	pets = Db.from("pet")
	rows : Rows(Pet)
	rows = Rows.({ q: pets })
	for line in rows {
		echo!("${line}\n")
	}
	Ok({})
}
