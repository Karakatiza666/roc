# A `for` loop whose `iter` use is refused crashes in place of the loop at
# run time: what runs before the loop runs, and neither the loop's body nor
# what follows it runs.
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
	echo!("before\n")
	for line in rows {
		echo!("in loop ${line}\n")
	}
	echo!("after\n")
	Ok({})
}
