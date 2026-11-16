# A query fragment whose lambda uses an intrinsic is fine to call at run time:
# the lambda is described. A use of the intrinsic outside the lambda runs.
# A row requirement inside the filter lambda is described too; the same
# requirement outside the lambda runs.
Db := {}.{
	Q(row) := { log : Str }.{
		new : {} -> Q(row)
		new = |_| Q.({ log: "" })

		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log}[${code.graph().rows().len().to_str()}]" })

		show : Q(row) -> Str
		show = |q| q.log
	}
}

Text :: {}.{
	is_email : Str -> Bool
}

Clock := { n : U64 }.{
	now : Clock -> Bool
}

named_only = |q| Db.Q.filter(q, |x| Text.is_email(x.e))

checked = |q, e| if Text.is_email(e) q else Db.Q.filter(q, |x| Text.is_email(x.e))

row_now = |q| Db.Q.filter(q, |x| x.t.now())

row_first = |q, row| if row.t.now() q else Db.Q.filter(q, |x| x.t.now())

main! = |args| {
	people : Db.Q({ e : Str })
	people = Db.Q.new({})
	clocks : Db.Q({ t : Clock })
	clocks = Db.Q.new({})
	echo!("fragment: ${named_only(people).show()}\n")
	echo!("row: ${row_now(clocks).show()}\n")
	if args.len() > 100 {
		echo!("outside: ${checked(people, "a").show()}\n")
		clock : Clock
		clock = { n: 1 }
		echo!("row outside: ${row_first(clocks, { t: clock }).show()}\n")
	}
	Ok({})
}
