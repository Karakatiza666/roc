# A closed call of an intrinsic in a reify-only definition is not evaluated
# while the compiler runs: a compile-time root that reaches an intrinsic is
# not selected. The same closed call in code that runs is an error.
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

hot = |s| Text.is_email(s) and Text.is_email("closed@example.com")

main! = |args| {
	people : Db.Q({ name : Str })
	people = Db.Q.new({})
	echo!("clause: ${people.filter(|p| hot(p.name) and Text.is_email("x")).show()}\n")
	if args.len() > 100 {
		echo!("closed: ${Str.inspect(Text.is_email("closed@example.com"))}\n")
	}
	Ok({})
}
