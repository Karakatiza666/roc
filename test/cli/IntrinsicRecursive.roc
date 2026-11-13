# A mutually recursive pair that reaches an intrinsic is reify-only as a
# whole. In a clause it is described; at run time it is an error, and the
# chain goes through both definitions.
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

ping = |n, s| if n == 0 Text.is_email(s) else pong(n - 1, s)

pong = |n, s| if n == 0 False else ping(n - 1, s)

main! = |args| {
	people : Db.Q({ name : Str })
	people = Db.Q.new({})
	echo!("clause: ${people.filter(|p| pong(2, p.name)).show()}\n")
	if args.len() > 100 {
		echo!("run: ${Str.inspect(pong(2, "a"))}\n")
	}
	Ok({})
}
