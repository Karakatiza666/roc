# A definition that calls an intrinsic at run time is reify-only. Inside a
# lambda written at a `Code` place it is described, so it is fine there. A
# call of it that runs is an error, and a dev run crashes only when it
# reaches that call.
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

hot = |s| Text.is_email(s)

main! = |args| {
	people : Db.Q({ name : Str })
	people = Db.Q.new({})
	echo!("clause: ${people.filter(|p| hot(p.name)).show()}\n")
	if args.len() > 100 {
		name = "a"
		echo!("run: ${Str.inspect(hot(name))}\n")
	} else {
		echo!("not taken\n")
	}
	Ok({})
}
