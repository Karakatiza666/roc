# The platform's required entry here is `process_string`. It is a root
# because the platform requires it, whatever its name. An intrinsic inside a
# lambda written at a `Code` place is described, so it is fine there. The
# same intrinsic called by the entry at run time is an error.
app [process_string] { pf: platform "../str/platform/main.roc" }

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

process_string : Str -> Str
process_string = |input| {
	people : Db.Q({ name : Str })
	people = Db.Q.new({})
	described = people.filter(|p| Text.is_email(p.name)).show()
	if input == "" described else Str.inspect(Text.is_email(input))
}
