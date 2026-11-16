# An intrinsic is a primitive at every site already, so a cut that lists one
# is refused at the entry, as a cut that lists a builtin is. An intrinsic used
# as a value inside a description is refused, as a function of an opaque type
# used as a value is, and so is an intrinsic named as the function to
# describe: it has no body to read.
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

Tr := {}.{
	twice : U64 -> U64
	twice = |x| x * 2

	code_primitives = [Code.prim(Tr.twice), Code.prim(Text.is_email)]

	arity : Code(f) -> U64
	arity = |code| code.graph().root_row().params.len()
}

main! = |_args| {
	people : Db.Q({ emails : List(Str) })
	people = Db.Q.new({})
	echo!("value: ${people.filter(|p| p.emails.map(Text.is_email).len() > 0).show()}\n")
	echo!("named: ${Tr.arity(Text.is_email).to_str()}\n")
	Ok({})
}
