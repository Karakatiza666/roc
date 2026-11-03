# A function that returns a lambda calling an intrinsic is reify-only. A call
# of it in a clause is described. A top-level constant is evaluated while the
# compiler runs, so a call of it there is an error, although evaluating it
# calls nothing.
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
	is_close : F64, F64 -> Bool
}

make = |k| |x| Text.is_close(x, k)

doubler = make(2.0)

main! = |_args| {
	rows : Db.Q({ x : F64 })
	rows = Db.Q.new({})
	echo!("clause: ${rows.filter(|r| make(2.0)(r.x)).show()}\n")
	Ok({})
}
