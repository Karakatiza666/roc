# A derived equality reaches the `is_eq` of its element type. In a clause the
# comparison is described; at run time it reaches the intrinsic.
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

Hit := { s : U64 }.{
	is_eq : Hit, Hit -> Bool
}

main! = |args| {
	rows : Db.Q({ h : Hit })
	rows = Db.Q.new({})
	echo!("clause: ${rows.filter(|r| [r.h] == [r.h]).show()}\n")
	if args.len() > 100 {
		h : Hit
		h = { s: 1 }
		echo!("run: ${Str.inspect([h] == [h])}\n")
	}
	Ok({})
}
