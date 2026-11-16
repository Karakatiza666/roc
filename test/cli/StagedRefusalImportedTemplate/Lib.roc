# A translator, and a generic function whose Code site reads an opaque
# type, which a description has no form for.
Lib :: {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} | ${code.graph().root_row().params.len().to_str()}" })

		show : Q(row) -> Str
		show = |q| q.log
	}

	from : Str -> Q(row)
	from = |name| Q.({ log: name })

	Stamp :: { n : U8 }.{
		n_of : Stamp -> U8
		n_of = |s| s.n
	}

	shifted : U8 -> U8
	shifted = |n| Stamp.n_of(Stamp.{ n }) + 1

	render : Q({ age : U8, ..r }) -> Str
	render = |q| q.filter(|x| shifted(x.age) > 3).show()
}
