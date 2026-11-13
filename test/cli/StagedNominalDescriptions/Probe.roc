## A Code site at a type variable of a generic function: each closing use
## describes it at the type that use fixes.
Probe :: {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |_q, code| Q.({ log: Str.inspect(code.graph().root_row().params) })

		show : Q(row) -> Str
		show = |q| q.log
	}

	of : row -> Q(row)
	of = |_row| Q.({ log: "" })
}
