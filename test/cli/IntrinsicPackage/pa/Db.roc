# A small translator: the filter and the counter take descriptions of code.
import T

Db := {}.{
	Q(row) := { log : Str }.{
		new : {} -> Q(row)
		new = |_| Q.({ log: "" })

		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log}[${code.graph().rows().len().to_str()}]" })

		show : Q(row) -> Str
		show = |q| q.log
	}

	select : Code(f) -> Str
	select = |code| code.graph().rows().len().to_str()

	count : Code(T -> Bool) -> Str
	count = |code| code.graph().rows().len().to_str()
}
