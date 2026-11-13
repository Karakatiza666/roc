# A form D1 of roc-reify-structural-proposal.md refuses by name: a site
# that binds inputs has one slot order, so it cannot be an instance site.
Db := {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} | ${code.graph().root_row().params.len().to_str()}" })

		show : Q(row) -> Str
		show = |q| q.log
	}

	from : Str -> Q(row)
	from = |name| Q.({ log: name })
}

Fmt := [Default].{
	default : () -> Fmt
	default = || Default

	encode_i64 : I64, List(U8) -> Try(List(U8), [])
	encode_i64 = |n, out| Ok(out.concat(n.to_str().to_utf8()))
}

Stage := {}.{
	## The row argument fixes the type of the lambda's parameter.
	render : Code.Binds(Code(r -> Bool), Fmt), r -> Code.Bound(Str)
	render = |code, _row| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")
}

pick : { n : I64, ..r }, I64 -> Str
pick = |row, least| Stage.render(|x| x.n > least, row).value()

main! = |_args| {
	echo!("${pick({ n: 1, m: 2 }, 0)}\n")
	Ok({})
}
