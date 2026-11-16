# A call that binds the run-time read of its `Code` lambda, whose type an
# error reaches only after the call's frame finished: the row type of `q` is
# fixed by `fix(q)`, and then the `where` method of `ready` meets the bad
# signature of `Med.describe`. Checking retires the call with no operand
# evaluated, so the lambda below it has no description and no root.
Prepared :: { statement : Str }.{
	statement : Prepared -> Str
	statement = |Prepared.(p)| p.statement
}

Query(row) :: { table : Str, clauses : List(U64) }.{
	from : Str -> Query(row)
	from = |table| Query.({ table, clauses: [] })

	filter : Query(row), Code(row -> Bool) -> Query(row)
	filter = |Query.(q), code| Query.({ ..q, clauses: q.clauses.append(code.graph().slots().len().to_u64()) })

	ready : Query(row) -> Code.Bound(Try(Prepared, [Bad])) where [row.describe : row -> Str]
	ready = |Query.(q)| Code.Bound.of(Ok(Prepared.({ statement: "SELECT FROM ${q.table} ${Str.inspect(q.clauses)}" })))
}

Med := { price : U16 }.{
	describe : Med -> Missing
	describe = |_| "med"
}

fix : Query(Med) -> {}
fix = |_| {}

cheaper_than : U16 -> Code.Bound(Try(Prepared, [Bad]))
cheaper_than = |limit| {
	q = Query.from("meds")
	bound = q.filter(|_m| limit > 0).ready()
	fix(q)
	bound
}

main! = |args| {
	n = args.len().to_u16_wrap()
	echo!(Str.inspect(cheaper_than(n).inputs().len()))
	Ok({})
}
