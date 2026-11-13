# Gap 1 end to end, in the shape of a query library: a `Query` keeps a list
# of closures, its builders take `Code` lambdas that read run-time values, and
# the terminal `ready` has no `Code` of its own. It returns a `Code.Bound` that
# `Code.Bound.of` builds, whose `Prepared` holds a `read` function.

## A nominal error type keeps the result type of `ready` closed. An open
## union such as `[Bad(Str)]` in a return type leaves it open, and a call
## with an open type is no compile-time root.
Error := [Bad(Str)]

Clause : [Now, Before], (U64 -> Str) -> Try(Str, Error)

Prepared(out) :: { statement : Str, read : List(Str) -> Try(out, Error) }.{
	statement : Prepared(out) -> Str
	statement = |Prepared.(p)| p.statement

	read : Prepared(out), List(Str) -> Try(out, Error)
	read = |Prepared.(p), rows| (p.read)(rows)
}

Query(row) :: { table : Str, clauses : List(Clause), columns : List(Clause) }.{
	from : Str -> Query(row)
	from = |table| Query.({ table, clauses: [], columns: [] })

	filter : Query(row), Code(row -> Bool) -> Query(row)
	filter = |Query.(q), code| Query.({ ..q, clauses: q.clauses.append(clause_of(code)) })

	select : Query(row), Code(row -> U16) -> Query(row)
	select = |Query.(q), code| Query.({ ..q, columns: q.columns.append(clause_of(code)) })

	render : Query(row), (U64 -> Str) -> Try((List(Str), List(Str)), Error)
	render = |Query.(q), param| {
		columns = q.columns.map_try(|c| c(Now, param))?
		clauses = q.clauses.map_try(|c| c(Now, param))?
		Ok((columns, clauses))
	}

	ready : Query(row) -> Code.Bound(Try(Prepared(U64), Error))
	ready = |Query.(q)| {
		param = |k| "@p${k.to_str()}"
		rendered = render(Query.(q), param)
		count = (q.clauses.len() + q.columns.len()).to_u64()
		Code.Bound.of(
			rendered.map_ok(
				|(columns, clauses)| {
					shown = if columns.is_empty() "*" else Str.join_with(columns, ", ")
					condition = if clauses.is_empty() "" else " WHERE ${Str.join_with(clauses, " AND ")}"
					Prepared.({ statement: "SELECT ${shown} FROM ${q.table}${condition}", read: |rows| Ok(rows.len().to_u64() + count) })
				},
			),
		)
	}
}

## A clause that names the placeholders of its lambda's slots, numbered
## across the chain from `first_slot`.
clause_of : Code(_fn) -> Clause
clause_of = |code| {
	first = code.first_slot()
	slots = code.graph().slots().len().to_u64()
	|at, param| match at {
		Now => Ok("[${Str.join_with(placeholders(first, slots, param), " ")}]")
		Before => Err(Error.Bad("before"))
	}
}

placeholders : U64, U64, (U64 -> Str) -> List(Str)
placeholders = |first, slots, param|
	if slots == 0 [] else [param(first)].concat(placeholders(first + 1, slots - 1, param))

Med : { price : U16, stock : U16 }

meds : Query(Med)
meds = Query.from("meds")

cheaper_than : U16, U16 -> Code.Bound(Try(Prepared(U64), Error))
cheaper_than = |limit, extra| meds.filter(|m| m.price < limit).select(|m| m.stock + extra).filter(|m| m.stock > 0 and m.price != limit).ready()

everything : Code.Bound(Try(Prepared(U64), Error))
everything = meds.ready()

show : Code.Bound(Try(Prepared(U64), Error)) -> Str
show = |bound| {
	inputs = bound.inputs().map(
		|value| match value {
			Int(n) => n.to_str()
			_ => "other"
		},
	)
	match bound.value() {
		Ok(p) => "${p.statement()} inputs [${Str.join_with(inputs, ", ")}] read ${Str.inspect(p.read(["a", "b"]))}"
		Err(_) => "err"
	}
}

main! = |args| {
	n = args.len().to_u16_wrap()
	echo!("${show(cheaper_than(n + 10, n + 20))}\n${show(cheaper_than(n + 30, n))}\n${show(everything)}\n")
	Ok({})
}
