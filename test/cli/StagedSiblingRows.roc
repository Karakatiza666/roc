# A lambda written at a `Code` position keeps its rows open until the binding
# around it generalizes.
#
# A call relates its arguments only after it has checked every one, so the
# table before the lambda fixes the row the lambda reads after the lambda was
# checked. The second clause of a chain reads the parameter record the first
# one opened and adds a field to it. A row nothing else fixes still closes on
# exactly the fields the lambda reads.
Tag(p, row) :: { name : Str }.{
	make : Str -> Tag(p, row)
	make = |name| Tag.({ name: name })

	keep : Tag(p, row), Code((p, row -> Bool)) -> Tag(p, row)
	keep = |tag, _| tag
}

Stage := {}.{
	two : Tag(p, a), Code((a -> Bool)) -> Str
	two = |_, code| Stage.signature(code)

	pairs : Tag(p, a), Tag(q, b), Code((a, b -> Bool)) -> Str
	pairs = |_, _, code| Stage.signature(code)

	alone : Code(a -> Bool) -> Str
	alone = |code| Stage.signature(code)

	params_of : Tag(p, row), Code((p, row -> Bool)) -> Str
	params_of = |_, code| Stage.signature(code)

	signature : Code(f) -> Str
	signature = |code| Str.join_with(Code.graph(code).root_row().params.map(|param| param.name()), " | ")
}

Row : { id : I64, name : Str, score : I64 }

rows : Tag({}, Row)
rows = Tag.make("rows")

main! = |_args| {
	# A local value shares its rows, so the clauses below fix `p` here.
	open_params : Tag(_, Row)
	open_params = Tag.make("rows")

	echo!("${Stage.two(rows, |r| r.id > 0)}\n")
	echo!("${Stage.pairs(rows, rows, |r, s| r.id == s.score)}\n")
	echo!("${Stage.alone(|r| r.id > 0)}\n")
	echo!("${Stage.params_of(open_params.keep(|b, r| r.id >= b.low), |b, r| r.id <= b.high)}\n")
	Ok({})
}
