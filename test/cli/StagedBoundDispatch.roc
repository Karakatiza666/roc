# A generic `Code.Bound` call reached through a method call: a method of a
# known type in a generic function, and a method called directly. The method
# call passes its Code instance table to the method (R7 of the Gap 1 design).
Q := [Q(Str)].{
	from : Str -> Q
	from = |name| Q(name)

	filter : Q, Code(U16 -> Bool) -> Q
	filter = |Q(text), code| Q("${text} slots ${Code.graph(code).slots().len().to_str()}")

	ready : Q -> Code.Bound(Try(Str, [NotFound, ..e]))
	ready = |Q(text)| Code.Bound.of(Ok(text))

	fetch : Q, U16 -> Code.Bound(Try(Str, [NotFound, ..e]))
	fetch = |_q, least| Q.from("meds").filter(|m| m > least).ready()
}

show = |bound| {
	text = match bound.value() {
		Ok(t) => t
		Err(_) => "err"
	}
	"${text} inputs ${Str.inspect(bound.inputs())}"
}

go : Q, U16 -> Code.Bound(Try(Str, [NotFound, ..e]))
go = |q, least| q.fetch(least)

main! = |_args| {
	a : Code.Bound(Try(Str, [NotFound, Other]))
	a = go(Q.from("meds"), 3)
	b : Code.Bound(Try(Str, [NotFound]))
	b = Q.from("pets").fetch(4)
	echo!("${show(a)}\n${show(b)}\n")
	Ok({})
}
