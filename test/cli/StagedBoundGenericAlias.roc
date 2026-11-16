# A generic function's `Code.Bound` call reached through exact procedure
# aliases (R7 of the Gap 1 design): a use of an alias of an alias, a forward
# use of an alias in another generic function, and a method bound to an
# alias. Each use carries its instance table through the aliases to `fetch`.
Q := [Q(Str)].{
	from : Str -> Q
	from = |name| Q(name)

	filter : Q, Code(U16 -> Bool) -> Q
	filter = |Q(text), code| Q("${text} where slots ${Code.graph(code).slots().len().to_str()} from ${code.first_slot().to_str()}")

	ready : Q -> Code.Bound(Try(Str, [NotFound, ..e]))
	ready = |Q(text)| Code.Bound.of(Ok(text))

	fetch : Q, U16, U16 -> Code.Bound(Try(Str, [NotFound, ..e]))
	fetch = |_q, least, most| Q.from("meds").filter(|m| m > least).filter(|m| m < most).ready()

	get = fetch
}

inner = Q.fetch

other = inner

forward = |least, most| other(Q.from("x"), least, most)

show = |bound| {
	text = match bound.value() {
		Ok(t) => t
		Err(_) => "err"
	}
	"${text} inputs ${Str.inspect(bound.inputs())}"
}

main! = |_args| {
	a : Code.Bound(Try(Str, [NotFound, Other]))
	a = other(Q.from("x"), 1, 9)
	b : Code.Bound(Try(Str, [NotFound]))
	b = forward(2, 8)
	c : Code.Bound(Try(Str, [NotFound, Third]))
	c = Q.from("x").get(3, 7)
	echo!("${show(a)}\n${show(b)}\n${show(c)}\n")
	Ok({})
}
