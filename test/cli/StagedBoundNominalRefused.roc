# A type that only holds a nominal type built on `Code.Bound` is no opt-in
# (R5 option A' of the Gap 1 design): a `Try` around it, or a record that
# holds it. The chain ends in that type, so the run-time read is refused,
# and the report names the type the chain ended in.
Error := [Bad(Str)]

Prepared(out) :: Code.Bound(Try(out, Error))

Q := [Q(Str)].{
	from : Str -> Q
	from = |name| Q(name)

	filter : Q, Code(U16 -> Bool) -> Q
	filter = |Q(text), code| Q("${text} slots ${Code.graph(code).slots().len().to_str()}")

	ready : Q -> Try(Prepared(Str), Error)
	ready = |Q(text)| Ok(Prepared.(Code.Bound.of(Ok(text))))

	held : Q -> { prepared : Prepared(Str) }
	held = |Q(text)| { prepared: Prepared.(Code.Bound.of(Ok(text))) }
}

outside : U16 -> Try(Prepared(Str), Error)
outside = |n| Q.from("meds").filter(|m| m > n).ready()

in_record : U16 -> { prepared : Prepared(Str) }
in_record = |n| Q.from("meds").filter(|m| m < n).held()

main! = |args| {
	n = args.len().to_u16_wrap()
	shown = match outside(n) {
		Ok(_) => "ok"
		Err(_) => "err"
	}
	_ = in_record(n)
	echo!("${shown}\n")
	Ok({})
}
