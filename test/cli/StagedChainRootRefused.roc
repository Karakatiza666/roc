# A lambda that reads a run-time value passes only through calls that take it,
# or a call that passed it on, as an argument or in the receiver
# (compiler-gaps.md Gap 1, R1, R10). The first three cases stop before the
# call whose result is a `Code.Bound`, so the read is refused. In the last
# one, the call binds two lambdas and the walk refuses one of them, so the
# call refuses the other one too: its slots would not line up.
Q := [Q(Str)].{
	from : Str -> Q
	from = |table| Q("FROM ${table}")

	filter : Q, Code(U16 -> Bool) -> Q
	filter = |Q(text), _code| Q("${text} WHERE")

	ready : Q, Code(U16 -> Bool) -> Code.Bound(Str)
	ready = |Q(text), code| code.bound(text)

	ready_in : { query : Q }, Code(U16 -> Bool) -> Code.Bound(Str)
	ready_in = |args, code| code.bound(Q.text(args.query))

	text : Q -> Str
	text = |Q(t)| t
}

# A branch: the `if` is no call.
branched : Bool, U16 -> Str
branched = |flag, limit| {
	base = Q.from("meds")
	(if flag base.filter(|m| m < limit) else base).ready(|m| m > 0).value()
}

# A binding: a lambda never follows a name.
named : U16 -> Str
named = |limit| {
	q = Q.from("meds").filter(|m| m < limit)
	q
}.ready(|m| m > 0).value()

# A record argument: the record is no call.
in_record : U16 -> Str
in_record = |limit| Q.ready_in({ query: Q.from("meds").filter(|m| m < limit) }, |m| m > 0).value()

# A refused lambda refuses each lambda its call binds.
mixed : U16 -> Str
mixed = |limit| {
	var $cap = limit
	$cap = $cap + 1
	Q.from("meds").filter(|m| m < $cap).ready(|m| m < limit).value()
}

main! = |_args| {
	echo!("${branched(Bool.True, 3)} ${named(3)} ${in_record(3)} ${mixed(3)}\n")
	Ok({})
}
