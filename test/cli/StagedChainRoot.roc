# Lambdas at `Code` positions in a chain of calls, bound at the first call of
# the chain whose result is a `Code.Bound` (compiler-gaps.md Gap 1, R1, R2).
#
# `filter` and `select` are plain builders: they return a `Q`, not a
# `Code.Bound`. A lambda that reads a run-time value passes through them, as
# an argument or in the receiver, to `ready`, which is a compile-time root of
# its own. The chain runs once, while the compiler runs, and each call of
# `cheaper_than` or `between` gives its own inputs. The slots of a root are the
# slots of its lambdas in site order, and `first_slot` of each lambda's `Code`
# is where its own slots start. Two lambdas with one normal form are equal
# whatever their first slot.
Q := [Q(Str)].{
	from : Str -> Q
	from = |table| Q("FROM ${table}")

	filter : Q, Code(U16 -> Bool) -> Q
	filter = |Q(text), code| Q("${text} WHERE ${Q.slots(code)}")

	select : Q, Code(U16 -> U16) -> Q
	select = |Q(text), code| Q("SELECT ${Q.slots(code)} ${text}")

	ready : Q, Code(U16 -> Bool) -> Code.Bound(Str)
	ready = |Q(text), code| code.bound("${text} HAVING ${Q.slots(code)}")

	slots : Code(f) -> Str
	slots = |code| "slots ${code.graph().slots().len().to_str()} from ${code.first_slot().to_str()}"

	pair : Code(U16 -> Bool), Code(U16 -> Bool) -> Code.Bound(Str)
	pair = |a, b| a.bound("pair from ${a.first_slot().to_str()} and ${b.first_slot().to_str()}, ${if a == b "equal" else "not equal"}")

	show : Code.Bound(Str) -> Str
	show = |bound| {
		inputs = bound.inputs().map(
			|value| match value {
				Int(n) => n.to_str()
				_ => "other"
			},
		)
		"${bound.value()} inputs [${Str.join_with(inputs, ", ")}]"
	}
}

cheaper_than : U16 -> Str
cheaper_than = |limit| Q.show(Q.from("meds").filter(|m| m < limit).ready(|m| m > 0))

between : U16, U16 -> Str
between = |low, high| Q.from("meds").filter(|m| m >= low).select(|m| m + high).ready(|m| m < high) |> Q.show()

both : U16 -> Str
both = |high| Q.pair(|m| m < high, |m| m < high) |> Q.show()

main! = |_args| {
	echo!("${cheaper_than(3)}\n${cheaper_than(9)}\n${between(2, 40)}\n${both(7)}\n")
	Ok({})
}
