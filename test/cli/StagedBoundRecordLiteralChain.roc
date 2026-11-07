# Lambdas that return record literals, in a chain whose terminal call has no
# `Code` of its own (compiler-gaps.md row 4, R6). Each literal's field kind
# is quantified with `rename`, which does not hold it, so the chain binds
# the captured values with no annotated helper.
Write(row) :: { table : Str, sets : List(Str) }.{
	into : Str -> Write(row)
	into = |table| Write.({ table, sets: [] })

	set_at : Write(row), Code(row -> patch) -> Write(row)
	set_at = |Write.(w), code| {
		slots = code.graph().slots().len().to_str()
		Write.({ ..w, sets: w.sets.append("slot ${code.first_slot().to_str()} of ${slots}") })
	}

	ready : Write(row) -> Code.Bound(Str)
	ready = |Write.(w)| Code.Bound.of("UPDATE ${w.table} SET ${Str.join_with(w.sets, ", ")}")
}

Med : { name : Str, price : U16 }

meds : Write(Med)
meds = Write.into("meds")

rename : Str, U16 -> Code.Bound(Str)
rename = |name, extra| meds.set_at(|_| { name: name }).set_at(|m| { price: m.price + extra }).ready()

show : Code.Bound(Str) -> Str
show = |bound| {
	inputs = bound.inputs().map(
		|value| match value {
			Str(s) => s
			Int(n) => n.to_str()
			_ => "other"
		},
	)
	"${bound.value()} inputs [${Str.join_with(inputs, ", ")}]"
}

main! = |args| {
	n = args.len().to_u16_wrap()
	echo!("${show(rename("ada", n + 1))}\n${show(rename("bo", n + 2))}\n")
	Ok({})
}
