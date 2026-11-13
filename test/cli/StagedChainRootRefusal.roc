# A translator that refuses a node of a lambda in a chain, in a function
# (compiler-gaps.md Gap 1, R8).
#
# The chain up to `ready` is a compile-time root of its own. `roc check`
# evaluates it, so the refusal is a compile error at the lambda's node, also
# when the program calls the function only with run-time values and when the
# chain is in a branch. A root that binds inputs is never guarded, so a crash
# in a translator in a branch is a compile error too: lowered in place, the
# call would give the program no inputs.
Q := [Q(Str)].{
	from : Str -> Q
	from = |table| Q("FROM ${table}")

	filter : Q, Code(U16 -> Bool) -> Q
	filter = |Q(text), code| {
		root = code.graph().root_row()
		refused = root.nodes.find_first_index(|node| match node.op {
			Prim(p) => p.method == "times"
			_ => Bool.False
		})
		match refused {
			Ok(index) => code.refuse_at({ row: root.id, node: index.to_u32_wrap() }, "this target has no multiplication")
			Err(_) => Q("${text} WHERE ?")
		}
	}

	checked : Q, Code(U16 -> Bool) -> Q
	checked = |Q(text), code| if code.graph().slots().len() > 0 crash "the translator stopped" else Q(text)

	ready : Q -> Code.Bound(Str)
	ready = |Q(text)| Code.Bound.of(text)
}

show : Code.Bound(Str) -> Str
show = |bound| "${bound.value()} inputs ${bound.inputs().len().to_str()}"

plain : U16 -> Str
plain = |limit| show(Q.from("meds").filter(|m| m * 2 < limit).ready())

branched : Bool, U16 -> Str
branched = |flag, limit| if flag show(Q.from("meds").filter(|m| m * 3 < limit).ready()) else "none"

crashed : Bool, U16 -> Str
crashed = |flag, limit| if flag show(Q.from("meds").checked(|m| m < limit).ready()) else "none"

main! = |args| {
	n = args.len().to_u16_wrap()
	echo!("${plain(n)} ${branched(n > 5, n)} ${crashed(n > 5, n)}\n")
	Ok({})
}
