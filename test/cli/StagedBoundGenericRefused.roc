# A translator in a generic chain refuses a node at each closing use. The
# report stands at the lambda, and the use reaches it.
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

	ready : Q -> Code.Bound(Try(Str, [NotFound, ..e]))
	ready = |Q(text)| Code.Bound.of(Ok(text))
}

refused = |limit| Q.from("meds").filter(|m| m * 2 < limit).ready()

crashed = |limit| Q.from("meds").checked(|m| m < limit).ready()

main! = |args| {
	n = args.len().to_u16_wrap()
	a : Code.Bound(Try(Str, [NotFound]))
	a = refused(n)
	b : Code.Bound(Try(Str, [NotFound]))
	b = crashed(n)
	echo!("${Str.inspect(a.inputs())} ${Str.inspect(b.inputs())}\n")
	Ok({})
}
