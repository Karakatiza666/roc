# A translator binds each primitive by id, and refuses a `Prim` it has no
# binding for. It refuses the `Prim` of a builtin, which is no intrinsic, so
# the report has no line about an intrinsic.
Stage := {}.{
	bound : List(Code.PrimId)
	bound = [Code.prim(Str.concat)]

	emit : Code(Str -> Bool) -> Str
	emit = |code| {
		root = code.graph().root_row()
		unbound = root.nodes.find_first_index(
			|node| match node.op {
				Prim(p) => !Stage.bound.contains(p.id)
				_ => Bool.False
			},
		)
		match unbound {
			Ok(index) => code.refuse_at({ row: root.id, node: index.to_u32_wrap() }, "this target has no binding for this primitive")
			Err(_) => "bound"
		}
	}
}

shader : Str
shader = Stage.emit(|s| s.is_empty())

main! = |_args| {
	echo!("shader: ${shader}\n")
	Ok({})
}
