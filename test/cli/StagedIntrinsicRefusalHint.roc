# A translator binds each primitive by id, and refuses a `Prim` it has no
# binding for. It refuses the `Prim` of an intrinsic, so the report adds a
# line that says the intrinsic has no Roc body. It refuses a `Prim` whose
# evidence names an intrinsic, so that report names the intrinsic too. The
# translator writes no code for either line.
Text :: {}.{
	is_email : Str -> Bool
}

Hit := { n : U64 }.{
	is_eq : Hit, Hit -> Bool
}

Stage := {}.{
	bound : List(Code.PrimId)
	bound = [Code.prim(Str.concat)]

	emit : Code(f) -> Str
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
shader = Stage.emit(|s| Text.is_email(s))

same : Hit -> Bool
same = |h| [h] == [h]

equal : Str
equal = Stage.emit(same)

main! = |_args| {
	echo!("shader: ${shader}, equal: ${equal}\n")
	Ok({})
}
