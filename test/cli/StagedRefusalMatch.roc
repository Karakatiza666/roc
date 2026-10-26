# A translator refuses a node inside an arm of a flat `match` (N7a). The arms
# are written out of the union's order, and the tree is rebuilt in it, so the
# refusal must still name the source region of the node in the arm it was
# written in.
Stage := {}.{
	no_times : Code.Inlined({ tag : [A, B, C], x : U16 } -> U16) -> Str
	no_times = |code| {
		graph = code.inline()
		root = graph.root_row()
		refused = root.nodes.find_first_index(|node| match node.op {
			Prim(p) => p.method == "times"
			_ => Bool.False
		})
		match refused {
			Ok(index) => code.refuse_at({ row: root.id, node: index.to_u32_wrap() }, "this target has no multiplication")
			Err(_) => "no multiplication"
		}
	}
}

scaled : { tag : [A, B, C], x : U16 } -> U16
scaled = |input| match input.tag {
	C => input.x + 1
	A => input.x * 3
	B => input.x + 2
}

shader : Str
shader = Stage.no_times(scaled)

main! = |_args| {
	echo!("shader: ${shader}\n")
	Ok({})
}
