# A translator refuses a node of a `Code.Inlined(f)` site while the compiler
# evaluates a top-level value (I9c).
#
# `step(x)` inlines to `x * 3`, and `scaled` also builds `x * 3` itself. The
# two are one node (N5a), so the compiler reports the refusal at both places:
# once in `step`'s body, reached through the call `step(x)`, and once in
# `scaled`.
Stage := {}.{
	no_times : Code.Inlined(U16 -> U16) -> Str
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

step : U16 -> U16
step = |x| x * 3

scaled : U16 -> U16
scaled = |x| step(x) + x * 3

shader : Str
shader = Stage.no_times(scaled)

main! = |_args| {
	echo!("shader: ${shader}\n")
	Ok({})
}
