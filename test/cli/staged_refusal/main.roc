# A translator refuses a node that an imported helper built (I9c).
#
# `Helpers.step(x)` inlines to `x * 3` from `Helpers.roc`, so the compiler
# names that module and its line and column, and highlights the call here.
import Helpers

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

scaled : U16 -> U16
scaled = |x| Helpers.step(x) + 1

shader : Str
shader = Stage.no_times(scaled)

main! = |_args| {
	echo!("shader: ${shader}\n")
	Ok({})
}
