# A translator refuses a node that an imported helper built through a call in
# the helper's module (I9c).
#
# `Helpers.bumped(x)` inlines to `step(x) + 1`, and `step(x)` inlines to `x * 3`,
# both in `Helpers.roc`. Every frame of the report shows its place as
# `path:line:col`, and the frame in `Helpers.roc` names that file.
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
scaled = |x| Helpers.bumped(x) + 1

shader : Str
shader = Stage.no_times(scaled)

main! = |_args| {
	echo!("shader: ${shader}\n")
	Ok({})
}
