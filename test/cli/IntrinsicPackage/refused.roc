# A translator in the app binds each primitive by id, and refuses the `Prim`
# of an intrinsic that a package declares. The report names that intrinsic.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Text

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
shader = Stage.emit(|s| Text.is_email(s))

main! = || {
	Stdout.line!("shader: ${shader}")
}
