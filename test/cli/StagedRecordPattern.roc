# A translator that reads a description through record patterns.
#
# `Block({ defs, end })` reads the fields of a `Code.Tree` payload, and
# `|{ name, ty, presence: _ }|` reads the fields of a record entry of a
# `Code.Ty`. Each field it reads is on the cycle of a recursive type.
Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| {
		graph = Code.graph(code)
		row = graph.root_row()
		params = Str.join_with(row.params.map(Stage.ty), ", ")
		"${params} : ${Stage.tree(graph.to_tree(row.id))}"
	}

	tree : Code.Tree -> Str
	tree = |t| match t {
		Op(o) => "op(${Str.join_with(o.args.map(Stage.tree), ", ")})"
		Param(k) => "p${k.to_str()}"
		Def(n) => "n${n.to_str()}"
		Block({ defs, end }) => {
			last = match end {
				Value(vals) => Str.join_with(vals.map(Stage.tree), ", ")
				_ => "other"
			}
			"block ${defs.len().to_str()} ${last}"
		}
		_ => "?"
	}

	ty : Code.Ty -> Str
	ty = |t| match t {
		Record(fields) => "{${Str.join_with(fields.map(|{ name, ty, presence: _ }| "${name}: ${Stage.ty(ty)}"), ", ")}}"
		_ => t.name()
	}
}

f : { a : U64, b : { c : U64 } } -> U64
f = |r| {
	y = r.a + r.b.c
	y * y
}

main! = |_args| {
	echo!("${Stage.describe(f)}\n")
	Ok({})
}
