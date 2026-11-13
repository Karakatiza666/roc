# A record literal in a reified function that leaves out a field with a
# default the type carries (`Default(value)` in `Code.Ty`) is described with
# the field set to the default's literal, as the program sets it when it runs
# (Q18 of roc-reify-structural-proposal.md). A nested nominal's default is
# filled too.
Kind := [Tablet, Syrup]

Inner := { a : I64, b : Str ?? "b" }

Med := { id : Str, stock : I32 ?? 0, tags : List(Str) ?? ["x"], kind : Kind ?? Tablet, inner : Inner ?? { a: 1 }, ratio : F32 ?? 0.5 }

tree : Code(Str -> Med) -> Str
tree = |code| {
	graph = code.graph()
	Str.inspect(graph.to_tree(graph.root_row().id))
}

make_med : Str -> Med
make_med = |s| { id: s }

main! = |_args| {
	echo!("tree: ${tree(make_med)}\n")
	echo!("inline: ${Str.inspect(tree(|s| { id: s, stock: 3 }) == tree(|s| { id: s, stock: 3, tags: ["x"], kind: Tablet, inner: { a: 1, b: "b" }, ratio: 0.5 }))}\n")
	echo!("run: ${Str.inspect(make_med("q"))}\n")
	Ok({})
}
