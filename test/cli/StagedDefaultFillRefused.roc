# A record literal in a reified function that leaves out a field whose
# default is computed is refused: the type does not carry the value
# (`DefaultComputed`), so the description cannot fill the field (Q18).
Labelled := { id : Str, label : Str ?? Str.concat("a", "b") }

size : Code(Str -> Labelled) -> U64
size = |code| code.graph().root_row().nodes.len()

main! = |_args| {
	echo!("${Str.inspect(size(|s| { id: s }))}\n")
	echo!("${Str.inspect(size(|s| { id: s, label: "c" }))}\n")
	Ok({})
}
