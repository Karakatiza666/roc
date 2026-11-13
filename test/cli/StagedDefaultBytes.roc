# A record literal in a reified function that leaves out a field fills it
# from the type (Q18). Where the default holds an embedded file, the file is
# one `Bytes` literal, the same literal that the file gives where it is
# written. Here the defaults of `inner` and `both` hold the file, so the
# description reads the value from the type. `Code.Ty` spells the default as
# a `List` of `Int` values, because `Code.Value` has no bytes form.
import "staged_bytes_blob.bin" as blob : List(U8)

Inner := { a : I64, data : List(U8) ?? blob }

Med := { id : Str, inner : Inner ?? { a: 1 } }

Pair := { id : Str, both : (List(U8), I64) ?? (blob, 2) }

med : Code(Str -> Med) -> Str
med = |code| {
	graph = code.graph()
	Str.inspect(graph.to_tree(graph.root_row().id))
}

pair : Code(Str -> Pair) -> Str
pair = |code| {
	graph = code.graph()
	Str.inspect(graph.to_tree(graph.root_row().id))
}

main! = |_args| {
	echo!("med: ${med(|s| { id: s })}\n")
	echo!("med same: ${Str.inspect(med(|s| { id: s }) == med(|s| { id: s, inner: { a: 1, data: blob } }))}\n")
	echo!("pair same: ${Str.inspect(pair(|s| { id: s }) == pair(|s| { id: s, both: (blob, 2) }))}\n")
	m : Med
	m = { id: "q" }
	echo!("run: ${Str.inspect(m)}\n")
	Ok({})
}
