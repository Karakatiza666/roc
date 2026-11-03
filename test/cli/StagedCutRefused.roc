# The item `code_primitives` lists the functions and constants a translator
# reads by name, each as `Code.prim(f)`. Each entry names a top-level function
# or constant, names it once, and names no primitive. Here `Tr.twice_id` is no
# `Code.prim` call, the second `Tr.twice` repeats the first, `Str.concat` is a
# builtin and `Stamp.from` is a function of an opaque type, so these four are
# refused. `Tr.limit` is a constant, which a cut can list.
Stamp :: { n : U64 }.{
	from : U64 -> Stamp
	from = |n| Stamp.{ n }
}

Tr := {}.{
	twice : U64 -> U64
	twice = |x| x * 2

	limit : U64
	limit = 3

	twice_id = Code.prim(Tr.twice)

	code_primitives = [Code.prim(Tr.twice), Code.prim(Tr.limit), Code.prim(Tr.twice), Tr.twice_id, Code.prim(Str.concat), Code.prim(Stamp.from)]

	arity : Code(f) -> U64
	arity = |code| code.graph().root_row().params.len()
}

wobble : U64 -> U64
wobble = |x| Tr.twice(x) + Tr.limit

main! = |_args| {
	echo!("${Tr.arity(wobble).to_str()}\n")
	Ok({})
}
