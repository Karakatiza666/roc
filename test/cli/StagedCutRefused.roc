# The item `code_primitives` lists the functions a translator reads by name.
# Each entry names a top-level function, and names it once. Here `Tr.limit`
# is a constant and `5` is no name, so both are refused, and so is the second
# `Tr.twice`.
Tr := {}.{
	twice : U64 -> U64
	twice = |x| x * 2

	limit : U64
	limit = 3

	code_primitives = (Tr.twice, Tr.limit, Tr.twice, 5)

	arity : Code(f) -> U64
	arity = |code| code.graph().root_row().params.len()
}

wobble : U64 -> U64
wobble = |x| Tr.twice(x) + 1

main! = |_args| {
	echo!("${Tr.arity(wobble).to_str()}\n")
	Ok({})
}
