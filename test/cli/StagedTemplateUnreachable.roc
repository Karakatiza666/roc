# A call is a `Code` only when it calls a template, and the compiler calls a
# template by name. Reached through a binding, or imported from another module,
# there is no body the walk can read, so the call is refused rather than left
# for lowering to meet as a value with no layout.

Stage := {}.{
	## Whether the description is a lambda, which is all this fixture needs.
	shape : Code(f) -> Str
	shape = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

scaled : F32 -> Code(F32 -> F32)
scaled = |factor| |x| x * factor

maker = scaled

main! = |_args| {
	echo!("${Stage.shape(maker(2.0))}\n")
	Ok({})
}
