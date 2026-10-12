# A template's arguments are written into the description, so each one has to be
# a literal at the call. One computed when the program runs is refused, and the
# refusal points at the argument rather than at the template.

Stage := {}.{
	## Whether the description is a lambda, which is all this fixture needs.
	shape : Code(f) -> Str
	shape = |code| match Code.ir(code) {
		Lambda(_, _, _) => "lambda"
		_ => "other"
	}
}

scaled : F32 -> Code(F32 -> F32)
scaled = |factor| |x| x * factor

main! = |args| {
	measured = args.len().to_f32()
	echo!("${Stage.shape(scaled(measured))}\n")
	Ok({})
}
