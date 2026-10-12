# A `Code` names a function's parameter or what a function returns, and nothing
# else. A function that returns one is a template the compiler calls, so it
# cannot itself be passed around: the annotation below is refused, and the
# refusal has to stop the build rather than leave a description-less `Code` for
# lowering to meet.

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

apply : (F32 -> Code(F32 -> F32)) -> Str
apply = |maker| Stage.shape(maker(2.0))

main! = |_args| {
	echo!("${apply(scaled)}\n")
	Ok({})
}
