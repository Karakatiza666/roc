# A function named where a `Code` is expected, staged end to end.
#
# `describe` asks for a description of an `F32 -> F32`, and `double` is one, so
# the argument checks against the function type inside the `Code` rather than
# against the `Code` itself. The compiler then describes `double`'s body, and
# `describe` reads that description while the program is built: the string this
# prints is computed by a stage, not at run time.
StagedCodePosition := {}.{
	describe : Code(F32 -> F32) -> Str
	describe = |code| match code.ir() {
		Lambda(params, _, _) => "lambda/${params.len().to_str()}"
		_ => "other"
	}
}

double : F32 -> F32
double = |x| x * 2.0

staged : Str
staged = StagedCodePosition.describe(double)

main! = |_args| {
	echo!("${staged}\n")
	Ok({})
}
