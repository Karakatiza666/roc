# A site the compiler cannot describe: a function read from a list at an
# index known only at run time names no definition.
Lib :: {}.{
	Stage := {}.{
		describe : Code(f) -> Str
		describe = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
	}

	step : F32 -> Str
	step = |x| x.to_str()

	bump : F32, U64 -> Str
	bump = |x, i| {
		chosen = match [step, step].get(i) {
			Ok(f) => f
			Err(_) => step
		}
		chosen(x)
	}

	staged : Str
	staged = Stage.describe(bump)
}
