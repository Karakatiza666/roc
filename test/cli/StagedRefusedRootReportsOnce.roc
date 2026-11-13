# A compile-time constant whose evaluation reaches a refused site. The
# description step reported the refusal, and the site lowers to a crash
# that says so, so the constant's evaluation discards its result and
# reports nothing more.
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

describe_bump : {} -> Str
describe_bump = |_| Stage.describe(bump)

label : Str
label = describe_bump({})

main! = |_args| {
	echo!("${label}\n")
	Ok({})
}
