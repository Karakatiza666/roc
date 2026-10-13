# A staged function the compiler cannot describe, and the report it produces.
#
# The walk stops at the first construct outside the description and records what
# stopped it. A call to a definition written in Roc is described, and its body
# is described beside the root, so `loud`'s body is inside the description; so
# is the `Str.concat` in it, under the name the compiler provides it by. A
# function an `if` chose is called in each branch, but a function read from a
# list at an index known only at run time names no definition to describe, so
# normalization stops there and the report names that reason rather than
# leaving the region to speak for itself.
Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

step : F32 -> Str
step = |x| x.to_str()

loud : F32 -> Str
loud = |x| Str.concat(x.to_str(), "!")

bump : F32, U64 -> Str
bump = |x, i| {
	chosen = match [step, loud].get(i) {
		Ok(f) => f
		Err(_) => step
	}
	chosen(x)
}

staged : Str
staged = Stage.describe(bump)

main! = |_args| {
	echo!("${staged}\n")
	Ok({})
}
