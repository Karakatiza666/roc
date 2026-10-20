# A match over a translator's result draws no "unconditional condition"
# warning.
#
# A description exists only while the compiler runs, so what a translator
# returns is known at compile time by design, and a `match` is how a program
# reads it. The three matches in `main!` read the result directly, through a
# top-level value, and through a local value. The `if` on a plain constant is
# the one condition here the warning is right about.
Stage := {}.{
	describe : Code(f) -> Try(U64, [Refused])
	describe = |code| Ok(code.graph().root_row().params.len())
}

double : F32 -> F32
double = |x| x * 2.0

described : Try(U64, [Refused])
described = Stage.describe(double)

main! = |_args| {
	direct = match Stage.describe(double) {
		Ok(n) => n.to_str()
		Err(Refused) => "refused"
	}
	through_top_level = match described {
		Ok(n) => n.to_str()
		Err(Refused) => "refused"
	}
	local = Stage.describe(double)
	through_local = match local {
		Ok(n) => n.to_str()
		Err(Refused) => "refused"
	}
	plain = if 1 + 1 == 2 "two" else "other"
	echo!("${direct} ${through_top_level} ${through_local} ${plain}\n")
	Ok({})
}
