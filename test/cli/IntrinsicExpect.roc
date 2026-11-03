# A top-level `expect` runs, so one that reaches an intrinsic is an error, and
# `roc test` counts it as blocked by a compiler error. An `expect` that only
# describes code runs normally.
Ops := {}.{
	count : Code(Str -> Bool) -> U64
	count = |code| code.graph().rows().len()
}

Text :: {}.{
	is_email : Str -> Bool
}

hot = |s| Text.is_email(s)

expect Ops.count(|s| hot(s)) == 1

expect hot("a@b.c")
