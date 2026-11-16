# A `Code.Bound` translator whose result function reads a run-time value.
#
# The run-time argument `k` keeps the call from being a compile-time root, so
# the compiler refuses to bind the captured value. StagedBoundFunctionResult.roc
# has the cases that bind.
Stage := {}.{
	real : Code(U16 -> U16), U16 -> Code.Bound({ text : Str, run : U16 -> U16 })
	real = |code, k| Code.bound(code, { text: "slots/${Code.graph(code).slots().len().to_str()}", run: |y| y + k })
}

with_runtime : U16 -> Str
with_runtime = |n| {
	result = Stage.real(|x| x + n, n).value()
	"${result.text} run=${(result.run)(4).to_str()}"
}

main! = |args| {
	n = args.len().to_u16_wrap()
	echo!("${with_runtime(n)}\n")
	Ok({})
}
