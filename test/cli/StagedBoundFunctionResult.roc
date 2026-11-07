# A `Code.Bound` translator whose result type holds a function type
# (compiler-gaps.md row 2, roc-reify-surrealdb).
#
# The call that binds the captured value is a compile-time root whose value
# may hold a function that its type fixes: a real field (`run`, which captures
# a value the translator computed) or a phantom type argument
# (`Cap(U16 -> U16)`). The same phantom over a type that holds no function
# (`Cap(Arrow)`) binds too. StagedBoundFunctionResultRefused.roc has the case
# that stays refused.
Arrow := {}

Cap(f) := [Cap(Str)].{
	text : Cap(f) -> Str
	text = |Cap(t)| t
}

Stage := {}.{
	phantom : Code(U16 -> U16) -> Code.Bound(Cap(U16 -> U16))
	phantom = |code| Code.bound(code, Cap("slots/${Code.graph(code).slots().len().to_str()}"))

	real : Code(U16 -> U16) -> Code.Bound({ text : Str, run : U16 -> U16 })
	real = |code| {
		count = Code.graph(code).slots().len().to_u16_wrap()
		Code.bound(code, { text: "slots/${count.to_str()}", run: |y| y + count })
	}

	plain : Code(U16 -> U16) -> Code.Bound(Cap(Arrow))
	plain = |code| Code.bound(code, Cap("slots/${Code.graph(code).slots().len().to_str()}"))
}

inputs : Code.Bound(a) -> Str
inputs = |bound| "in=${bound.inputs().len().to_str()}"

with_phantom : U16 -> Str
with_phantom = |n| {
	bound = Stage.phantom(|x| x + n)
	"${bound.value().text()} ${inputs(bound)}"
}

with_real : U16 -> Str
with_real = |n| {
	bound = Stage.real(|x| x + n)
	result = bound.value()
	"${result.text} run=${(result.run)(4).to_str()} ${inputs(bound)}"
}

with_plain : U16 -> Str
with_plain = |n| {
	bound = Stage.plain(|x| x + n)
	"${bound.value().text()} ${inputs(bound)}"
}

main! = |args| {
	n = args.len().to_u16_wrap()
	echo!("${with_phantom(n)}\n${with_real(n)}\n${with_plain(n)}\n")
	Ok({})
}
