# A lambda written at a `Code` position that reads names a pattern bound while
# the program runs.
#
# The report names each capture by the identifier its pattern bound: a string
# pattern's capture by the name inside `${ ... }`, whatever spacing wrote it,
# and an `as` pattern by the name after `as`.
Stage := {}.{
	render : Code(Str -> Bool) -> Str
	render = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

spaced : Str -> Str
spaced = |s| match s {
	"key=${ value }" => Stage.render(|x| x == value)
	_ => ""
}

renamed : (Str, Str) -> Str
renamed = |pair| match pair {
	(_, _) as whole => Stage.render(|x| x == whole.0)
}

main! = |_args| {
	echo!("${spaced("key=v")}${renamed(("a", "b"))}\n")
	Ok({})
}
