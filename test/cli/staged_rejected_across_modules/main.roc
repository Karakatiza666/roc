# A rejected literal in a function of another module that only a `Code` site
# reaches.
import Words

Stage := {}.{
	render : Code(f) -> Str
	render = |code| "rows ${Code.graph(code).rows().len().to_str()}"
}

main! = |_args| {
	echo!("${Stage.render(Words.mark)}\n")
	Ok({})
}
