# Reading inside an opaque nominal from outside its module. Roc itself forbids
# it, so the program is refused before any description.
import Secret

Stage := {}.{
	shape : Code(f) -> Str
	shape = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

peek : Secret -> U16
peek = |s| s.code

main! = |_args| {
	echo!("${Stage.shape(peek)}\n")
	Ok({})
}
