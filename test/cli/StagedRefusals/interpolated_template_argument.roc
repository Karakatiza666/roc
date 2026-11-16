# An interpolated literal of a type of your own as a template argument. The
# checker binds every interpolated value to a name, so the argument is not a
# constant form, however constant its pieces are.
Stage := {}.{
	shape : Code(f) -> Str
	shape = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

Html := [Html(Str)].{
	from_interpolation : List(Str) -> Try((Iter(Str) -> Html), [InvalidInterpolation(Str)])
	from_interpolation = |segments|
		Str.from_interpolation(segments).map_ok(|assemble| |values| Html(assemble(values)))
}

labelled : Html -> Code(U16 -> U16)
labelled = |_html| |x| x

main! = |_args| {
	echo!("${Stage.shape(labelled("a${"b"}c".Html))}\n")
	Ok({})
}
