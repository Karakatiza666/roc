# A literal that its conversion rejects is a compile error in a function that
# only a `Code` site reaches, as it is in one that is called. Nothing runs
# `mark` here: the description is the only thing that reads it.

Stage := {}.{
	render : Code(f) -> Str
	render = |code| "rows ${Code.graph(code).rows().len().to_str()}"
}

Html := [Html(Str)].{
	from_interpolation : List(Str) -> Try((List(Str) -> Html), [InvalidInterpolation(Str)])
	from_interpolation = |segments|
		if segments.any(|segment| segment.contains("<script")) {
			Err(InvalidInterpolation("no scripts"))
		} else {
			Str.from_interpolation(segments).map_ok(|assemble| |values| Html(assemble(values)))
		}

	width : Html, F64 -> F64
	width = |h, f| match h {
		Html(text) => if text.is_empty() 0.0 else f
	}
}

mark : F64 -> F64
mark = |x| "<script>${x.to_str()}!".Html.width(x)

main! = |_args| {
	echo!("${Stage.render(mark)}\n")
	Ok({})
}
