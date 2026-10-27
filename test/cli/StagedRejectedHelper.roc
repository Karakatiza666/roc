# A rejected literal in a helper that the function at a `Code` position calls.

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

bad : F64 -> F64
bad = |x| "<script>${x.to_str()}!".Html.width(x)

mark : F64 -> F64
mark = |x| bad(x) + 1.0

main! = |_args| {
	echo!("${Stage.render(mark)}\n")
	Ok({})
}
