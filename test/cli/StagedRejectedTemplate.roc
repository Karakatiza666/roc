# A rejected literal in the lambda a template returns, which each call of the
# template describes.

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

make : F64 -> Code(F64 -> F64)
make = |k| |x| "<script>${x.to_str()}!".Html.width(x) + k

main! = |_args| {
	echo!("${Stage.render(make(2.0))}\n")
	Ok({})
}
