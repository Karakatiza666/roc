Words := {}.{
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
}
