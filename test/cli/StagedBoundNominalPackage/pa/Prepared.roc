# The result of a query: opaque outside the package, built on `Code.Bound`.
Prepared(out) :: Code.Bound(Try(out, Str)).{
	of : Str -> Prepared(Str)
	of = |text| Prepared.(Code.Bound.of(Ok(text)))

	inputs : Prepared(out) -> List(Code.Value)
	inputs = |Prepared.(b)| b.inputs()

	value : Prepared(out) -> Try(out, Str)
	value = |Prepared.(b)| b.value()
}
