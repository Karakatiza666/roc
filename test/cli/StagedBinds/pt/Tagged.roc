# A value with a tag. The type hides its representation, so a description
# never reads its fields. Its encoder writes the value with the format's
# own `encode_tagged`, which a `where` requirement selects.
Tagged(a) :: { v : a }.{
	of : a -> Tagged(a)
	of = |v| Tagged.{ v }

	is_set : Tagged(a) -> Bool
	is_set = |_t| Bool.True

	encoder_for : fmt -> (Tagged(a), List(U8) -> Try(List(U8), []))
		where [fmt.encode_tagged : a, List(U8) -> Try(List(U8), [])]
	encoder_for = |_format| {
		Fmt : fmt
		|t, out| Fmt.encode_tagged(t.v, out)
	}
}
