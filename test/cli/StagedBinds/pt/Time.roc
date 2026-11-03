# A point in time, as nanoseconds. The type hides its representation, so a
# description names its functions and never reads its fields. Its encoder
# writes it with any format that can write an `I128`.
Time :: { nanos : I128 }.{
	from_nanos : I128 -> Time
	from_nanos = |nanos| Time.{ nanos }

	is_before : Time, Time -> Bool
	is_before = |a, b| a.nanos < b.nanos

	encoder_for : fmt -> (Time, List(U8) -> Try(List(U8), []))
		where [fmt.encode_i128 : I128, List(U8) -> Try(List(U8), [])]
	encoder_for = |_format| {
		Fmt : fmt
		|t, out| Fmt.encode_i128(t.nanos, out)
	}
}
