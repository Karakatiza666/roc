# A point in time, as nanoseconds. The type hides its representation, so a
# description names its functions and never reads its fields. Its encoder
# writes it with any format that can write an `I128`. It has a number literal
# conversion, so `41` can be a `Time`.
Time :: { nanos : I128 }.{
	from_nanos : I128 -> Time
	from_nanos = |nanos| Time.{ nanos }

	from_numeral : Numeral -> Try(Time, [InvalidNumeral(Str)])
	from_numeral = |numeral| {
		Inner : I128
		match Inner.from_numeral(numeral) {
			Ok(nanos) => Ok(Time.{ nanos })
			Err(err) => Err(err)
		}
	}

	zero : () -> Time
	zero = || Time.{ nanos: 0 }

	is_before : Time, Time -> Bool
	is_before = |a, b| a.nanos < b.nanos

	encoder_for : fmt -> (Time, List(U8) -> Try(List(U8), []))
		where [fmt.encode_i128 : I128, List(U8) -> Try(List(U8), [])]
	encoder_for = |_format| {
		Fmt : fmt
		|t, out| Fmt.encode_i128(t.nanos, out)
	}
}
