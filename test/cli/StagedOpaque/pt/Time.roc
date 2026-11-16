# A point in time, as nanoseconds. The type hides its representation, so each
# function and constant here whose type names `Time` is a primitive of the
# type: a description names it and never reads its body.
Time :: { nanos : I128 }.{
	from_nanos : I128 -> Time
	from_nanos = |nanos| Time.{ nanos }

	to_nanos : Time -> I128
	to_nanos = |t| t.nanos

	is_lt : Time, Time -> Bool
	is_lt = |a, b| a.nanos < b.nanos

	is_before : Time, Time -> Bool
	is_before = |a, b| a.nanos < b.nanos

	epoch : Time
	epoch = Time.{ nanos: 0 }

	# Its type names no `Time`, so a description reads its value.
	days_in_week : U8
	days_in_week = 7
}
