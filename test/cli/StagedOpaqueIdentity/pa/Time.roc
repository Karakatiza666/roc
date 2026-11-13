# A point in time, as nanoseconds. Package `pb` declares another type of this
# name.
Time :: { nanos : I64 }.{
	from_nanos : I64 -> Time
	from_nanos = |nanos| Time.{ nanos }

	is_lt : Time, Time -> Bool
	is_lt = |a, b| a.nanos < b.nanos
}
