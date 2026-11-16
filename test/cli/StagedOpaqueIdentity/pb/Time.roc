# A point in time, as seconds. Package `pa` declares another type of this
# name.
Time :: { seconds : I64 }.{
	from_seconds : I64 -> Time
	from_seconds = |seconds| Time.{ seconds }

	is_lt : Time, Time -> Bool
	is_lt = |a, b| a.seconds < b.seconds
}
