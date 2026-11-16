# A point in time, as nanoseconds. `from_nanos` and `to_nanos` name `Time`, so
# they are primitives of the type. `shifted` names no `Time`, so a description
# reads its body, which builds the opaque record and has no description.
Time :: { nanos : I64 }.{
	from_nanos : I64 -> Time
	from_nanos = |nanos| Time.{ nanos }

	to_nanos : Time -> I64
	to_nanos = |t| t.nanos

	shifted : I64 -> I64
	shifted = |nanos| Time.to_nanos(Time.{ nanos }) + 1
}
