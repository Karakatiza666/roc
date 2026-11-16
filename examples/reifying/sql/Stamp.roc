# A point in time, as nanoseconds, for `extensions.roc`. The type hides its
# representation, so a reified function names its operations and never reads
# its field, and the SQL translator knows none of them by itself.
Stamp :: { nanos : I128 }.{
	from_nanos : I128 -> Stamp
	from_nanos = |nanos| Stamp.{ nanos }

	is_lt : Stamp, Stamp -> Bool
	is_lt = |a, b| a.nanos < b.nanos

	is_eq : Stamp, Stamp -> Bool
	is_eq = |a, b| a.nanos == b.nanos

	encoder_for : _
}
