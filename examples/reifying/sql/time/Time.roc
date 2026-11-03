# A point in time, as nanoseconds since the Unix epoch. A package of its own,
# which knows nothing of SQL: the type hides its representation, so a query
# that reifies a function over it names its operations and never reads its
# field. `../time_sql/` tells the SQL translator what they mean.
Time :: { nanos : I128 }.{
	from_nanos : I128 -> Time
	from_nanos = |nanos| Time.{ nanos }

	from_seconds : I64 -> Time
	from_seconds = |seconds| Time.{ nanos: seconds.to_i128() * 1_000_000_000 }

	is_eq : Time, Time -> Bool
	is_eq = |a, b| a.nanos == b.nanos

	is_lt : Time, Time -> Bool
	is_lt = |a, b| a.nanos < b.nanos

	is_gt : Time, Time -> Bool
	is_gt = |a, b| a.nanos > b.nanos

	## Written with whatever format the caller names: the SQL package binds
	## it in `Sql.Param`, and a JSON encoder would write `{"nanos": ..}`.
	encoder_for : _
}
