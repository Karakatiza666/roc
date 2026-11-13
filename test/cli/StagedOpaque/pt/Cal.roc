# A namespace whose nested type hides its representation. `parse` names
# `Cal.Time`, which this module declares, so it is a primitive.
Cal :: {}.{
	Time :: { days : U64 }.{
		is_lt : Cal.Time, Cal.Time -> Bool
		is_lt = |a, b| a.days < b.days
	}

	parse : Str -> Cal.Time
	parse = |text| Cal.Time.{ days: text.count_utf8_bytes() }
}
