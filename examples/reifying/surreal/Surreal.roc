import Ql
import Encode
import Types
import Translate
import Schema

# A SurrealDB ORM over reified Roc functions: rows are ordinary Roc records,
# and every constraint, filter and projection is a Roc function that the
# compiler reifies and the translator reads.
#
# This file has the parts in sections: the foundations (links, ids,
# datetimes and tables), the schema builder and the query API.
Surreal :: {}.{

	## What the translator does not look inside. A call to one of these stays
	## a call in the reified description, and the translator knows its form:
	## `get` is a traversal, `id` the record id, `==` on ids `=`, `key`
	## `record::id`, and `<` and `<=` on datetimes the same operators. Their
	## bodies have no SurrealQL form (a `crash`, a byte loop, a field of the
	## backing record). The cut belongs to the type that owns the method with
	## the `Code` parameter, so each such type below lists it again.
	code_primitives = (Link.get, Link.id, Id.is_eq, Id.key, Id.table, Datetime.is_lt, Datetime.is_lte, Text.is_email, Text.is_url, Text.is_domain, Text.is_ip, Text.is_ipv4, Text.is_ipv6, Text.is_uuid, Text.is_ulid, Text.is_semver, Text.is_alpha, Text.is_alphanum, Text.is_numeric, Text.is_latitude, Text.is_longitude, Text.is_datetime, Text.matches, Text.similarity_jaro, Text.similarity_jaro_winkler, Text.distance_levenshtein, Text.distance_damerau_levenshtein, Text.distance_normalized_levenshtein, Text.is_ascii, Text.is_hexadecimal, Hash.sha256, Hash.blake3, Hash.md5, Hash.sha1, Hash.sha512, Array.distinct, Array.union, Array.intersect, Array.complement, Time.now, Time.floor, Time.ceil, Time.round, Time.group, Time.plus, Time.minus, Time.wday, Time.yday, Time.week, Time.unix, Time.unix_millis, Time.unix_micros, Time.nano, Time.format, Time.from_unix, Time.year, Time.month, Time.day, Time.hour, Time.minute, Time.second, Math.mean, Math.median, Math.stddev, Math.variance, Math.percentile, Rand.uuid, Rand.ulid, Rand.int)

	# ======================================================== foundations

	## Why a reified function is not SurrealQL, or a schema is not one
	## SurrealDB can create. Every rejection names the construct.
	Error : Ql.Error

	## A typed record id: `customer:⟨ada⟩`. `phantom` is always empty. It ties
	## the id to its row type, which the reifier sees.
	Id(row) := { table : Str, key : Str, phantom : List(row) }.{

		## Equal when the table and the key are equal.
		is_eq : Id(row), Id(row) -> Bool
		is_eq = |Id.(a), Id.(b)| a.table == b.table and a.key == b.key

		## The key, without the table: `record::id(id)` in a clause.
		key : Id(row) -> Str
		key = |Id.(i)| i.key

		## The name of the table: `record::tb(id)` in a clause.
		table : Id(row) -> Str
		table = |Id.(i)| i.table

		encoder_for : Encode.Format -> (Id(row), Encode.State -> Try(Encode.State, []))
		encoder_for = |_format| |Id.(i), state| Encode.Format.encode_id(i.table, i.key, state)
	}

	## A stored link. `fetched` holds the row when the application has it (seed
	## data, a FETCH result). In a clause, `get` is a traversal: `customer.name`.
	Link(row) := { id : Id(row), fetched : [Fetched(row), NotFetched] }.{

		## The row. A link that was not fetched has none, and this crashes: the
		## row lives in the database, so only a clause can read through it.
		get : Link(row) -> row
		get = |Link.(l)| match l.fetched {
			Fetched(r) => r
			NotFetched => crash "this link was not fetched"
		}

		## The record id the link holds: the id itself in a clause.
		id : Link(row) -> Id(row)
		id = |Link.(l)| l.id

		## Equal when the ids are equal.
		is_eq : Link(row), Link(row) -> Bool
		is_eq = |a, b| a.id() == b.id()

		encoder_for : Encode.Format -> (Link(row), Encode.State -> Try(Encode.State, []))
		encoder_for = |_format| |Link.(l), state| {
			Id.(i) = l.id
			Encode.Format.encode_id(i.table, i.key, state)
		}
	}

	## A SurrealDB `datetime`, held as UTC ISO 8601 with a `Z`
	## (`2026-10-28T04:53:59Z`). A fraction has no trailing zeros, so equal
	## times are equal strings. Make one with `datetime`.
	Datetime := { iso : Str }.{
		is_eq : _

		## Earlier. The order is the order of the text without its `Z`: with
		## the `Z` kept, `...59Z` would sort after `...59.5Z`.
		is_lt : Datetime, Datetime -> Bool
		is_lt = |Datetime.(a), Datetime.(b)| Surreal.bytes_lt(a.iso.drop_suffix("Z").to_utf8(), b.iso.drop_suffix("Z").to_utf8())

		is_lte : Datetime, Datetime -> Bool
		is_lte = |a, b| a == b or Datetime.is_lt(a, b)

		is_gt : Datetime, Datetime -> Bool
		is_gt = |a, b| Datetime.is_lt(b, a)

		is_gte : Datetime, Datetime -> Bool
		is_gte = |a, b| Datetime.is_lte(b, a)

		## Nanoseconds since 1970-01-01T00:00:00Z, as `time::nano` counts them. `I128` holds all years.
		to_unix_nanos : Datetime -> I128
		to_unix_nanos = |at| {
			part = |value| value.to_i128()
			days = Surreal.days_from_civil(part(Surreal.Time.year(at)), part(Surreal.Time.month(at)), part(Surreal.Time.day(at)))
			seconds = ((days * 24 + part(Surreal.Time.hour(at))) * 60 + part(Surreal.Time.minute(at))) * 60 + part(Surreal.Time.second(at))
			seconds * 1000000000 + Surreal.fraction_nanos(at)
		}

		## The datetime at this many nanoseconds since 1970. A year outside 0 to 9999 is refused.
		from_unix_nanos : I128 -> Try(Datetime, [BadDatetime])
		from_unix_nanos = |nanos| {
			seconds = nanos.div_floor_by(1000000000)
			rest = nanos.mod_by(1000000000)
			day_seconds = seconds.mod_by(86400)
			(year, month, day) = Surreal.civil_from_days(seconds.div_floor_by(86400))
			if year < 0 or year > 9999 {
				Err(BadDatetime)
			} else {
				fraction = if (rest == 0) "" else ".${Surreal.pad(rest, 9)}"
				clock = "${Surreal.pad(day_seconds // 3600, 2)}:${Surreal.pad(day_seconds % 3600 // 60, 2)}:${Surreal.pad(day_seconds % 60, 2)}"
				Surreal.datetime("${Surreal.pad(year, 4)}-${Surreal.pad(month, 2)}-${Surreal.pad(day, 2)}T${clock}${fraction}Z")
			}
		}

		encoder_for : Encode.Format -> (Datetime, Encode.State -> Try(Encode.State, []))
		encoder_for = |_format| |Datetime.(d), state| Encode.Format.encode_datetime(d.iso, state)
	}

	## A datetime from `YYYY-MM-DDTHH:MM:SS`, an optional fraction of up to
	## nine digits, and `Z`. Other offsets are refused: the order of the text
	## is the order of the time only in UTC.
	datetime : Str -> Try(Datetime, [BadDatetime])
	datetime = |text| {
		bytes = text.to_utf8()
		match bytes {
			[y1, y2, y3, y4, 45, m1, m2, 45, d1, d2, 84, h1, h2, 58, n1, n2, 58, s1, s2, .. as rest] => {
				number = |digits| digits.fold(0.U64, |acc, b| acc * 10 + (b - 48).to_u64())
				is_digits = |digits| digits.all(|b| b >= 48 and b <= 57)
				year = number([y1, y2, y3, y4])
				month = number([m1, m2])
				day = number([d1, d2])
				fraction = match rest {
					[90] => Ok([])
					[46, .. as more] => match more.last() {
						Ok(90) => if (more.len() > 1) Ok(more.drop_last(1)) else Err(BadDatetime)
						_ => Err(BadDatetime)
					}
					_ => Err(BadDatetime)
				}
				digits_ok = is_digits([y1, y2, y3, y4, m1, m2, d1, d2, h1, h2, n1, n2, s1, s2])
				in_range = month >= 1 and month <= 12 and day >= 1 and day <= Surreal.days_in_month(year, month) and number([h1, h2]) < 24 and number([n1, n2]) < 60 and number([s1, s2]) < 60
				match fraction {
					Ok(frac) =>
						if digits_ok and is_digits(frac) and frac.len() <= 9 and in_range {
							kept = Surreal.drop_zeros(frac)
							whole = bytes.take_first(19)
							iso = if (kept.is_empty()) whole.append(90) else whole.append(46).concat(kept).append(90)
							match Str.from_utf8(iso) {
								Ok(s) => Ok(Datetime.({ iso: s }))
								Err(_) => crash "ASCII digits and punctuation are valid UTF-8"
							}
						} else {
							Err(BadDatetime)
						}
					Err(_) => Err(BadDatetime)
				}
			}
			_ => Err(BadDatetime)
		}
	}

	## Byte order, as the text of a datetime sorts.
	bytes_lt : List(U8), List(U8) -> Bool
	bytes_lt = |a, b| match (a, b) {
		([x, .. as xs], [y, .. as ys]) => x < y or (x == y and Surreal.bytes_lt(xs, ys))
		([], [_, ..]) => Bool.True
		_ => Bool.False
	}

	days_in_month : U64, U64 -> U64
	days_in_month = |year, month|
		if month == 2 {
			if (year % 4 == 0 and (year % 100 != 0 or year % 400 == 0)) 29 else 28
		} else if month == 4 or month == 6 or month == 9 or month == 11 {
			30
		} else {
			31
		}

	## The day number of a date, counting from 1970-01-01.
	days_from_civil : I128, I128, I128 -> I128
	days_from_civil = |year, month, day| {
		shifted = if (month <= 2) year - 1 else year
		era = shifted.div_floor_by(400)
		year_of_era = shifted - era * 400
		day_of_year = (153 * (if (month > 2) month - 3 else month + 9) + 2) // 5 + day - 1
		era * 146097 + year_of_era * 365 + year_of_era // 4 - year_of_era // 100 + day_of_year - 719468
	}

	## The year, month and day of a day number counted from 1970-01-01.
	civil_from_days : I128 -> (I128, I128, I128)
	civil_from_days = |days| {
		shifted = days + 719468
		era = shifted.div_floor_by(146097)
		day_of_era = shifted - era * 146097
		year_of_era = (day_of_era - day_of_era // 1460 + day_of_era // 36524 - day_of_era // 146096) // 365
		day_of_year = day_of_era - (365 * year_of_era + year_of_era // 4 - year_of_era // 100)
		march_month = (5 * day_of_year + 2) // 153
		month = if (march_month < 10) march_month + 3 else march_month - 9
		(year_of_era + era * 400 + (if (month <= 2) 1 else 0), month, day_of_year - (153 * march_month + 2) // 5 + 1)
	}

	## The nanoseconds of the fraction of a datetime.
	fraction_nanos : Datetime -> I128
	fraction_nanos = |Datetime.(d)| {
		digits = d.iso.to_utf8().drop_first(20).drop_last(1)
		digits.concat(List.repeat(48, 9 - digits.len())).fold(0.I128, |acc, b| acc * 10 + (b - 48).to_i128())
	}

	## A number in at least `width` digits, with leading zeros.
	pad : I128, U64 -> Str
	pad = |n, width| {
		text = n.to_str()
		Str.repeat("0", width - text.count_utf8_bytes()).concat(text)
	}

	## A fraction without its trailing zeros.
	drop_zeros : List(U8) -> List(U8)
	drop_zeros = |digits| match digits.last() {
		Ok(48) => Surreal.drop_zeros(digits.drop_last(1))
		_ => digits
	}

	# ============================================== functions of the database

	## A length of time, as SurrealDB's `duration`. Make one with the functions
	## of `Time`, such as `Time.hours`. It cannot be a column or a captured value.
	Duration := { nanos : U64 }.{
		is_eq : _
	}

	## The `string::` functions that Roc has no builtin for. A function that says
	## "database only" has no Roc body: calling it outside a clause stops the program.
	Text :: {}.{

		## `string::is_email`. Database only.
		is_email : Str -> Bool
		is_email = |_| crash "Surreal.Text.is_email runs in the database only"

		## `string::is_url`. Database only.
		is_url : Str -> Bool
		is_url = |_| crash "Surreal.Text.is_url runs in the database only"

		## `string::is_domain`. Database only.
		is_domain : Str -> Bool
		is_domain = |_| crash "Surreal.Text.is_domain runs in the database only"

		## `string::is_ip`. Database only.
		is_ip : Str -> Bool
		is_ip = |_| crash "Surreal.Text.is_ip runs in the database only"

		## `string::is_ipv4`. Database only.
		is_ipv4 : Str -> Bool
		is_ipv4 = |_| crash "Surreal.Text.is_ipv4 runs in the database only"

		## `string::is_ipv6`. Database only.
		is_ipv6 : Str -> Bool
		is_ipv6 = |_| crash "Surreal.Text.is_ipv6 runs in the database only"

		## `string::is_uuid`. Database only.
		is_uuid : Str -> Bool
		is_uuid = |_| crash "Surreal.Text.is_uuid runs in the database only"

		## `string::is_ulid`. Database only.
		is_ulid : Str -> Bool
		is_ulid = |_| crash "Surreal.Text.is_ulid runs in the database only"

		## `string::is_semver`. Database only.
		is_semver : Str -> Bool
		is_semver = |_| crash "Surreal.Text.is_semver runs in the database only"

		## `string::is_alpha`. It is Unicode: `abé` is true. Database only.
		is_alpha : Str -> Bool
		is_alpha = |_| crash "Surreal.Text.is_alpha runs in the database only"

		## `string::is_alphanum`. It is Unicode. Database only.
		is_alphanum : Str -> Bool
		is_alphanum = |_| crash "Surreal.Text.is_alphanum runs in the database only"

		## `string::is_numeric`. It is Unicode: Arabic digits are true. Database only.
		is_numeric : Str -> Bool
		is_numeric = |_| crash "Surreal.Text.is_numeric runs in the database only"

		## `string::is_latitude`, for a text such as `45.5`. Database only.
		is_latitude : Str -> Bool
		is_latitude = |_| crash "Surreal.Text.is_latitude runs in the database only"

		## `string::is_longitude`, for a text such as `45.5`. Database only.
		is_longitude : Str -> Bool
		is_longitude = |_| crash "Surreal.Text.is_longitude runs in the database only"

		## `string::is_datetime`: the text read with a `strftime` pattern. Database only.
		is_datetime : Str, Str -> Bool
		is_datetime = |_, _| crash "Surreal.Text.is_datetime runs in the database only"

		## `string::matches`: the pattern is Rust regex syntax. Database only.
		matches : Str, Str -> Bool
		matches = |_, _| crash "Surreal.Text.matches runs in the database only"

		## `string::similarity::jaro`. Database only.
		similarity_jaro : Str, Str -> F64
		similarity_jaro = |_, _| crash "Surreal.Text.similarity_jaro runs in the database only"

		## `string::similarity::jaro_winkler`. Database only.
		similarity_jaro_winkler : Str, Str -> F64
		similarity_jaro_winkler = |_, _| crash "Surreal.Text.similarity_jaro_winkler runs in the database only"

		## `string::distance::levenshtein`: edits counted in characters. Database only.
		distance_levenshtein : Str, Str -> I64
		distance_levenshtein = |_, _| crash "Surreal.Text.distance_levenshtein runs in the database only"

		## `string::distance::damerau_levenshtein`. Database only.
		distance_damerau_levenshtein : Str, Str -> I64
		distance_damerau_levenshtein = |_, _| crash "Surreal.Text.distance_damerau_levenshtein runs in the database only"

		## `string::distance::normalized_levenshtein`: a similarity, 1 for equal texts. Database only.
		distance_normalized_levenshtein : Str, Str -> F64
		distance_normalized_levenshtein = |_, _| crash "Surreal.Text.distance_normalized_levenshtein runs in the database only"

		## `string::is_ascii`: not empty, and every byte is below 128.
		is_ascii : Str -> Bool
		is_ascii = |text| {
			bytes = text.to_utf8()
			!bytes.is_empty() and bytes.all(|b| b < 128)
		}

		## `string::is_hexadecimal`: not empty, and every byte is `0-9`, `a-f` or `A-F`.
		is_hexadecimal : Str -> Bool
		is_hexadecimal = |text| {
			bytes = text.to_utf8()
			!bytes.is_empty() and bytes.all(|b| (b >= 48 and b <= 57) or (b >= 97 and b <= 102) or (b >= 65 and b <= 70))
		}
	}

	## The `crypto::` hashes, as lower-case hex text.
	Hash :: {}.{

		## `crypto::sha256`.
		sha256 : Str -> Str
		sha256 = |text| Crypto.SHA256.hash(text.to_utf8()).to_hex()

		## `crypto::blake3`.
		blake3 : Str -> Str
		blake3 = |text| Crypto.BLAKE3.hash(text.to_utf8()).to_hex()

		## `crypto::md5`. Database only.
		md5 : Str -> Str
		md5 = |_| crash "Surreal.Hash.md5 runs in the database only"

		## `crypto::sha1`. Database only.
		sha1 : Str -> Str
		sha1 = |_| crash "Surreal.Hash.sha1 runs in the database only"

		## `crypto::sha512`. Database only.
		sha512 : Str -> Str
		sha512 = |_| crash "Surreal.Hash.sha512 runs in the database only"
	}

	## The `array::` functions on a list of values.
	Array :: {}.{

		## `array::distinct`: each value once, in the order of its first place.
		distinct : List(a) -> List(a) where [a.is_eq : a, a -> Bool]
		distinct = |items| items.fold([], |seen, item| if (seen.contains(item)) seen else seen.append(item))

		## `array::union`: the distinct values of both lists.
		union : List(a), List(a) -> List(a) where [a.is_eq : a, a -> Bool]
		union = |a, b| Array.distinct(a.concat(b))

		## `array::intersect`: the distinct values of the first list that the second has.
		intersect : List(a), List(a) -> List(a) where [a.is_eq : a, a -> Bool]
		intersect = |a, b| Array.distinct(a).keep_if(|item| b.contains(item))

		## `array::complement`: the values of the first list that the second has not. It is not `array::difference`.
		complement : List(a), List(a) -> List(a) where [a.is_eq : a, a -> Bool]
		complement = |a, b| a.keep_if(|item| !b.contains(item))
	}

	## The `time::` functions, and the constructors of `Duration`. Every part of a
	## time is read in UTC, as the library keeps every `Datetime`.
	Time :: {}.{

		## A `Duration` of this many nanoseconds.
		nanos : U64 -> Duration
		nanos = |n| Duration.({ nanos: n })

		micros : U64 -> Duration
		micros = |n| Duration.({ nanos: n * 1000 })

		millis : U64 -> Duration
		millis = |n| Duration.({ nanos: n * 1000000 })

		secs : U64 -> Duration
		secs = |n| Duration.({ nanos: n * 1000000000 })

		mins : U64 -> Duration
		mins = |n| Duration.({ nanos: n * 60000000000 })

		hours : U64 -> Duration
		hours = |n| Duration.({ nanos: n * 3600000000000 })

		days : U64 -> Duration
		days = |n| Duration.({ nanos: n * 86400000000000 })

		weeks : U64 -> Duration
		weeks = |n| Duration.({ nanos: n * 604800000000000 })

		## `time::now`. It differs on each call, so a clause must not compare it to itself. Database only.
		now : () -> Datetime
		now = || crash "Surreal.Time.now runs in the database only"

		## `time::floor`: the start of the span that holds the time. Database only.
		floor : Datetime, Duration -> Datetime
		floor = |_, _| crash "Surreal.Time.floor runs in the database only"

		## `time::ceil`: the end of the span that holds the time. Database only.
		ceil : Datetime, Duration -> Datetime
		ceil = |_, _| crash "Surreal.Time.ceil runs in the database only"

		## `time::round`: the nearest span boundary, a half going up. Database only.
		round : Datetime, Duration -> Datetime
		round = |_, _| crash "Surreal.Time.round runs in the database only"

		## `time::group`: the start of the unit that holds the time. Database only.
		group : Datetime, [Year, Month, Day, Hour, Minute, Second] -> Datetime
		group = |_, _| crash "Surreal.Time.group runs in the database only"

		## The time `duration` later: `datetime + duration`. Database only.
		plus : Datetime, Duration -> Datetime
		plus = |_, _| crash "Surreal.Time.plus runs in the database only"

		## The time `duration` earlier: `datetime - duration`. Database only.
		minus : Datetime, Duration -> Datetime
		minus = |_, _| crash "Surreal.Time.minus runs in the database only"

		## `time::wday`: Monday is 1 and Sunday is 7. Database only.
		wday : Datetime -> I64
		wday = |_| crash "Surreal.Time.wday runs in the database only"

		## `time::yday`: 1 for the first of January. Database only.
		yday : Datetime -> I64
		yday = |_| crash "Surreal.Time.yday runs in the database only"

		## `time::week`: the week of the year. Database only.
		week : Datetime -> I64
		week = |_| crash "Surreal.Time.week runs in the database only"

		## `time::unix`: whole seconds since 1970. Database only.
		unix : Datetime -> I64
		unix = |_| crash "Surreal.Time.unix runs in the database only"

		## `time::millis`: whole milliseconds since 1970. It is not `millis`, which makes a `Duration`. Database only.
		unix_millis : Datetime -> I64
		unix_millis = |_| crash "Surreal.Time.unix_millis runs in the database only"

		## `time::micros`: whole microseconds since 1970. It is not `micros`, which makes a `Duration`. Database only.
		unix_micros : Datetime -> I64
		unix_micros = |_| crash "Surreal.Time.unix_micros runs in the database only"

		## `time::nano`: whole nanoseconds since 1970. Database only.
		nano : Datetime -> I64
		nano = |_| crash "Surreal.Time.nano runs in the database only"

		## `time::format`: the time written with a `strftime` pattern. Database only.
		format : Datetime, Str -> Str
		format = |_, _| crash "Surreal.Time.format runs in the database only"

		## `time::from_unix`: the time at this many seconds since 1970. Database only.
		from_unix : I64 -> Datetime
		from_unix = |_| crash "Surreal.Time.from_unix runs in the database only"

		## `time::year`.
		year : Datetime -> I64
		year = |at| Time.digits(at, 0, 4)

		## `time::month`: 1 to 12.
		month : Datetime -> I64
		month = |at| Time.digits(at, 5, 2)

		## `time::day`: 1 to 31.
		day : Datetime -> I64
		day = |at| Time.digits(at, 8, 2)

		## `time::hour`: 0 to 23.
		hour : Datetime -> I64
		hour = |at| Time.digits(at, 11, 2)

		## `time::minute`: 0 to 59.
		minute : Datetime -> I64
		minute = |at| Time.digits(at, 14, 2)

		## `time::second`: 0 to 59, without the fraction.
		second : Datetime -> I64
		second = |at| Time.digits(at, 17, 2)

		## The number in `count` digits of the text of a datetime, from byte `start`.
		digits : Datetime, U64, U64 -> I64
		digits = |Datetime.(d), start, count| d.iso.to_utf8().drop_first(start).take_first(count).fold(0, |acc, b| acc * 10 + (b - 48).to_i64())
	}

	## The `math::` statistics on a list of floats. Convert an `I64` or `Dec` field with `to_f64()`.
	Math :: {}.{

		## `math::mean`. A list with no value has no mean: the result is not a number.
		mean : List(F64) -> F64
		mean = |values| values.sum() / values.len().to_f64()

		## `math::median`. Database only.
		median : List(F64) -> F64
		median = |_| crash "Surreal.Math.median runs in the database only"

		## `math::stddev`: the sample deviation. Database only.
		stddev : List(F64) -> F64
		stddev = |_| crash "Surreal.Math.stddev runs in the database only"

		## `math::variance`: the sample variance. Database only.
		variance : List(F64) -> F64
		variance = |_| crash "Surreal.Math.variance runs in the database only"

		## `math::percentile`: a value of the list, with the percentage 0 to 100, interpolated. Database only.
		percentile : List(F64), F64 -> F64
		percentile = |_, _| crash "Surreal.Math.percentile runs in the database only"
	}

	## The `rand::` functions. Each gives a new value on every call, so a clause
	## may use them only in a default, a computed field or an update. Database only.
	Rand :: {}.{

		## `rand::uuid`, as text.
		uuid : () -> Str
		uuid = || crash "Surreal.Rand.uuid runs in the database only"

		## `rand::ulid`: 26 characters that sort by time.
		ulid : () -> Str
		ulid = || crash "Surreal.Rand.ulid runs in the database only"

		## `rand::int`: a whole number from the first to the second, both included.
		int : I64, I64 -> I64
		int = |_, _| crash "Surreal.Rand.int runs in the database only"
	}

	## A table whose rows are `row`. It holds the name, the row type that the
	## identity lambda reified, and whether it is an edge table. `Types` reads
	## the schema off the row type.
	Table(row) :: { name : Str, row_ty : Code.Ty, kind : Types.Kind }.{

		## The id of a row of this table.
		id : Table(row), Str -> Id(row)
		id = |Table.(t), key| Id.({ table: t.name, key: key, phantom: [] })

		## A link to a row of this table. It is not fetched.
		link : Table(row), Str -> Link(row)
		link = |this, key| Link.({ id: Table.id(this, key), fetched: NotFetched })

		## The schema builder of this table.
		define : Table(row) -> Def(row)
		define = |this| Def.({ source: Surreal.source(this), rules: [], problems: [] })

		# ---------------------------------------------------- writes

		## The cut of `update` and `delete` clauses (see `Surreal.code_primitives`).
		code_primitives = (Surreal.Link.get, Surreal.Link.id, Surreal.Id.is_eq, Surreal.Id.key, Surreal.Id.table, Surreal.Datetime.is_lt, Surreal.Datetime.is_lte, Surreal.Text.is_email, Surreal.Text.is_url, Surreal.Text.is_domain, Surreal.Text.is_ip, Surreal.Text.is_ipv4, Surreal.Text.is_ipv6, Surreal.Text.is_uuid, Surreal.Text.is_ulid, Surreal.Text.is_semver, Surreal.Text.is_alpha, Surreal.Text.is_alphanum, Surreal.Text.is_numeric, Surreal.Text.is_latitude, Surreal.Text.is_longitude, Surreal.Text.is_datetime, Surreal.Text.matches, Surreal.Text.similarity_jaro, Surreal.Text.similarity_jaro_winkler, Surreal.Text.distance_levenshtein, Surreal.Text.distance_damerau_levenshtein, Surreal.Text.distance_normalized_levenshtein, Surreal.Text.is_ascii, Surreal.Text.is_hexadecimal, Surreal.Hash.sha256, Surreal.Hash.blake3, Surreal.Hash.md5, Surreal.Hash.sha1, Surreal.Hash.sha512, Surreal.Array.distinct, Surreal.Array.union, Surreal.Array.intersect, Surreal.Array.complement, Surreal.Time.now, Surreal.Time.floor, Surreal.Time.ceil, Surreal.Time.round, Surreal.Time.group, Surreal.Time.plus, Surreal.Time.minus, Surreal.Time.wday, Surreal.Time.yday, Surreal.Time.week, Surreal.Time.unix, Surreal.Time.unix_millis, Surreal.Time.unix_micros, Surreal.Time.nano, Surreal.Time.format, Surreal.Time.from_unix, Surreal.Time.year, Surreal.Time.month, Surreal.Time.day, Surreal.Time.hour, Surreal.Time.minute, Surreal.Time.second, Surreal.Math.mean, Surreal.Math.median, Surreal.Math.stddev, Surreal.Math.variance, Surreal.Math.percentile, Surreal.Rand.uuid, Surreal.Rand.ulid, Surreal.Rand.int)

		## One transaction that inserts every row, with the values the
		## compiler's derived encoder writes. An absent optional field is a key
		## left out. The `id` field stays in the row: it is the record key.
		insert : Table(row), List(row) -> Try(Statement, Error) where [row.encoder_for : Encode.Format -> (row, Encode.State -> Try(Encode.State, []))]
		insert = |Table.(t), rows| {
			objects = rows.map_try(|row| Surreal.object_of(row).map_ok(|fields| Surreal.ends_named(fields, t.kind)))?
			head = match t.kind {
				Relation(_) => "INSERT RELATION INTO"
				Normal => "INSERT INTO"
			}
			literals = Str.join_with(objects.map(|fields| Ql.literal(Ql.Value.Object(fields))), ", ")
			Ok(Surreal.statement("BEGIN;\n${head} ${Ql.ident(t.name)} [${literals}];\nCOMMIT"))
		}

		## A new row at `table:⟨id⟩`. It fails when the row exists.
		create : Table(row), row -> Try(Statement, Error) where [row.encoder_for : Encode.Format -> (row, Encode.State -> Try(Encode.State, []))]
		create = |Table.(t), row| Surreal.content_write("CREATE", t, row)

		## The row at `table:⟨id⟩`, replaced when it exists and made when not.
		upsert : Table(row), row -> Try(Statement, Error) where [row.encoder_for : Encode.Format -> (row, Encode.State -> Try(Encode.State, []))]
		upsert = |Table.(t), row| Surreal.content_write("UPSERT", t, row)

		## An edge between the rows of `from` and `to`. Only a relation table has
		## edges.
		relate : Table(row), row -> Try(Statement, Error) where [row.encoder_for : Encode.Format -> (row, Encode.State -> Try(Encode.State, []))]
		relate = |Table.(t), row| {
			match t.kind {
				Normal => return Err(Unsupported("`${t.name}` is not a relation table, so it has no edges to relate"))
				Relation(_) => {}
			}
			split = Surreal.split_id(t, row)?
			from = Surreal.field_of(split.fields, "in")?
			to = Surreal.field_of(split.fields, "out")?
			rest = split.fields.keep_if(|f| f.name != "in" and f.name != "out")
			Ok(Surreal.statement("RELATE ${Ql.literal(from)}->${Ql.record_id(t.name, split.key)}->${Ql.literal(to)} CONTENT ${Ql.literal(Ql.Value.Object(rest))}"))
		}

		## Set the fields the patch changes in every row the condition keeps.
		## The patch is the row with some fields replaced, `|o| { ..o, f: .. }`,
		## and each changed field is a `SET` item. `SET`, never `MERGE`, because
		## `MERGE` breaks a union field.
		update : Table(row), Code(row -> Bool), Code(row -> row) -> Write(p, row)
		update = |Table.(t), condition, patch| {
			row = Translate.document("", Surreal.is_edge(t.kind))
			build = |param| {
				keep = Translate.render(condition.graph(), [row], param)?
				sets = Translate.assignments(patch.graph(), [row], param)?
				Ok("UPDATE ${Ql.ident(t.name)} SET ${Surreal.set_list(sets)} WHERE ${keep}")
			}
			Write.({ build: build })
		}

		## [Table.update] where the condition and the patch read the parameter
		## record, `|p, o| ..`.
		update_by : Table(row), Code((p, row -> Bool)), Code((p, row -> row)) -> Write(p, row)
		update_by = |Table.(t), condition, patch| {
			row = Translate.document("", Surreal.is_edge(t.kind))
			build = |param| {
				keep = Translate.render(condition.graph(), [Translate.Binding.Params, row], param)?
				sets = Translate.assignments(patch.graph(), [Translate.Binding.Params, row], param)?
				Ok("UPDATE ${Ql.ident(t.name)} SET ${Surreal.set_list(sets)} WHERE ${keep}")
			}
			Write.({ build: build })
		}

		## Delete every row the condition keeps.
		delete : Table(row), Code(row -> Bool) -> Write(p, row)
		delete = |Table.(t), condition| {
			row = Translate.document("", Surreal.is_edge(t.kind))
			build = |param| Ok("DELETE ${Ql.ident(t.name)} WHERE ${Translate.render(condition.graph(), [row], param)?}")
			Write.({ build: build })
		}

		## [Table.delete] where the condition reads the parameter record.
		delete_by : Table(row), Code((p, row -> Bool)) -> Write(p, row)
		delete_by = |Table.(t), condition| {
			row = Translate.document("", Surreal.is_edge(t.kind))
			build = |param| Ok("DELETE ${Ql.ident(t.name)} WHERE ${Translate.render(condition.graph(), [Translate.Binding.Params, row], param)?}")
			Write.({ build: build })
		}
	}

	## The schema entry of a table: what `Types` reads.
	source : Table(row) -> Types.Source
	source = |Table.(t)| t

	## A table. The identity lambda is only there to be reified, so that the
	## table holds the type of its row. The annotation on the binding fixes `row`:
	##
	## customers : Surreal.Table(Customer)
	## customers = Surreal.table("customer", |c| c)
	table : Str, Code(row -> row) -> Table(row)
	table = |name, code| Table.({ name: name, row_ty: code.graph().root_row().result, kind: Types.Kind.Normal })

	## An edge table from one table to another. The row has `from : Link(a)`
	## and `to : Link(b)`: SurrealDB's `in` and `out`, which a row cannot name
	## because `in` is a keyword.
	relation : Str, Table(a), Table(b), Code(row -> row) -> Table(row)
	relation = |name, Table.(from), Table.(to), code| {
		ends = { from: { name: from.name, row_ty: from.row_ty }, to: { name: to.name, row_ty: to.row_ty } }
		Table.({ name: name, row_ty: code.graph().root_row().result, kind: Types.Kind.Relation(ends) })
	}

	## A link that holds its row, for seed data and for a row read back.
	fetched : Table({ id : Str, ..others }), { id : Str, ..others } -> Link({ id : Str, ..others })
	fetched = |tbl, row| Link.({ id: Table.id(tbl, row.id), fetched: Fetched(row) })

	# ============================================================= schema

	## A table's schema being built. Each clause is a Roc function that is
	## reified and translated where it is given; a clause SurrealQL cannot
	## hold is kept as a problem, and `schema` reports the first one.
	Def(row) :: { source : Types.Source, rules : List(Schema.Rule), problems : List(Error) }.{

		## The cut of schema clauses (see `Surreal.code_primitives`).
		code_primitives = (Surreal.Link.get, Surreal.Link.id, Surreal.Id.is_eq, Surreal.Id.key, Surreal.Id.table, Surreal.Datetime.is_lt, Surreal.Datetime.is_lte, Surreal.Text.is_email, Surreal.Text.is_url, Surreal.Text.is_domain, Surreal.Text.is_ip, Surreal.Text.is_ipv4, Surreal.Text.is_ipv6, Surreal.Text.is_uuid, Surreal.Text.is_ulid, Surreal.Text.is_semver, Surreal.Text.is_alpha, Surreal.Text.is_alphanum, Surreal.Text.is_numeric, Surreal.Text.is_latitude, Surreal.Text.is_longitude, Surreal.Text.is_datetime, Surreal.Text.matches, Surreal.Text.similarity_jaro, Surreal.Text.similarity_jaro_winkler, Surreal.Text.distance_levenshtein, Surreal.Text.distance_damerau_levenshtein, Surreal.Text.distance_normalized_levenshtein, Surreal.Text.is_ascii, Surreal.Text.is_hexadecimal, Surreal.Hash.sha256, Surreal.Hash.blake3, Surreal.Hash.md5, Surreal.Hash.sha1, Surreal.Hash.sha512, Surreal.Array.distinct, Surreal.Array.union, Surreal.Array.intersect, Surreal.Array.complement, Surreal.Time.now, Surreal.Time.floor, Surreal.Time.ceil, Surreal.Time.round, Surreal.Time.group, Surreal.Time.plus, Surreal.Time.minus, Surreal.Time.wday, Surreal.Time.yday, Surreal.Time.week, Surreal.Time.unix, Surreal.Time.unix_millis, Surreal.Time.unix_micros, Surreal.Time.nano, Surreal.Time.format, Surreal.Time.from_unix, Surreal.Time.year, Surreal.Time.month, Surreal.Time.day, Surreal.Time.hour, Surreal.Time.minute, Surreal.Time.second, Surreal.Math.mean, Surreal.Math.median, Surreal.Math.stddev, Surreal.Math.variance, Surreal.Math.percentile, Surreal.Rand.uuid, Surreal.Rand.ulid, Surreal.Rand.int)

		## A row predicate, named for its error message. It is the `ASSERT`
		## of the one field it reads, or an event when it reads several.
		check : Def(row), Str, Code(row -> Bool) -> Def(row)
		check = |this, name, predicate| Def.add(this, |src| Schema.check(src, name, predicate.graph()))

		## A predicate on one field. Through `.?` it sees a `Try`.
		assert : Def(row), Code(row -> v), Code(v -> Bool) -> Def(row)
		assert = |this, path, predicate| Def.add(this, |_| Schema.assert(path.graph(), predicate.graph()))

		## A predicate on each element of a list field.
		assert_each : Def(row), Code(row -> List(v)), Code(v -> Bool) -> Def(row)
		assert_each = |this, path, predicate| Def.add(this, |_| Schema.assert_each(path.graph(), predicate.graph()))

		## A unique index on a path, or on a record of paths.
		unique : Def(row), Code(row -> k) -> Def(row)
		unique = |this, key| Def.add(this, |src| Schema.index(src, key.graph(), Bool.True))

		index : Def(row), Code(row -> k) -> Def(row)
		index = |this, key| Def.add(this, |src| Schema.index(src, key.graph(), Bool.False))

		## The value a field takes when a write leaves it out: `.default(|c| c.tags, [])`.
		default : Def(row), Code(row -> v), v -> Def(row) where [v.encoder_for : Encode.Format -> (v, Encode.State -> Try(Encode.State, []))]
		default = |this, path, value| Def.add(this, |_| Schema.default(path.graph(), Encode.value_of(value)?))

		## As `default`, with the value an expression of the row, which may call
		## `Rand`: `.default_by(|o| o.key, |_| Surreal.Rand.ulid())`.
		default_by : Def(row), Code(row -> v), Code(row -> v) -> Def(row)
		default_by = |this, path, value| Def.add(this, |src| Schema.default_by(src, path.graph(), value.graph()))

		## A field SurrealDB computes on every write from the row.
		computed : Def(row), Code(row -> v), Code(row -> v) -> Def(row)
		computed = |this, path, value| Def.add(this, |src| Schema.computed(src, path.graph(), value.graph()))

		readonly : Def(row), Code(row -> v) -> Def(row)
		readonly = |this, path| Def.add(this, |_| Schema.readonly(path.graph()))

		## The time of the row's first write, which later writes keep.
		created_now : Def(row), Code(row -> Datetime) -> Def(row)
		created_now = |this, path| Def.add(this, |_| Schema.created_now(path.graph()))

		## What deleting a row of `target` does to every link from this table
		## to it, at any depth. Without one, the delete is rejected.
		on_delete : Def(row), Table(t), [Reject, Unset, Cascade, Ignore] -> Def(row)
		on_delete = |this, target, policy| Def.add(this, |_| Schema.on_delete(Surreal.source(target).name, policy))

		## The same for the one link at a path; it wins over `on_delete`.
		on_delete_at : Def(row), Code(row -> l), [Reject, Unset, Cascade, Ignore] -> Def(row)
		on_delete_at = |this, path, policy| Def.add(this, |_| Schema.on_delete_at(path.graph(), policy))

		comment : Def(row), Code(row -> v), Str -> Def(row)
		comment = |this, path, text| Def.add(this, |_| Schema.comment(path.graph(), text))

		## The definition, ready for `schema`.
		done : Def(row) -> Defined
		done = |Def.(d)| Schema.defined(d.source, d.rules, d.problems)

		add : Def(row), (Types.Source -> Try(List(Schema.Rule), Error)) -> Def(row)
		add = |Def.(d), clause| match clause(d.source) {
			Ok(rules) => Def.({ ..d, rules: d.rules.concat(rules) })
			Err(problem) => Def.({ ..d, problems: d.problems.append(problem) })
		}
	}

	## A finished table definition.
	Defined : Schema.Defined

	## The schema script of every table: tables, fields, indexes, events, in
	## that order. The list is also where a link finds its target table.
	schema : List(Defined) -> Try(Str, Error)
	schema = |defined| Schema.script(defined)

	# ======================================================== queries

	## A clause is written when its statement is, because the spelling of a
	## parameter is chosen then: `$name` for a driver, the literal for a script.
	Clause : (Str -> Str) -> Try(Str, Error)

	## A query over the rows of a table, taking parameters of type `p`.
	## `source` says what a clause reads its row as: the table row, or the
	## pair of a row and its edges once `outgoing` or `incoming` ran.
	Query(p, row) :: {
		table : Str,
		source : Translate.Binding,
		filters : List(Clause),
		fetches : List(Try(Str, Error)),
	}.{

		## The cut of filters, projections and keys (see `Surreal.code_primitives`).
		code_primitives = (Surreal.Link.get, Surreal.Link.id, Surreal.Id.is_eq, Surreal.Id.key, Surreal.Id.table, Surreal.Datetime.is_lt, Surreal.Datetime.is_lte, Surreal.Text.is_email, Surreal.Text.is_url, Surreal.Text.is_domain, Surreal.Text.is_ip, Surreal.Text.is_ipv4, Surreal.Text.is_ipv6, Surreal.Text.is_uuid, Surreal.Text.is_ulid, Surreal.Text.is_semver, Surreal.Text.is_alpha, Surreal.Text.is_alphanum, Surreal.Text.is_numeric, Surreal.Text.is_latitude, Surreal.Text.is_longitude, Surreal.Text.is_datetime, Surreal.Text.matches, Surreal.Text.similarity_jaro, Surreal.Text.similarity_jaro_winkler, Surreal.Text.distance_levenshtein, Surreal.Text.distance_damerau_levenshtein, Surreal.Text.distance_normalized_levenshtein, Surreal.Text.is_ascii, Surreal.Text.is_hexadecimal, Surreal.Hash.sha256, Surreal.Hash.blake3, Surreal.Hash.md5, Surreal.Hash.sha1, Surreal.Hash.sha512, Surreal.Array.distinct, Surreal.Array.union, Surreal.Array.intersect, Surreal.Array.complement, Surreal.Time.now, Surreal.Time.floor, Surreal.Time.ceil, Surreal.Time.round, Surreal.Time.group, Surreal.Time.plus, Surreal.Time.minus, Surreal.Time.wday, Surreal.Time.yday, Surreal.Time.week, Surreal.Time.unix, Surreal.Time.unix_millis, Surreal.Time.unix_micros, Surreal.Time.nano, Surreal.Time.format, Surreal.Time.from_unix, Surreal.Time.year, Surreal.Time.month, Surreal.Time.day, Surreal.Time.hour, Surreal.Time.minute, Surreal.Time.second, Surreal.Math.mean, Surreal.Math.median, Surreal.Math.stddev, Surreal.Math.variance, Surreal.Math.percentile, Surreal.Rand.uuid, Surreal.Rand.ulid, Surreal.Rand.int)

		## Keep the rows the function is true for: `WHERE`.
		filter : Query(p, row), Code(row -> Bool) -> Query(p, row)
		filter = |Query.(q), predicate| {
			base = q.source
			clause = |param| Translate.render(predicate.graph(), [base], param)
			Query.({ ..q, filters: q.filters.append(clause) })
		}

		## A filter that reads the parameter record, its first argument. Each
		## field it reads is a `$name` that `bind` gives a `LET`.
		filter_by : Query(p, row), Code((p, row -> Bool)) -> Query(p, row)
		filter_by = |Query.(q), predicate| {
			base = q.source
			clause = |param| Translate.render(predicate.graph(), [Translate.Binding.Params, base], param)
			Query.({ ..q, filters: q.filters.append(clause) })
		}

		## Read the row a link points to along with the row: `FETCH customer`.
		fetch : Query(p, row), Code(row -> Link(t)) -> Query(p, row)
		fetch = |Query.(q), path| Query.({ ..q, fetches: q.fetches.append(Translate.path_of(path.graph()).map_ok(Translate.spell)) })

		## Read the rows the links in a list point to: `FETCH items[*].product`.
		fetch_each : Query(p, row), Code(row -> List(Link(t))) -> Query(p, row)
		fetch_each = |Query.(q), path| Query.({ ..q, fetches: q.fetches.append(Translate.path_of(path.graph()).map_ok(Translate.spell)) })

		## The row and its edges in `edges`, `->edges`. The row becomes the pair
		## `(row, List(edge))`, which a clause takes apart with a tuple pattern.
		outgoing : Query(p, a), Table(e) -> Query(p, (a, List(e)))
		outgoing = |Query.(q), Table.(t)| Query.({ table: q.table, source: Translate.Binding.Pair(q.source, Translate.outgoing(t.name)), filters: q.filters, fetches: q.fetches })

		## As `outgoing`, with the edges that point at the row: `<-edges`.
		incoming : Query(p, b), Table(e) -> Query(p, (b, List(e)))
		incoming = |Query.(q), Table.(t)| Query.({ table: q.table, source: Translate.Binding.Pair(q.source, Translate.incoming(t.name)), filters: q.filters, fetches: q.fetches })

		## Every field of the row: `SELECT *`.
		select_all : Query(p, row) -> Selected(p, row)
		select_all = |Query.(q)| {
			results = |_| Ok(Translate.Binding.Row({ at: "", of: Obj, edge: Bool.False }))
			Surreal.selected(q, |_| Ok("*"), results, [])
		}

		## The columns of the result. The function returns a record, and its
		## fields name the columns, in name order: `SELECT e AS f, ..`.
		select : Query(p, row), Code(row -> out) -> Selected(p, out)
		select = |Query.(q), projection| {
			base = q.source
			columns = |param| Ok(Surreal.aliased(Translate.columns(projection.graph(), [base], param)?))
			Surreal.selected(q, columns, Surreal.by_name, [])
		}

		## One value per row: `SELECT VALUE e`.
		select_value : Query(p, row), Code(row -> v) -> Selected(p, v)
		select_value = |Query.(q), projection| {
			base = q.source
			value = |param| Translate.render(projection.graph(), [base], param)
			columns = |param| Ok("VALUE ${value(param)?}")
			results = |param| Ok(Translate.Binding.Expr(value(param)?))
			Surreal.selected(q, columns, results, [])
		}

		## Group the rows by what the function returns: a value, or a record of
		## them.
		group_by : Query(p, row), Code(row -> k) -> Grouped(p, row, k)
		group_by = |query, key| Grouped.({ query: query, key: key })
	}

	## Rows grouped by a key, waiting for what to compute per group.
	Grouped(p, row, k) :: { query : Query(p, row), key : Code(row -> k) }.{

		## The cut of the per-group function, which reads the group's rows
		## (see `Surreal.code_primitives`).
		code_primitives = (Surreal.Link.get, Surreal.Link.id, Surreal.Id.is_eq, Surreal.Id.key, Surreal.Id.table, Surreal.Datetime.is_lt, Surreal.Datetime.is_lte, Surreal.Text.is_email, Surreal.Text.is_url, Surreal.Text.is_domain, Surreal.Text.is_ip, Surreal.Text.is_ipv4, Surreal.Text.is_ipv6, Surreal.Text.is_uuid, Surreal.Text.is_ulid, Surreal.Text.is_semver, Surreal.Text.is_alpha, Surreal.Text.is_alphanum, Surreal.Text.is_numeric, Surreal.Text.is_latitude, Surreal.Text.is_longitude, Surreal.Text.is_datetime, Surreal.Text.matches, Surreal.Text.similarity_jaro, Surreal.Text.similarity_jaro_winkler, Surreal.Text.distance_levenshtein, Surreal.Text.distance_damerau_levenshtein, Surreal.Text.distance_normalized_levenshtein, Surreal.Text.is_ascii, Surreal.Text.is_hexadecimal, Surreal.Hash.sha256, Surreal.Hash.blake3, Surreal.Hash.md5, Surreal.Hash.sha1, Surreal.Hash.sha512, Surreal.Array.distinct, Surreal.Array.union, Surreal.Array.intersect, Surreal.Array.complement, Surreal.Time.now, Surreal.Time.floor, Surreal.Time.ceil, Surreal.Time.round, Surreal.Time.group, Surreal.Time.plus, Surreal.Time.minus, Surreal.Time.wday, Surreal.Time.yday, Surreal.Time.week, Surreal.Time.unix, Surreal.Time.unix_millis, Surreal.Time.unix_micros, Surreal.Time.nano, Surreal.Time.format, Surreal.Time.from_unix, Surreal.Time.year, Surreal.Time.month, Surreal.Time.day, Surreal.Time.hour, Surreal.Time.minute, Surreal.Time.second, Surreal.Math.mean, Surreal.Math.median, Surreal.Math.stddev, Surreal.Math.variance, Surreal.Math.percentile, Surreal.Rand.uuid, Surreal.Rand.ulid, Surreal.Rand.int)

		## One result row per group. The function takes the key and the group's
		## rows as a `List(row)`: `rows.len()` is `count()`, and
		## `rows.map(f).sum()` is `math::sum(f)`.
		aggregate : Grouped(p, row, k), Code((k, List(row) -> out)) -> Selected(p, out)
		aggregate = |Grouped.(g), per_group| {
			Query.(q) = g.query
			base = q.source
			key = g.key
			groups = |param| {
				parts = Surreal.parts_of(Translate.evaluate(key.graph(), [base], param)?)?
				Ok(Str.join_with(parts, ", "))
			}
			columns = |param| {
				group_key = Translate.evaluate(key.graph(), [base], param)?
				Ok(Surreal.aliased(Translate.columns(per_group.graph(), [group_key, Translate.Binding.Group(base)], param)?))
			}
			Surreal.selected(q, columns, Surreal.by_name, [groups])
		}
	}

	## A query with its result columns fixed.
	Selected(p, out) :: {
		table : Str,
		filters : List(Clause),
		fetches : List(Try(Str, Error)),
		groups : List(Clause),
		columns : Clause,
		results : (Str -> Str) -> Try(Translate.Binding, Error),
		order : List(Clause),
		limit : [Unlimited, Limit(U64)],
		start : [FromFirst, Start(U64)],
	}.{

		## Order by what the function reads off a result row, so it names the
		## result's columns. Several calls order by the first, then the second.
		## The type has no cut: an ordering names a column. SurrealDB accepts a
		## path through a link column after `ORDER BY`, but does not order by it.
		order_by : Selected(p, out), Code(out -> k), [Asc, Desc] -> Selected(p, out)
		order_by = |Selected.(s), key, direction| {
			clause = |param| {
				result = (s.results)(param)?
				parts = Surreal.parts_of(Translate.evaluate(key.graph(), [result], param)?)?
				suffix = match direction {
					Asc => ""
					Desc => " DESC"
				}
				Ok(Str.join_with(parts.map(|part| "${part}${suffix}"), ", "))
			}
			Selected.({ ..s, order: s.order.append(clause) })
		}

		## At most this many rows.
		limit : Selected(p, out), U64 -> Selected(p, out)
		limit = |Selected.(s), count| Selected.({ ..s, limit: Limit(count) })

		## Skip this many rows first.
		start : Selected(p, out), U64 -> Selected(p, out)
		start = |Selected.(s), count| Selected.({ ..s, start: Start(count) })

		## The statement with a `$name` for each parameter it reads.
		to_surql : Selected(p, out) -> Try(Str, Error)
		to_surql = |selected| Selected.render(selected, Translate.variable)

		## The statement and a `LET` for each field of the parameter record.
		## The record is the type the filters read, so a parameter a filter
		## reads is a field the record has.
		bind : Selected(p, out), p -> Try(Statement, Error) where [p.encoder_for : Encode.Format -> (p, Encode.State -> Try(Encode.State, []))]
		bind = |selected, params| Surreal.bound(|param| Selected.render(selected, param), params)

		render : Selected(p, out), (Str -> Str) -> Try(Str, Error)
		render = |Selected.(s), param| {
			run = |clause| clause(param)
			filters = s.filters.map_try(run)?
			parts = [
				"SELECT ${run(s.columns)?}",
				"FROM ${Ql.ident(s.table)}",
			]
				.concat(Surreal.keyword("WHERE", if (filters.len() > 1) filters.map(|f| "(${f})") else filters, " AND "))
				.concat(Surreal.keyword("GROUP BY", s.groups.map_try(run)?, ", "))
				.concat(Surreal.keyword("ORDER BY", s.order.map_try(run)?, ", "))
				.concat(
					match s.limit {
						Unlimited => []
						Limit(n) => ["LIMIT ${n.to_str()}"]
					},
				)
				.concat(
					match s.start {
						FromFirst => []
						Start(n) => ["START ${n.to_str()}"]
					},
				)
				.concat(Surreal.keyword("FETCH", s.fetches.map_try(|f| f)?, ", "))
			Ok(Str.join_with(parts, " "))
		}
	}

	## A write that reads a clause: an update or a delete.
	Write(p, row) :: { build : (Str -> Str) -> Try(Str, Error) }.{

		## The statement with a `$name` for each parameter it reads.
		to_surql : Write(p, row) -> Try(Str, Error)
		to_surql = |Write.(w)| (w.build)(Translate.variable)

		## The statement and a `LET` for each field of the parameter record.
		bind : Write(p, row), p -> Try(Statement, Error) where [p.encoder_for : Encode.Format -> (p, Encode.State -> Try(Encode.State, []))]
		bind = |Write.(w), params| Surreal.bound(w.build, params)
	}

	## A statement ready for a driver: the text with a `$name` per parameter,
	## the value each name is bound to, and the same text with the values
	## written in. `surql` has no final `;`.
	Statement := { surql : Str, lets : List({ name : Str, value : Ql.Value }), inlined : Str }.{

		## What a script holds: a `LET` line per parameter, then the statement.
		to_script : Statement -> Str
		to_script = |Statement.(s)| {
			lets = s.lets.map(|l| "LET $${l.name} = ${Ql.literal(l.value)};")
			Str.join_with(lets.append("${s.surql};"), "\n")
		}

		## One block of a script that `check.py` runs: the header line, the
		## directive lines (`-- ordered`, `-- roc: ..`), then the script.
		block : Statement, Str, List(Str) -> Str
		block = |statement, header, directives| Str.join_with(List.concat([header], directives).append(statement.to_script()), "\n")

		## This statement, then the other. A name bound in both must have one value.
		then : Statement, Statement -> Try(Statement, Error)
		then = |Statement.(a), Statement.(b)| {
			text = |l| Ql.literal(l.value)
			clash = b.lets.find_first(|l| a.lets.any(|m| m.name == l.name and text(m) != text(l)))
			match clash {
				Ok(l) => Err(Unsupported("`$${l.name}` is bound to two different values in one script"))
				Err(_) =>
					Ok(
						Statement.(
							{
								surql: "${a.surql};\n${b.surql}",
								lets: a.lets.concat(b.lets.keep_if(|l| !a.lets.any(|m| m.name == l.name))),
								inlined: "${a.inlined};\n${b.inlined}",
							},
						),
					)
			}
		}
	}

	## Every column of the rows of `table` that the filter keeps, where the
	## filter reads values from around the function it is written in, such as
	## a parameter. The translator runs while the compiler runs, so it writes a
	## `$_1`, `$_2`, ... for each captured value, and the program receives the
	## values in the result's `inputs`. `slots` are the types of those values.
	select_where : Table(row), Code(row -> Bool) -> Code.Bound(Try({ surql : Str, slots : List(Code.Ty) }, Error))
	select_where = |Table.(t), predicate| {
		graph = predicate.graph()
		rendered = Translate.render(graph, [Translate.document("", Surreal.is_edge(t.kind))], Translate.variable)
		Code.bound(predicate, rendered.map_ok(|condition| { surql: "SELECT * FROM ${Ql.ident(t.name)} WHERE ${condition}", slots: graph.slots() }))
	}

	## The statement [Surreal.select_where] built, with a `LET` for each
	## captured value.
	bind_captured : Code.Bound(Try({ surql : Str, slots : List(Code.Ty) }, Error)) -> Try(Statement, Error)
	bind_captured = |bound| {
		built = bound.value()?
		inputs = bound.inputs()
		if inputs.len() != built.slots.len() {
			return Err(Unsupported("the clause captured ${inputs.len().to_str()} value(s) but has ${built.slots.len().to_str()} slot(s)"))
		}
		lets = List.map2(built.slots, inputs, |ty, value| { ty, value })
			.map_with_index(|pair, k| (k, pair))
			.map_try(|(k, pair)| Ok({ name: Translate.input_name(k), value: Translate.captured(pair.ty, pair.value)? }))?
		# The last name first, so `$_1` never matches the start of `$_10`.
		inlined = lets.fold_rev(built.surql, |l, text| text.replace_each("$${l.name}", Ql.literal(l.value)))
		Ok(Statement.({ surql: built.surql, lets, inlined }))
	}

	## The id of a row by its table's name. Unlike `Table.id`, a constant made
	## with it can be read in a clause: `Table.id` reads the table, which holds
	## the reified type, and a clause cannot hold that.
	id_of : Str, Str -> Id(row)
	id_of = |name, key| Id.({ table: name, key: key, phantom: [] })

	## A Roc value as a SurrealQL literal: the reference result of a query,
	## which `check.py` compares with what the database returns.
	literal : a -> Try(Str, Error) where [a.encoder_for : Encode.Format -> (a, Encode.State -> Try(Encode.State, []))]
	literal = |value| Encode.value_of(value).map_ok(Ql.literal)

	## The table's rows, to start a query from.
	from : Table(row) -> Query(p, row)
	from = |Table.(t)| Query.({ table: t.name, source: Translate.document("", Surreal.is_edge(t.kind)), filters: [], fetches: [] })

	# ------------------------------------------------------------- helpers

	is_edge : Types.Kind -> Bool
	is_edge = |kind| match kind {
		Relation(_) => Bool.True
		Normal => Bool.False
	}

	selected : { table : Str, filters : List(Clause), fetches : List(Try(Str, Error)), source : Translate.Binding }, Clause, ((Str -> Str) -> Try(Translate.Binding, Error)), List(Clause) -> Selected(p, out)
	selected = |q, columns, results, groups| Selected.(
		{
			table: q.table,
			filters: q.filters,
			fetches: q.fetches,
			groups: groups,
			columns: columns,
			results: results,
			order: [],
			limit: Unlimited,
			start: FromFirst,
		},
	)

	## A result row is read by the names of its columns, so `id` is the column
	## and not the key of the record.
	by_name : (Str -> Str) -> Try(Translate.Binding, Error)
	by_name = |_| Ok(Translate.Binding.Row({ at: "", of: Obj, edge: Bool.False }))

	aliased : List({ name : Str, surql : Str }) -> Str
	aliased = |columns| Str.join_with(columns.map(|c| "${c.surql} AS ${Ql.ident(c.name)}"), ", ")

	## The values a key or an ordering is made of: one, or a record's fields.
	parts_of : Translate.Binding -> Try(List(Str), Error)
	parts_of = |binding| match binding {
		Fields(fields) => fields.map_try(|f| Translate.text(f.binding))
		other => Translate.text(other).map_ok(|one| [one])
	}

	keyword : Str, List(Str), Str -> List(Str)
	keyword = |word, parts, separator| if (parts.is_empty()) [] else ["${word} ${Str.join_with(parts, separator)}"]

	set_list : List({ name : Str, surql : Str }) -> Str
	set_list = |sets| Str.join_with(sets.map(|a| "${a.name} = ${a.surql}"), ", ")

	statement : Str -> Statement
	statement = |surql| Statement.({ surql, lets: [], inlined: surql })

	## The fields a row or a parameter record encodes to.
	object_of : a -> Try(List({ name : Str, value : Ql.Value }), Error) where [a.encoder_for : Encode.Format -> (a, Encode.State -> Try(Encode.State, []))]
	object_of = |value| match Encode.value_of(value)? {
		Object(fields) => Ok(fields)
		_ => Err(Unsupported("a row or a parameter record is a record"))
	}

	## The ends of an edge are SurrealDB's `in` and `out`.
	ends_named : List({ name : Str, value : Ql.Value }), Types.Kind -> List({ name : Str, value : Ql.Value })
	ends_named = |fields, kind| fields.map(|f| { ..f, name: Translate.spell_name(f.name, Surreal.is_edge(kind)) })

	field_of : List({ name : Str, value : Ql.Value }), Str -> Try(Ql.Value, Error)
	field_of = |fields, name| match fields.find_first(|f| f.name == name) {
		Ok(f) => Ok(f.value)
		Err(_) => Err(Unsupported("a row of a relation table has the field for `${name}`"))
	}

	## A row split into its key and the other fields, the key written once
	## as the record id and not again in the content.
	split_id : { name : Str, row_ty : Code.Ty, kind : Types.Kind }, a -> Try({ key : Str, fields : List({ name : Str, value : Ql.Value }) }, Error) where [a.encoder_for : Encode.Format -> (a, Encode.State -> Try(Encode.State, []))]
	split_id = |t, row| {
		fields = Surreal.ends_named(Surreal.object_of(row)?, t.kind)
		match fields.find_first(|f| f.name == "id") {
			Ok({ value: Str(key), .. }) => Ok({ key, fields: fields.keep_if(|f| f.name != "id") })
			_ => Err(Unsupported("a row of `${t.name}` needs an `id : Str` field, the record key"))
		}
	}

	content_write : Str, { name : Str, row_ty : Code.Ty, kind : Types.Kind }, a -> Try(Statement, Error) where [a.encoder_for : Encode.Format -> (a, Encode.State -> Try(Encode.State, []))]
	content_write = |verb, t, row| {
		split = Surreal.split_id(t, row)?
		Ok(Surreal.statement("${verb} ${Ql.record_id(t.name, split.key)} CONTENT ${Ql.literal(Ql.Value.Object(split.fields))}"))
	}

	## Fields a statement cannot take as a `LET`: SurrealDB sets them itself.
	protected : List(Str)
	protected = ["session", "auth", "token", "access"]

	## A statement over the parameter record: its text with names, the `LET`
	## of each field, and its text with the values written in.
	bound : ((Str -> Str) -> Try(Str, Error)), p -> Try(Statement, Error) where [p.encoder_for : Encode.Format -> (p, Encode.State -> Try(Encode.State, []))]
	bound = |render, params| {
		lets = Surreal.object_of(params)?
		match lets.find_first(|l| Surreal.protected.contains(l.name)) {
			Ok(l) => return Err(Unsupported("`$${l.name}` is a protected variable in SurrealDB; name the parameter otherwise"))
			Err(_) => {}
		}
		surql = render(Translate.variable)?
		inlined = render(
			|name| match lets.find_first(|l| l.name == name) {
				Ok(l) => Ql.literal(l.value)
				Err(_) => Translate.variable(name)
			},
		)?
		Ok(Statement.({ surql, lets, inlined }))
	}
}

# ------------------------------------------------------------------ tests

Person : { id : Str, name : Str }

people : Surreal.Table(Person)
people = Surreal.table("person", |p| p)

ada : Person
ada = { id: "ada", name: "Ada" }

fetched_ada : Surreal.Link(Person)
fetched_ada = Surreal.fetched(people, ada)

# Ids and links are equal by table and key.
expect people.id("ada") == people.id("ada")
expect people.id("ada") != people.id("bob")
expect people.id("ada").key() == "ada"
expect people.link("ada") == fetched_ada
expect people.link("ada") != people.link("bob")
expect fetched_ada.get().name == "Ada"
expect fetched_ada.id() == people.id("ada")

# What a row holding a link or an id is written as.
Holder : { id : Str, who : Surreal.Link(Person), by : Surreal.Id(Person), at : Surreal.Datetime }

holder : Holder
holder = match Surreal.datetime("2026-10-28T04:53:59Z") {
	Ok(at) => { id: "h", who: fetched_ada, by: people.id("o'neil"), at: at }
	Err(_) => crash "a valid datetime"
}

expect Encode.value_of(holder).map_ok(Ql.literal) == Ok("{ at: d'2026-10-28T04:53:59Z', by: person:⟨o'neil⟩, id: 'h', who: person:⟨ada⟩ }")

expect Surreal.literal([{ id: "a", n: 2.U8 }, { id: "b", n: 3 }]) == Ok("[{ id: 'a', n: 2 }, { id: 'b', n: 3 }]")

# Datetimes: one shape in, one text out.
iso_of : Str -> Str
iso_of = |text| match Surreal.datetime(text) {
	Ok(d) => Str.inspect(d)
	Err(BadDatetime) => "bad"
}

expect iso_of("2026-10-28T04:53:59Z") == "{ iso: \"2026-10-28T04:53:59Z\" }"
expect iso_of("2026-10-28T04:53:59.500Z") == "{ iso: \"2026-10-28T04:53:59.5Z\" }"
expect iso_of("2026-10-28T04:53:59.000Z") == "{ iso: \"2026-10-28T04:53:59Z\" }"
expect iso_of("2026-10-28T04:53:59.123456789Z") == "{ iso: \"2026-10-28T04:53:59.123456789Z\" }"
expect iso_of("2024-02-29T00:00:00Z") == "{ iso: \"2024-02-29T00:00:00Z\" }"
expect iso_of("2026-02-29T00:00:00Z") == "bad"
expect iso_of("1900-02-29T00:00:00Z") == "bad"
expect iso_of("2000-02-29T00:00:00Z") == "{ iso: \"2000-02-29T00:00:00Z\" }"
expect iso_of("2026-13-01T00:00:00Z") == "bad"
expect iso_of("2026-04-31T00:00:00Z") == "bad"
expect iso_of("2026-10-28T24:00:00Z") == "bad"
expect iso_of("2026-10-28T04:60:00Z") == "bad"
expect iso_of("2026-10-28T04:53:60Z") == "bad"
expect iso_of("2026-10-28T04:53:59") == "bad"
expect iso_of("2026-10-28T04:53:59+01:00") == "bad"
expect iso_of("2026-10-28 04:53:59Z") == "bad"
expect iso_of("2026-10-28T04:53:59.Z") == "bad"
expect iso_of("2026-10-28T04:53:59.1234567890Z") == "bad"
expect iso_of("2026-1a-28T04:53:59Z") == "bad"
expect iso_of("") == "bad"

# Order is time order, with or without a fraction.
at : Str -> Surreal.Datetime
at = |text| match Surreal.datetime(text) {
	Ok(d) => d
	Err(_) => crash "a valid datetime"
}

expect at("2026-10-28T04:53:59Z") < at("2026-10-28T04:54:00Z")
expect at("2026-10-28T04:53:59Z") < at("2026-10-28T04:53:59.5Z")
expect at("2026-10-28T04:53:59.25Z") < at("2026-10-28T04:53:59.5Z")
expect at("2026-10-28T04:53:59.05Z") < at("2026-10-28T04:53:59.5Z")
expect !(at("2026-10-28T04:53:59.5Z") < at("2026-10-28T04:53:59Z"))
expect !(at("2026-10-28T04:53:59Z") < at("2026-10-28T04:53:59Z"))
expect at("2026-10-28T04:53:59Z") <= at("2026-10-28T04:53:59.000Z")
expect at("2026-10-28T04:53:59.5Z") > at("2026-10-28T04:53:59Z")
expect at("2026-10-28T04:53:59Z") >= at("2026-10-28T04:53:59Z")
expect at("2026-10-28T04:53:59.500Z") == at("2026-10-28T04:53:59.5Z")

# Tables: a plain one, and an edge table that remembers both ends.
Knows : { id : Str, from : Surreal.Link(Person), to : Surreal.Link(Person), since : I64 }

knows : Surreal.Table(Knows)
knows = Surreal.relation("knows", people, people, |e| e)

expect Surreal.source(people).name == "person"
expect Surreal.source(people).kind == Types.Kind.Normal
expect Surreal.source(knows).name == "knows"
expect Surreal.source(knows).kind == Types.Kind.Relation({ from: { name: "person", row_ty: Surreal.source(people).row_ty }, to: { name: "person", row_ty: Surreal.source(people).row_ty } })
expect Surreal.source(people).row_ty == Record([{ name: "id", ty: Str, presence: Required }, { name: "name", ty: Str, presence: Required }])
