# Two sites with one normal form give equal `Code` values, and a `Code` carries
# the normal-form version a translator keys its cache by.
#
# `double` and `twice` differ only in names, which the normal form does not
# hold, so they compare equal and one set holds them as one entry. `shifted` computes something else.
Stage := {}.{
	same : Code(U16 -> U16), Code(U16 -> U16) -> Str
	same = |a, b| {
		# A set keeps one entry for two values only where `is_eq` and
		# `to_hash` both agree.
		entries = Set.empty().insert(a).insert(b).len()
		if a == b "equal, ${entries.to_str()} set entry" else "different, ${entries.to_str()} set entries"
	}

	version : Code(U16 -> U16) -> Str
	version = |code| "version ${code.version().to_str()}"
}

double : U16 -> U16
double = |x| x * 2

twice : U16 -> U16
twice = |value| value * 2

shifted : U16 -> U16
shifted = |x| x + 2

main! = |_args| {
	echo!("${Stage.same(double, twice)}\n")
	echo!("${Stage.same(double, shifted)}\n")
	echo!("${Stage.version(double)}\n")
	Ok({})
}
