# A top-level constant that holds a closure over an intrinsic. Evaluating
# `make(2.0)` calls nothing, but the rule is per definition, so `make` exists
# only in reified code and the constant is refused.
Text :: {}.{
	is_close : F64, F64 -> Bool
}

make : F64 -> (F64 -> Bool)
make = |k| |x| Text.is_close(x, k)

doubler : F64 -> Bool
doubler = make(2.0)

main! = |_args| {
	echo!(if doubler(1.0) "yes\n" else "no\n")
	Ok({})
}
