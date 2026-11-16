# A value known only at run time, given to a call of a chain outside a lambda
# (compiler-gaps.md Gap 1, R9).
#
# The chain up to `ready` or `prepare` runs once, while the compiler runs, so
# each argument of its calls outside a lambda must be fixed then. `n` in
# `.limit(n)` and `least` in the record that `prepare` takes are not, so the
# lambda is refused, and the report names the lambda form. `limit_code` reads
# the same value in a lambda, where it is an input slot.
Q := [Q(Str)].{
	from : Str -> Q
	from = |table| Q("FROM ${table}")

	filter : Q, Code(U16 -> Bool) -> Q
	filter = |Q(text), _code| Q("${text} WHERE")

	limit : Q, U64 -> Q
	limit = |Q(text), n| Q("${text} LIMIT ${n.to_str()}")

	limit_code : Q, Code(U16 -> U64) -> Q
	limit_code = |Q(text), _code| Q("${text} LIMIT ?")

	prepare : Q, { least : U16 } -> Code.Bound(Str)
	prepare = |Q(text), args| Code.Bound.of("${text} ${args.least.to_str()}")

	ready : Q -> Code.Bound(Str)
	ready = |Q(text)| Code.Bound.of(text)
}

limited : U16, U64 -> Str
limited = |least, n| Q.from("meds").filter(|m| m > least).limit(n).ready().value()

prepared : U16 -> Str
prepared = |least| Q.from("meds").filter(|m| m > least).prepare({ least: least }).value()

in_lambda : U16, U64 -> Str
in_lambda = |least, n| {
	bound = Q.from("meds").filter(|m| m > least).limit_code(|_| n).ready()
	"${bound.value()} inputs ${bound.inputs().len().to_str()}"
}

main! = |_args| {
	echo!("${limited(3, 4)} ${prepared(2)} ${in_lambda(1, 5)}\n")
	Ok({})
}
