# `{ name }` is a block whose value is `name`, not a record. Where a nominal
# type that wraps a record expects it, the report says so and names the
# record spellings.
Opq := { name : Str }

make : Str -> Opq
make = |name| Opq.({ name })

main! = |_args| {
	_o = make("x")
	Ok({})
}
