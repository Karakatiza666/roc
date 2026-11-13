# `{ name }` is a block whose value is `name`, not a record. Where the
# annotation expects a record, the report says so and names the record
# spellings.
r : Str -> { name : Str }
r = |name| { name }

main! = |_args| {
	_o = r("x")
	Ok({})
}
