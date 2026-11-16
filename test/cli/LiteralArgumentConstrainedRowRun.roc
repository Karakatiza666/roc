# A local generic function with a numeric literal, called with a value whose
# type names a constrained row variable of the enclosing function, and a call
# that fixes the row to a nominal (issue 13085).
Named := { name : Str }.{
	describe : Named -> Str
	describe = |n| n.name
}

Row(r) : { id : Str, ..r }

make : { id : Str, ..new } -> U64 where [new.describe : new -> Str]
make = |whole| {
	built = |x| { count: 1, got: x }
	built(whole).count
}

main! = |_args| {
	row : Row(Named)
	row = { id: "a", name: "b" }
	echo!("count: ${make(row).to_str()}")
	Ok({})
}
