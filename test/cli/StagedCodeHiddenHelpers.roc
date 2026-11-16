# The helpers behind the `Code` API are private to the builtin module. A user
# program cannot call them, and in particular cannot forge the refusal of a
# site with a raw key: only `Code.refuse_at` refuses, and it reads the key from
# the `Code` it is given.

main! = |_args| {
	_ = Code.refuse(12345, 0, 0, "forged refusal")
	echo!("${Code.at_index([5, 6], 1).to_str()}\n")
	Ok({})
}
