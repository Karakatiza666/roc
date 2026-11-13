# A site whose function fails to check has one report: the checker's.
#
# Each function here calls a method that `U64` does not have. The checker
# reports that, and the site the function stands at is refused with no report
# of its own: a lambda written at the site, a function the site names, and a
# lambda at a site in a generic function, which its closing use describes.
Q(row) := {}.{
	filter : Q(row), Code(row -> Bool) -> Str
	filter = |_, code| "rows ${Code.graph(code).root_row().params.len().to_str()}"
}

stage : Code(U64 -> Bool) -> Str
stage = |code| "rows ${Code.graph(code).root_row().params.len().to_str()}"

pred : U64 -> Bool
pred = |x| x.is_small()

helper : Q(r) -> Str
helper = |q| q.filter(|o| o.is_large())

numbers : Q(U64)
numbers = Q.({})

main! = |_args| {
	echo!(stage(|x| x.is_tiny()))
	echo!(stage(pred))
	echo!(helper(numbers))
	Ok({})
}
