# A `var` whose initializer is a method call over literals is a hoisted
# constant. Monotype restores it from the stored value, so it must not expect
# the closed result of the dispatch it was written as.
add_six : U64 -> U64
add_six = |n| {
	var $a = 3.U64 * 2
	$a = $a + n
	$a
}

answer : U64
answer = add_six(1)

main! = |_args| {
	var $b = 3.U64 * 2
	$b = $b + 1
	echo!("${answer.to_str()} ${$b.to_str()}\n")
	Ok({})
}
