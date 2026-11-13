# An import inside a body. The parser refuses it before a description could
# meet one.
main! = |_args| {
	import Foo
	echo!("x\n")
	Ok({})
}
