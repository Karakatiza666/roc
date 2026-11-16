# A name that does not exist, passed at a `Code` position, has one report:
# the checker's.
#
# Each `filter(..)` call below has an erroneous argument, so checking retires
# it into a runtime error that still evaluates its receiver. The receiver is a
# closing use of the fragment `named_only`, whose site is described at each
# closing use, so the use gets its instance table like any other: once in a
# constant compile-time evaluation computes, once in `main!`.
Q(row) := { log : Str }.{
	filter : Q(row), Code(row -> Bool) -> Q(row)
	filter = |q, code| Q.({ log: "${q.log} ${Code.graph(code).root_row().params.len().to_str()}" })

	show : Q(row) -> Str
	show = |q| q.log
}

named_only : Q({ name : Str, ..r }) -> Q({ name : Str, ..r })
named_only = |q| q.filter(|x| x.name != "")

Pet : { name : Str, age : U8 }

pets : Q(Pet)
pets = Q.({ log: "pets" })

shown : Str
shown = named_only(pets).filter(undefined_fn).show()

main! = |_args| {
	echo!(shown)
	echo!(named_only(pets).filter(missing_pred).show())
	Ok({})
}
