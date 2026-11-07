# A generic `Code.Bound` function stored in a constant. The constant is not
# generalized, so its one use fixes the type, and the call binds its input.
Q := [Q(Str)].{
	from : Str -> Q
	from = |name| Q(name)

	filter : Q, Code(U16 -> Bool) -> Q
	filter = |Q(text), code| Q("${text} where slots ${Code.graph(code).slots().len().to_str()}")

	ready : Q -> Code.Bound([A, ..e])
	ready = |Q(_text)| Code.Bound.of(A)
}

fetch : U16 -> Code.Bound([A, ..e])
fetch = |least| Q.from("meds").filter(|m| m > least).ready()

holder = { f: fetch }

main! = |_args| {
	a : Code.Bound([A])
	a = (holder.f)(3)
	echo!("${Str.inspect(a.inputs())}\n")
	Ok({})
}
