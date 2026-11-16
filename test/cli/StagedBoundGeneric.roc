# A generic function whose `Code.Bound` call has a type variable of the
# function in its type (R7 of the Gap 1 design). Each closing use fixes the
# type, so each use binds the call's inputs at its own instance.
Q := [Q(Str)].{
	from : Str -> Q
	from = |name| Q(name)

	filter : Q, Code(U16 -> Bool) -> Q
	filter = |Q(text), code| Q("${text} where slots ${Code.graph(code).slots().len().to_str()} from ${code.first_slot().to_str()}")

	ready : Q -> Code.Bound(Try(Str, [NotFound, ..e]))
	ready = |Q(text)| Code.Bound.of(Ok(text))
}

fetch = |least, most| Q.from("meds").filter(|m| m > least).filter(|m| m < most).ready()

show = |bound| {
	text = match bound.value() {
		Ok(t) => t
		Err(_) => "err"
	}
	"${text} inputs ${Str.inspect(bound.inputs())}"
}

main! = |_args| {
	a : Code.Bound(Try(Str, [NotFound, Other]))
	a = fetch(1, 9)
	b : Code.Bound(Try(Str, [NotFound]))
	b = fetch(2, 8)
	echo!("${show(a)}\n${show(b)}\n")
	Ok({})
}
