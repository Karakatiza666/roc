# A descriptor method whose body calls a generic function that binds its
# inputs with a `Code.Bound` translator (Q17, design.md "Bound Instance
# Roots"). Only a written call roots such a call, and the compiler calls
# `to_inspect` with no written use, so the method is refused by name at the
# call. A refused method is a rejected declaration, so inspection renders
# the default form.
Q := [Q(Str)].{
	from : Str -> Q
	from = |name| Q(name)

	filter : Q, Code(U16 -> Bool) -> Q
	filter = |Q(text), code| Q("${text} slots ${Code.graph(code).slots().len().to_str()}")

	ready : Q -> Code.Bound(Try(Str, [NotFound, ..e]))
	ready = |Q(text)| Code.Bound.of(Ok(text))
}

fetch : U16 -> Code.Bound(Try(Str, [NotFound, ..e]))
fetch = |least| Q.from("meds").filter(|m| m > least).ready()

Rows(e) := { least : U16, last : Try(Str, [NotFound, ..e]) }.{
	to_inspect : Rows(e) -> Str
	to_inspect = |rows| {
		bound : Code.Bound(Try(Str, [NotFound, ..e]))
		bound = fetch(rows.least)
		text = match bound.value() {
			Ok(t) => t
			Err(_) => "err"
		}
		"${text} inputs ${Str.inspect(bound.inputs())}"
	}
}

main! = |_args| {
	rows : Rows([Other])
	rows = Rows.({ least: 3, last: Err(NotFound) })
	echo!("inspect: ${Str.inspect(rows)}\n")
	Ok({})
}
