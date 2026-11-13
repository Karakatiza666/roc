# A descriptor method whose body calls a generic function that binds its
# inputs with a `Code.Bound` translator is refused at the method (Q17). A
# call that selects the method through `where` evidence is refused too: the
# bound call's root at that call has no table to bind its inputs. Both
# lowerings read the refused method as a rejected declaration, so the call
# crashes.
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
	is_eq : Rows(e), Rows(e) -> Bool
	is_eq = |a, b| {
		bound : Code.Bound(Try(Str, [NotFound, ..e]))
		bound = fetch(a.least)
		bound.inputs().len() > 0 and a.least == b.least
	}
}

same : a, a -> Bool where [a.is_eq : a, a -> Bool]
same = |x, y| x.is_eq(y)

main! = |_args| {
	r : Rows([Other])
	r = Rows.({ least: 3, last: Err(NotFound) })
	echo!("same: ${Str.inspect(same(r, r))}\n")
	Ok({})
}
