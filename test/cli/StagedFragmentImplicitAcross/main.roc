# A method bound by value to a function of another module that holds a Code
# site at its own variables (Q17 of roc-reify-structural-proposal.md). The
# compiler calls `Other.render` for inspection, with no written use. Each
# type occurrence of the owner describes the method at that type, so the
# method is described at each owner type the program inspects.
import Other

Pet : { id : Str, name : Str }

## Bound directly to a function of another module.
Rows(r) := { row : r }.{
	to_inspect : Rows(r) -> Str
	to_inspect = Other.render
}

render_here : a -> Str
render_here = Other.render

## Bound through a binding of this module.
Chained(r) := { row : r }.{
	to_inspect : Chained(r) -> Str
	to_inspect = render_here
}

## Inspection through a type variable.
show : a -> Str
show = |x| Str.inspect(x)

## A generic function that builds the owner type at its own variable.
wrap : a -> Rows(a)
wrap = |x| Rows.({ row: x })

## A generic function that inspects the owner type it builds.
shown_rows : a -> Str
shown_rows = |x| Str.inspect(Rows.({ row: x }))

main! = |_args| {
	pet = { id: "1", name: "rex" }
	rows : Rows(Pet)
	rows = Rows.({ row: pet })
	chained : Chained(Pet)
	chained = Chained.({ row: pet })
	local = rows
	echo!("direct: ${Other.render(pet)}\n")
	echo!("inspect: ${Str.inspect(rows)} ${Str.inspect(chained)} ${Str.inspect(local)}\n")
	echo!("record: ${Str.inspect({ r: rows })}\n")
	echo!("list: ${Str.inspect([rows])}\n")
	echo!("show: ${show(rows)}\n")
	echo!("wrap: ${show(wrap(pet))}\n")
	echo!("generic: ${shown_rows(pet)}\n")
	echo!("other: ${shown_rows("x")}\n")
	Ok({})
}
