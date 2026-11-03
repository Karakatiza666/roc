# A method bound by value to a function of another module that holds a Code
# site at its own variables (Q17 of roc-reify-structural-proposal.md).
# The method registry follows a method bound by value only through this
# module's bindings, so these methods get no registry entry: inspection
# renders the default form and never calls `Other.render`. A written use of
# `Other.render` is described as usual. If the registry starts to follow such
# a binding, the Q17 refusal must reach it, and this test changes.
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

main! = |_args| {
	pet = { id: "1", name: "rex" }
	rows : Rows(Pet)
	rows = Rows.({ row: pet })
	chained : Chained(Pet)
	chained = Chained.({ row: pet })
	echo!("direct: ${Other.render(pet)}\n")
	echo!("inspect: ${Str.inspect(rows)} ${Str.inspect({ r: rows })} ${Str.inspect(chained)}\n")
	Ok({})
}
