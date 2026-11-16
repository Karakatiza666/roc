# A method bound to a computed callable of another module, whose closure
# holds a Code site at a variable the binding leaves free, selected by
# `where` evidence and by a direct dispatch (Q14 of
# roc-reify-structural-proposal.md). Each edge relates the binding's entry
# wrapper to the callable it selects, so the edge's table describes the
# closure at that owner type (design.md "Code Instance Tables").
import Par

label_of : x -> Str where [x.label : x -> Str]
label_of = |x| x.label()

main! = |_args| {
	par : Par.Par(Str)
	par = Par.Par.({ row: "x" })
	pet : Par.Par({ id : U8 })
	pet = Par.Par.({ row: { id: 1 } })
	echo!("${label_of(par)}\n")
	echo!("${label_of(pet)}\n")
	echo!("${par.label()}\n")
	Ok({})
}
