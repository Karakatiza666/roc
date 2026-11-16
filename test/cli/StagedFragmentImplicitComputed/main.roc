# A method bound to a computed callable of another module, whose closure
# holds a Code site at a variable the binding leaves free (Q17 of
# roc-reify-structural-proposal.md). The compiler calls `to_inspect` with
# no written use. Each type occurrence of the owner describes the method at
# that type, and gives the binding's entry wrapper that table, so each
# owner type the program inspects has its own description. A written call
# of the closure is described as usual.
import Mk

Par(r) := { row : r }.{
	to_inspect = Mk.make({})
}

main! = |_args| {
	par : Par(Str)
	par = Par.({ row: "x" })
	echo!("direct: ${Mk.make({})(par)}\n")
	echo!("inspect: ${Str.inspect(par)}\n")
	pet : Par({ id : U8 })
	pet = Par.({ row: { id: 1 } })
	echo!("second: ${Str.inspect(pet)} ${Str.inspect({ p: pet })}\n")
	Ok({})
}
