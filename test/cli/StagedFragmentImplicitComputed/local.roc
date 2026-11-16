# A method bound to a computed callable of this module, whose closure holds
# a Code site at a variable the binding leaves free (Q17 of
# roc-reify-structural-proposal.md). The compiler calls `to_inspect` with
# no written use. Each type occurrence of the owner describes the method at
# that type, and gives the binding's entry wrapper that table. A written
# call of the closure is described as usual.
import Db

## A closure that holds a Code site at this function's own variable `a`.
make : {} -> (a -> Str)
make = |{}| |x| Db.of(x).filter(|_y| Bool.True).show()

Par(r) := { row : r }.{
	to_inspect = make({})
}

main! = |_args| {
	par : Par(Str)
	par = Par.({ row: "x" })
	echo!("direct: ${make({})(par)}\n")
	echo!("inspect: ${Str.inspect(par)}\n")
	pet : Par({ id : U8 })
	pet = Par.({ row: { id: 1 } })
	echo!("second: ${Str.inspect(pet)} ${Str.inspect({ p: pet })}\n")
	Ok({})
}
