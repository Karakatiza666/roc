# A method that another module binds to a computed callable whose type
# leaves a type variable open. A use in this module instantiates the
# variable, so its edge records a substitution of the scheme of the
# binding's entry wrapper. A direct dispatch and `where` evidence select it
# at two owner types.
import Par

label_of : x -> Str where [x.label : x -> Str]
label_of = |x| x.label()

main! = |_args| {
	par : Par.Par(Str)
	par = Par.Par.({ row: "x" })
	pet : Par.Par({ id : U8 })
	pet = Par.Par.({ row: { id: 1 } })
	echo!("${par.label()} ${pet.label()} ${label_of(par)} ${label_of(pet)}\n")
	Ok({})
}
