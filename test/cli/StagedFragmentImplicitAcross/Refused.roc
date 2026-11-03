# A use of a function of another module that holds a Code site, at the type
# variables of a method the compiler calls (Q17): refused at the method.
import Other

Pet : { id : Str, name : Str }

Rows(r) := { row : r }.{
	to_inspect : Rows(r) -> Str
	to_inspect = |rows| Other.render(rows)
}

main! = |_args| {
	pet = { id: "1", name: "rex" }
	rows : Rows(Pet)
	rows = Rows.({ row: pet })
	echo!("direct: ${Other.render(pet)}\n")
	echo!("inspect: ${Str.inspect(rows)}\n")
	Ok({})
}
