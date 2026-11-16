# A generic `:=` nominal that extends its argument, read through a function
# whose argument is an open record row. Both lowerings run it; Boxy once
# crashed here ("record descriptor had non-struct payload layout").
Ref(r) := { id : Str, ..r }

name : Ref({ name : Str, ..o }) -> Str
name = |o| "${o.id} ${o.name}"

main! = |_args| {
	echo!("${name(Ref.({ id: "1", name: "Ada" }))}\n")
	echo!("${name(Ref.({ id: "2", name: "Bob", age: 3 }))}\n")
	Ok({})
}
