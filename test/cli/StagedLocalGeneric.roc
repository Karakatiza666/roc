# A use of a query fragment inside a function that a block made generic. The
# local function `narrow` captures `label`, so it stays a local function, and
# its row is a type variable. The use of `named_only` inside it does not fix
# that row, so no description exists for the site.
Db := {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} | ${code.graph().root_row().params.len().to_str()}" })

		show : Q(row) -> Str
		show = |q| q.log
	}

	from : Str -> Q(row)
	from = |name| Q.({ log: name })
}

named_only : Db.Q({ name : Str, ..r }) -> Db.Q({ name : Str, ..r })
named_only = |q| Db.Q.filter(q, |x| x.name != "")

Pet : { id : Str, name : Str, age : U8 }
Owner : { id : Str, name : Str, city : Str }

report : Str -> Str
report = |label| {
	narrow = |q| named_only(q).show().concat(label)
	pets : Db.Q(Pet)
	pets = Db.from("pet")
	owners : Db.Q(Owner)
	owners = Db.from("owner")
	"${narrow(pets)} ${narrow(owners)}"
}

main! = |_args| {
	echo!("${report("!")}\n")
	Ok({})
}
