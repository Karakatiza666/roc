# Code sites at the type variables of methods the compiler calls with no
# written use (Q17 of roc-reify-structural-proposal.md). Str.inspect calls
# `to_inspect`, `==` calls `is_eq`, and hashing calls `to_hash`, also for a
# structure that holds the type, through a `where` clause, and inside a
# builtin. Each type occurrence of the owner describes the method at that
# type.
Db := {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} | ${Db.fields(code.graph().root_row().params)}" })

		show : Q(row) -> Str
		show = |q| q.log
	}

	from : Str -> Q(row)
	from = |name| Q.({ log: name })

	fields = |params| match params {
		[Record(fields)] => Str.join_with(fields.map(|f| "${f.name}:${Str.inspect(f.ty)}"), ",")
		_ => "other"
	}
}

Pet : { id : Str, name : Str, age : U8 }

named_only : Db.Q({ name : Str, ..r }) -> Db.Q({ name : Str, ..r })
named_only = |q| q.filter(|x| x.name != "")

Rows(r) := { q : Db.Q(r) }.{
	to_inspect : Rows(r) -> Str
	to_inspect = |rows| rows.q.filter(|_x| Bool.True).show()
}

Named(r) := { q : Db.Q(r) }.{
	is_eq : Named({ name : Str, ..r }), Named({ name : Str, ..r }) -> Bool
	is_eq = |a, b| named_only(a.q).show() == named_only(b.q).show()

	to_hash : Named({ name : Str, ..r }), Hasher -> Hasher
	to_hash = |a, hasher| named_only(a.q).show().to_hash(hasher)
}

## `Code.ty_of` at the method's own variable.
Shown(a) := { value : a }.{
	to_inspect : Shown(a) -> Str
	to_inspect = |_| {
		proxy : Code.Proxy(a)
		proxy = Code.proxy()
		Str.inspect(Code.ty_of(proxy))
	}
}

same : a, a -> Bool where [a.is_eq : a, a -> Bool]
same = |x, y| x == y

main! = |_args| {
	pets : Db.Q(Pet)
	pets = Db.from("pet")
	rows : Rows(Pet)
	rows = Rows.({ q: pets })
	named : Named(Pet)
	named = Named.({ q: pets })
	echo!("direct: ${named_only(pets).show()}\n")
	echo!("inspect: ${Str.inspect(rows)} ${Str.inspect({ r: rows })}\n")
	echo!("eq: ${Str.inspect(named == named)} ${Str.inspect({ n: named } == { n: named })} ${Str.inspect(same(named, named))} ${Str.inspect([named].contains(named))}\n")
	echo!("hash: ${Str.inspect(Set.from_list([named, named]).len())} ${Str.inspect(Set.from_list([{ n: named }]).len())}\n")
	echo!("ty_of: ${Str.inspect(Shown.({ value: 1.U8 }))} ${Str.inspect(Shown.({ value: "s" }))}\n")
	Ok({})
}
