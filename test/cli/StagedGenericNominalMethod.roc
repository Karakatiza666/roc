# Which instantiation a generic nominal's own method describes at.
#
# A derivation reaches the method with no call site, so no dispatch edge says
# what the method's quantified variables stand for. The receiver says it: the
# method's first parameter is the value being compared or hashed, and pairing
# that parameter with the value's own type binds what the scheme quantifies.
# So `Deep(U16)` and `Deep(Str)` take a row each, and each call names its own.
Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| {
		rows = Code.definitions(code).map(|d| "${d.name} = ${Stage.node(d.ir)}")
		"${Str.join_with(rows, " ; ")} || ${Stage.node(Code.ir(code))}"
	}

	node : Code.Ir -> Str
	node = |ir| match ir {
		Lambda(_, body, _) => "fn(${Stage.node(body)})"
		Param(name, _) => name
		Local(name, _) => name
		Field(record, name, _) => "${Stage.node(record)}.${name}"
		Binop(op, lhs, rhs, _) => "(${Stage.node(lhs)} ${op} ${Stage.node(rhs)})"
		Call(name, args, _) => "${name}(${Str.join_with(args.map(Stage.node), ", ")})"
		MakeRecord(fields, _) => "{${Str.join_with(fields.map(Stage.field), ", ")}}"
		Lit(_, _) => "lit"
		_ => "other"
	}

	field : { name : Str, value : Code.Ir } -> Str
	field = |f| "${f.name}: ${Stage.node(f.value)}"
}

# A generic nominal writing both methods over its quantified field.
Deep(a) := { v : a }.{
	is_eq : Deep(a), Deep(a) -> Bool where [a.is_eq : a, a -> Bool]
	is_eq = |x, y| x.v == y.v

	to_hash : Deep(a), Hasher -> Hasher where [a.to_hash : a, Hasher -> Hasher]
	to_hash = |x, h| x.v.to_hash(h)
}

# One description over both instantiations. The bodies differ by the width each
# one feeds the hasher, so a row described at the wrong instantiation shows.
both_hash : { p : Deep(U16), q : Deep(Str), h : Hasher } -> Hasher
both_hash = |r| { m: r.q }.to_hash({ m: r.p }.to_hash(r.h))

# The comparison the nominal writes, at the instantiation this one fixes.
eq_str : { a : Deep(Str), b : Deep(Str) } -> Bool
eq_str = |r| { m: r.a } == { m: r.b }

main! = |_args| {
	echo!("${Stage.describe(both_hash)}\n")
	echo!("${Stage.describe(eq_str)}\n")
	Ok({})
}
