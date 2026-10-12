# Which comparison a nominal component gets: the one it writes, or the one the
# compiler derives.
#
# `==` and `.to_hash` dispatch to a nominal's own method before they look at
# the nominal's representation, and a derivation carries no dispatch plan, so
# the walk resolves the method itself. The checked method registries answer it,
# and they say which of the two it is: a written method describes as the call
# it is, with its body in the table, and a derived one expands the backing.
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

# A nominal that writes both methods.
Point := { x : U16 }.{
	is_eq : Point, Point -> Bool
	is_eq = |a, b| a.x == b.x

	to_hash : Point, Hasher -> Hasher
	to_hash = |a, h| a.x.to_hash(h)
}

# The same shape, deriving both.
Plain := { x : U16 }.{
	is_eq : _
	to_hash : _
}

# An opaque nominal that writes its own. Calling the method leaves the
# representation hidden, which is what the `Ty` of an opaque does everywhere
# else; a derived one over an opaque stays refused for the same reason.
Sealed :: { x : U16 }.{
	is_eq : Sealed, Sealed -> Bool
	is_eq = |a, b| a.x == b.x
}

# The written method is the comparison, so the description is the call to it.
written_eq : { a : Point, b : Point } -> Bool
written_eq = |r| { m: r.a } == { m: r.b }

# The derived one is the compiler's recipe, so the comparison is the backing's.
derived_eq : { a : Plain, b : Plain } -> Bool
derived_eq = |r| { m: r.a } == { m: r.b }

# `to_hash : value, Hasher -> Hasher`, so the value leads and the hasher follows.
written_hash : { p : Point, h : Hasher } -> Hasher
written_hash = |r| { m: r.p }.to_hash(r.h)

# The derived recipe feeds the hasher one component at a time.
derived_hash : { p : Plain, h : Hasher } -> Hasher
derived_hash = |r| { m: r.p }.to_hash(r.h)

# An opaque component describes as the call and nothing more.
sealed_eq : { a : Sealed, b : Sealed } -> Bool
sealed_eq = |r| { m: r.a } == { m: r.b }

# A builtin container writes its own `is_eq` like any other nominal, and the
# walk stops at a builtin's body, so the comparison is the name and nothing
# more. A translator resolves that name against what its own target provides,
# or rejects it by name.
list_eq : { a : List(U16), b : List(U16) } -> Bool
list_eq = |r| { m: r.a } == { m: r.b }

dict_eq : { a : Dict(U16, U16), b : Dict(U16, U16) } -> Bool
dict_eq = |r| { m: r.a } == { m: r.b }

try_eq : { a : Try(U16, Str), b : Try(U16, Str) } -> Bool
try_eq = |r| { m: r.a } == { m: r.b }

main! = |_args| {
	echo!("${Stage.describe(written_eq)}\n")
	echo!("${Stage.describe(derived_eq)}\n")
	echo!("${Stage.describe(written_hash)}\n")
	echo!("${Stage.describe(derived_hash)}\n")
	echo!("${Stage.describe(sealed_eq)}\n")
	echo!("${Stage.describe(list_eq)}\n")
	echo!("${Stage.describe(dict_eq)}\n")
	echo!("${Stage.describe(try_eq)}\n")
	Ok({})
}
