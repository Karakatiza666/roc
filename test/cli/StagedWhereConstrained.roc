# A `where` constrained type variable, named by the type its `Code` position
# fixed it to.
#
# A constraint is no shape of its own. The site fixes the variable the way it
# fixes any other, and the description names what it was fixed to, in a
# parameter and in a result alike; the method the body dispatches is named by
# that type too. A constrained variable no site fixes is refused as a type
# variable, which is every other polymorphic root's refusal.
Stage := {}.{
	reads : Code(Meters -> U16) -> Str
	reads = |code| Stage.node(Code.ir(code))

	builds : Code(U16 -> Meters) -> Str
	builds = |code| Stage.node(Code.ir(code))

	node : Code.Ir -> Str
	node = |ir| match ir {
		Lambda(_params, body, m) => "${m.ty.name()} { ${Stage.node(body)} }"
		Param(name, _) => name
		Lit(lit, _) => match lit {
			Int(value, _) => value.to_str()
			_ => "?"
		}
		Binop(op, lhs, rhs, _) => "(${op} ${Stage.node(lhs)} ${Stage.node(rhs)})"
		Call(callee, args, _) => "(${callee} ${Str.join_with(args.map(Stage.node), " ")})"
		_ => "?"
	}
}

Meters := { m : U16 }.{
	size : Meters -> U16
	size = |v| v.m

	wrap : U16 -> Meters
	wrap = |m| Meters.{ m }
}

## The constraint stands in the parameter, and the body dispatches on it.
doubled : a -> U16 where [a.size : a -> U16]
doubled = |v| v.size() * 2

## The constraint stands in the result. A body names a type it does not
## receive through a local alias for the variable.
built : U16 -> a where [a.wrap : U16 -> a]
built = |x| {
	A : a
	A.wrap(x)
}

taken : Str
taken = Stage.reads(doubled)

made : Str
made = Stage.builds(built)

main! = |_args| {
	echo!("taken: ${taken}\n")
	echo!("made: ${made}\n")
	Ok({})
}
