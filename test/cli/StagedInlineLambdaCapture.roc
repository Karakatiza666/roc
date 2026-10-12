# A lambda written at a `Code` position that reads the block around it.
#
# A description carries no scope, so each value the lambda reads from around
# itself is bound at the head of its body by the statement that produced it.
# A translator meets an ordinary local, and a statement the lambda does not
# read stays out of the description.
Stage := {}.{
	render : Code(U16 -> U16) -> Str
	render = |code| Stage.node(Code.ir(code))

	node : Code.Ir -> Str
	node = |ir| match ir {
		Lambda(params, body, _) => "(fn ${Str.join_with(params.map(|p| p.name), " ")} ${Stage.node(body)})"
		Param(name, _) => name
		Local(name, _) => name
		Let(name, value, body, _) => "(let ${name} ${Stage.node(value)} ${Stage.node(body)})"
		Lit(lit, _) => match lit {
			Int(value, _) => value.to_str()
			_ => "?"
		}
		Binop(op, lhs, rhs, _) => "(${op} ${Stage.node(lhs)} ${Stage.node(rhs)})"
		Call(callee, args, _) => "(call ${callee} ${Str.join_with(args.map(Stage.node), " ")})"
		MakeTuple(parts, _) => "(tuple ${Str.join_with(parts.map(Stage.node), " ")})"
		Index(receiver, at, _) => "(.${at.to_str()} ${Stage.node(receiver)})"
		_ => "?"
	}
}

triple : U16 -> U16
triple = |n| n * 3

literal : Str
literal = {
	bump : U16
	bump = 5
	Stage.render(|x| x + bump)
}

## `b` reads `a`, so `a` is bound outside it, and `_skipped` is read by nothing.
chained : Str
chained = {
	a : U16
	a = 2
	_skipped = 99
	b = a + 1
	Stage.render(|x| x * b + a)
}

called : Str
called = {
	k = triple(4)
	Stage.render(|x| x + k)
}

## A destructuring binding replays as the one statement it was written as.
destructured : Str
destructured = {
	(p, q) = (3, 4)
	Stage.render(|x| x + p * q)
}

## A function the block binds is lifted into a row, and what it captures is
## passed to it first.
lifted : Str
lifted = {
	step = 7
	add_step = |y| y + step
	Stage.render(|x| add_step(x))
}

nested : Str
nested = {
	outer : U16
	outer = 1
	inner = {
		deep = outer + 1
		Stage.render(|x| x + deep + outer)
	}
	inner
}

main! = |_args| {
	echo!("literal: ${literal}\n")
	echo!("chained: ${chained}\n")
	echo!("called: ${called}\n")
	echo!("destructured: ${destructured}\n")
	echo!("lifted: ${lifted}\n")
	echo!("nested: ${nested}\n")
	Ok({})
}
