# A template whose argument is a function.
#
# The `Ir` is first order, so a function argument has no node: the template's
# parameter binds to the definition the argument names, and a call on the
# parameter names that definition's row.
Stage := {}.{
	render : Code(U16 -> U16) -> Str
	render = |code| Stage.describe(Code.definitions(code), Code.ir(code))

	describe : List(Code.Def), Code.Ir -> Str
	describe = |defs, root| {
		rows = defs.map(|d| "${d.name} = ${Stage.node(d.ir)} ; ")
		"${Str.join_with(rows, "")}${Stage.node(root)}"
	}

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
		_ => "?"
	}
}

twice : (U16 -> U16) -> Code(U16 -> U16)
twice = |g| |x| g(g(x))

inc : U16 -> U16
inc = |n| n + 1

named : Str
named = Stage.render(twice(inc))

## A lambda written as the argument takes a row of its own.
written : Str
written = Stage.render(twice(|y| y * 3))

## What a lambda argument reads from the block around it is bound at the head
## of its row.
captured : Str
captured = {
	step : U16
	step = 5
	Stage.render(twice(|y| y + step))
}

## A function a block binds takes a row the same way. A call lifts the same
## lambda into a row that takes what it captured as a parameter, so the two
## describe as two rows.
block_bound : Str
block_bound = {
	k : U16
	k = 2
	bump = |n| n + k
	called = Stage.render(|x| bump(x))
	passed = Stage.render(twice(bump))
	"${called} | ${passed}"
}

## A generic function describes at the type the template's parameter fixes.
same : a -> a
same = |v| v

generic : Str
generic = Stage.render(twice(same))

main! = |_args| {
	echo!("named: ${named}\n")
	echo!("written: ${written}\n")
	echo!("captured: ${captured}\n")
	echo!("block bound: ${block_bound}\n")
	echo!("generic: ${generic}\n")
	Ok({})
}
