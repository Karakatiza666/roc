# A function bound inside a block, named where a `Code` is expected.
#
# The name leads to the lambda its statement binds, and the lambda describes
# the way one written at the site does: what it reads from the block around it
# is bound at the head of its body. A block generalizes a lambda that captures
# nothing, and each site describes it at the type that site fixes, the way a
# generic top-level function describes.
Stage := {}.{
	render : Code(U16 -> U16) -> Str
	render = |code| Stage.describe(Code.definitions(code), Code.ir(code))

	render_str : Code(Str -> Str) -> Str
	render_str = |code| Stage.describe(Code.definitions(code), Code.ir(code))

	describe : List(Code.Def), Code.Ir -> Str
	describe = |defs, root| {
		rows = defs.map(|d| "${d.name} = ${Stage.node(d.ir)} ; ")
		"${Str.join_with(rows, "")}${Stage.node(root)}"
	}

	node : Code.Ir -> Str
	node = |ir| match ir {
		Lambda(params, body, meta) => "(fn ${Str.join_with(params.map(|p| p.name), " ")} : ${Stage.ty(meta.ty)} ${Stage.node(body)})"
		Param(name, _) => name
		Local(name, _) => name
		Let(name, value, body, _) => "(let ${name} ${Stage.node(value)} ${Stage.node(body)})"
		Lit(lit, _) => match lit {
			Int(value, _) => value.to_str()
			Str(value) => "\"${value}\""
			_ => "?"
		}
		If(cond, yes, no, _) => "(if ${Stage.node(cond)} ${Stage.node(yes)} ${Stage.node(no)})"
		Binop(op, lhs, rhs, _) => "(${op} ${Stage.node(lhs)} ${Stage.node(rhs)})"
		Call(callee, args, _) => "(call ${callee} ${Str.join_with(args.map(Stage.node), " ")})"
		_ => "?"
	}

	ty : Code.Ty -> Str
	ty = |t| match t {
		U16 => "U16"
		Str => "Str"
		Bool => "Bool"
		Fn(args, ret) => "(${Str.join_with(args.map(Stage.ty), ", ")} -> ${Stage.ty(ret)})"
		_ => "?"
	}
}

## An annotation fixes the lambda's type where the block binds it.
annotated : Str
annotated = {
	double : U16 -> U16
	double = |x| x * 2
	Stage.render(double)
}

## `add_k` captures `k`, so the description binds `k` ahead of the body.
captured : Str
captured = {
	k = 3
	add_k = |x| x + k
	Stage.render(add_k)
}

## One generalized lambda, described at each type a site fixes.
generic : Str
generic = {
	same = |x| x
	"${Stage.render(same)} / ${Stage.render_str(same)}"
}

## A generalized lambda the root calls takes a row per type a call fixes.
called : Str
called = {
	same = |y| y
	Stage.render(|x| if same(x > 1) same(x) else 0)
}

main! = |_args| {
	echo!("annotated: ${annotated}\n")
	echo!("captured: ${captured}\n")
	echo!("generic: ${generic}\n")
	echo!("called: ${called}\n")
	Ok({})
}
