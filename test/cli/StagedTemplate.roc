# A function that returns a `Code` is a template: the compiler calls it, writes
# the call's arguments into the description, and the call site takes what that
# produces. One template written once describes a different body per call.

Stage := {}.{
	## The staged body, printed as an s-expression with its literals in place.
	render : Code(f) -> Str
	render = |code| Stage.node(Code.ir(code))

	node : Code.Ir -> Str
	node = |ir| match ir {
		Lambda(params, body, _) => "(fn ${Str.join_with(params.map(|p| p.name), " ")} ${Stage.node(body)})"
		Param(name, _) => name
		Lit(lit, _) => match lit {
			Int(value, _) => value.to_str()
			Frac(value, _) => value.to_str()
			Fixed(value) => value.to_str()
			Bool(value) => if value "True" else "False"
			Str(value) => "\"${value}\""
			Bytes(bytes) => "bytes(${bytes.len().to_str()})"
		}
		Binop(op, lhs, rhs, _) => "(${op} ${Stage.node(lhs)} ${Stage.node(rhs)})"
		Field(receiver, name, _) => "(. ${Stage.node(receiver)} ${name})"
		If(cond, then, else_, _) => "(if ${Stage.node(cond)} ${Stage.node(then)} ${Stage.node(else_)})"
		_ => "?"
	}
}

Entity : { hp : I32, name : Str }

## Everything below the threshold, named for whoever reads the message.
weaker_than : I32, Str -> Code(Entity -> Str)
weaker_than = |threshold, label| |e| if e.hp < threshold label else e.name

main! = |_args| {
	echo!("${Stage.render(weaker_than(10, "weak"))}\n")
	echo!("${Stage.render(weaker_than(99, "doomed"))}\n")
	Ok({})
}
