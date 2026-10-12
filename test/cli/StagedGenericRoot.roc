# A generic function named where a `Code` is expected.
#
# The root of a description is walked at the types its site fixes it to, the
# same way a generic callee is walked at the types its call fixes. `twin` is
# one definition, and the two sites below describe it twice: once with `a` at
# `Str` and once with `a` at `U16`. The parameter's `Ty` and the tuple the body
# builds both follow.
Stage := {}.{
	from_str : Code(Str -> (Str, Str)) -> Str
	from_str = |code| Stage.render(Code.ir(code))

	from_u16 : Code(U16 -> (U16, U16)) -> Str
	from_u16 = |code| Stage.render(Code.ir(code))

	render : Code.Ir -> Str
	render = |ir| match ir {
		Lambda(params, body, m) =>
			"${m.ty.name()} { ${Str.join_with(params.map(|p| p.name), ", ")} => ${Stage.render(body)} }"
		MakeTuple(parts, _m) => "(${Str.join_with(parts.map(Stage.render), ", ")})"
		Param(name, m) => "${name}:${m.ty.name()}"
		_ => "?"
	}
}

twin : a -> (a, a)
twin = |x| (x, x)

staged_str : Str
staged_str = Stage.from_str(twin)

staged_u16 : Str
staged_u16 = Stage.from_u16(twin)

main! = |_args| {
	echo!("${staged_str}\n")
	echo!("${staged_u16}\n")
	Ok({})
}
