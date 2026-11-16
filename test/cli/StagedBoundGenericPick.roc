# A generic function that binds the input of a translator whose result type
# holds the function's open row (R7 of the Gap 1 design). Each closing use
# fixes the row and binds the input there.
Fmt := [Default].{
	default : () -> Fmt
	default = || Default

	encode_i64 : I64, List(U8) -> Try(List(U8), [])
	encode_i64 = |n, out| Ok(out.concat(n.to_str().to_utf8()))
}

Rendered(r) := [Rendered(Str)].{
	text : Rendered(r) -> Str
	text = |Rendered(t)| t
}

Stage := {}.{
	render : Code.Binds(Code(r -> Bool), Fmt) -> Code.Bound(Rendered(r))
	render = |code| Code.bound(code, Rendered("slots ${Code.graph(code).slots().len().to_str()} params ${Code.graph(code).root_row().params.len().to_str()}"))
}

pick : I64 -> Code.Bound(Rendered({ n : I64, ..r }))
pick = |least| Stage.render(|x| x.n > least)

main! = |_args| {
	a : Code.Bound(Rendered({ n : I64, m : I64 }))
	a = pick(1)
	b : Code.Bound(Rendered({ n : I64 }))
	b = pick(2)
	echo!("${a.value().text()} ${Str.inspect(a.inputs())}\n${b.value().text()} ${Str.inspect(b.inputs())}\n")
	Ok({})
}
