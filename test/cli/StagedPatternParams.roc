# A reified lambda's parameters may be patterns.
#
# A pattern parameter takes its argument apart the way a destructuring binding
# does: the parameter goes by a name of its own and the pattern's reads wrap
# the body. `_` binds nothing, so it reads nothing. A lambda passed inside the
# body is lifted into a row named after the first name its patterns bind.
Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| Stage.node(code.ir())

	rows : Code(f) -> Str
	rows = |code| Str.join_with(code.definitions().map(|def| "${def.name} = ${Stage.node(def.ir)}"), " ; ")

	pair : Code((U16, U16) -> U16) -> Str
	pair = |code| Stage.node(code.ir())

	node : Code.Ir -> Str
	node = |ir| match ir {
		Lit(Int(n, _), _) => n.to_str()
		Lambda(params, body, _) => "|${Str.join_with(params.map(|p| p.name), ", ")}| ${Stage.node(body)}"
		Param(name, _) => name
		Local(name, _) => name
		Let(name, bound, rest, _) => "let ${name} = ${Stage.node(bound)}; ${Stage.node(rest)}"
		Field(record, name, _) => "${Stage.node(record)}.${name}"
		Index(tuple, at, _) => "${Stage.node(tuple)}.${at.to_str()}"
		Binop(op, lhs, rhs, _) => "(${Stage.node(lhs)} ${op} ${Stage.node(rhs)})"
		Call(callee, args, _) => "${callee}(${Str.join_with(args.map(Stage.node), ", ")})"
		Match(subject, _, _) => "match ${Stage.node(subject)}"
		_ => "other"
	}
}

Wrapped := [Pair(U16, U16)]

nested : ((U16, U16), U16) -> U16
nested = |((a, _), c)| a + c

skipped : U16, U16 -> U16
skipped = |_, b| b

fields : { a : U16, b : U16 } -> U16
fields = |{ a, b }| a + b

variant : Wrapped -> U16
variant = |Pair(a, b)| a + b

firsts : List((U16, U16)) -> List(U16)
firsts = |pairs| pairs.map(|(a, _)| a)

apply : (U16, U16), ((U16, U16) -> U16) -> U16
apply = |pair, f| f(pair)

lifted : (U16, U16) -> U16
lifted = |pair| apply(pair, |(a, _)| a)

ignored : (U16, U16) -> U16
ignored = |pair| apply(pair, |_| 0)

main! = |_args| {
	echo!("${Stage.describe(nested)}\n")
	echo!("${Stage.describe(skipped)}\n")
	echo!("${Stage.describe(fields)}\n")
	echo!("${Stage.describe(variant)}\n")
	echo!("${Stage.describe(firsts)}\n")
	echo!("${Stage.rows(lifted)}\n")
	echo!("${Stage.rows(ignored)}\n")
	echo!("${Stage.pair(|(x, y)| x * y + 1)}\n")
	Ok({})
}
