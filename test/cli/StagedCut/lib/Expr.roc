# A translator in a package of its own: a reified function in, one expression
# out. Its cut is `Expr.clamp`, so a call of `clamp` reaches it as a `Prim`
# named `Expr` and `clamp`. Every other function a site calls, `Expr.twice`
# and `Expr.norm` among them, reaches it as its body.
Expr :: {}.{
	code_primitives = (Expr.clamp)

	clamp : F64 -> F64
	clamp = |x| if (x < 0.0) 0.0 else x

	twice : F64 -> F64
	twice = |x| x * 2.0

	norm : F64 -> F64
	norm = |x| x.sqrt()

	## The function as an expression, or why it has none.
	to_text : Code(f) -> Str
	to_text = |code| {
		row = code.graph().root_row()
		match Expr.root_text(row) {
			Ok(text) => text
			Err({ why, .. }) => "no expression: ${why}"
		}
	}

	## The same, but a node with no form stops the build at its source.
	to_text_or_stop : Code(f) -> Str
	to_text_or_stop = |code| {
		row = code.graph().root_row()
		match Expr.root_text(row) {
			Ok(text) => text
			Err({ node, why }) => code.refuse_at({ row: row.id, node }, why)
		}
	}

	root_text : Code.Row -> Try(Str, { node : U32, why : Str })
	root_text = |row| match row.body.end {
		Value([result]) => Expr.val_text(row, result)
		_ => Err({ node: 0, why: "this body is more than one value" })
	}

	val_text : Code.Row, Code.Val -> Try(Str, { node : U32, why : Str })
	val_text = |row, val| match val {
		Param(k) => Ok("p${k.to_str()}")
		Node(index) => Expr.node_text(row, index)
		_ => Err({ node: 0, why: "this value has no form" })
	}

	node_text : Code.Row, U32 -> Try(Str, { node : U32, why : Str })
	node_text = |row, index| {
		node = row.node(index)
		match node.op {
			Lit(Frac(x, _)) => Ok(x.to_str())
			Prim({ owner, method }) =>
				match (owner, Expr.symbol(method), node.args) {
					("Expr", _, [only]) => Ok("Expr.${method}(${Expr.val_text(row, only)?})")
					(_, Ok(symbol), [left, right]) => Ok("(${Expr.val_text(row, left)?} ${symbol} ${Expr.val_text(row, right)?})")
					_ => Err({ node: index, why: "`${method}` has no form here" })
				}
			_ => Err({ node: index, why: "this node has no form here" })
		}
	}

	symbol : Str -> Try(Str, [NoOperator])
	symbol = |method| match method {
		"plus" => Ok("+")
		"times" => Ok("*")
		_ => Err(NoOperator)
	}
}
