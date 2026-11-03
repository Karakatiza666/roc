# The smallest useful translator: a reified Roc function in, one arithmetic
# expression out. It runs while the compiler runs, and it is ordinary Roc.
Calc :: {}.{

	## The function as an expression. `p0` is its first parameter, `p1` its second.
	## A node with no form here is an `Err` that names it.
	to_expr : Code(f) -> Try(Str, [Unsupported(Str)])
	to_expr = |code| {
		row = code.graph().root_row()
		text = Calc.root_text(row)
		match text {
			Ok(expr) => Ok(expr)
			Err({ why, .. }) => Err(Unsupported(why))
		}
	}

	## The same translation, but a node with no form stops the build. The
	## compiler reports the reason at the line of the source the node came from.
	to_expr_or_stop : Code(f) -> Str
	to_expr_or_stop = |code| {
		row = code.graph().root_row()
		match Calc.root_text(row) {
			Ok(expr) => expr
			Err({ node, why }) => code.refuse_at({ row: row.id, node }, why)
		}
	}

	# The root row's body is one value. A node is read by its index in `row.nodes`.
	root_text : Code.Row -> Try(Str, { node : U32, why : Str })
	root_text = |row| match row.body.end {
		Value([result]) => Calc.val_text(row, result)
		_ => Err({ node: 0, why: "this body is more than one value" })
	}

	val_text : Code.Row, Code.Val -> Try(Str, { node : U32, why : Str })
	val_text = |row, val| match val {
		Param(k) => Ok("p${k.to_str()}")
		Node(index) => Calc.node_text(row, index)
		_ => Err({ node: 0, why: "this value has no form" })
	}

	node_text : Code.Row, U32 -> Try(Str, { node : U32, why : Str })
	node_text = |row, index| {
		node = row.node(index)
		match node.op {
			Lit(Int(n, _)) => Ok(n.to_str())
			Lit(Frac(x, _)) => Ok(x.to_str())
			Prim({ method, .. }) => match (Calc.symbol(method), node.args) {
				(Ok(symbol), [left, right]) => Ok("(${Calc.val_text(row, left)?} ${symbol} ${Calc.val_text(row, right)?})")
				_ => Err({ node: index, why: "`${method}` has no operator here" })
			}
			_ => Err({ node: index, why: "this node has no form here" })
		}
	}

	symbol : Str -> Try(Str, [NoOperator])
	symbol = |method| match method {
		"plus" => Ok("+")
		"minus" => Ok("-")
		"times" => Ok("*")
		_ => Err(NoOperator)
	}
}
