# Node identities in the `inline` view (V5a).
#
# `inline_digest` names a node by its content. Two spellings of one function
# that meet in `inline` give each node one digest, and a change to what a node
# computes changes its digest and the digest of every node that reads it.
Stage := {}.{
	## The digest of every node of the root row, in node order.
	digests : Code.Inlined(U16 -> U16) -> List(U128)
	digests = |code| {
		root = code.inline().root_row()
		root.nodes.map_with_index(|_, node| code.inline_digest({ row: root.id, node: node.to_u32_wrap() }).to_u128())
	}

	## The digest of the node the root returns, which is its last node.
	result : Code.Inlined(U16 -> U16) -> U128
	result = |code| Stage.digests(code).last().ok_or(0)
}

step : U16 -> U16
step = |x| x * 3 + 1

## `step` is called twice, so `graph` keeps it as a row and `inline` inlines it.
written : U16 -> U16
written = |x| step(x) + step(x + 7)

spelled_out : U16 -> U16
spelled_out = |x| (x * 3 + 1) + ((x + 7) * 3 + 1)

renamed : U16 -> U16
renamed = |value| {
	a = value
	b = a + 7
	(a * 3 + 1) + (b * 3 + 1)
}

other_constant : U16 -> U16
other_constant = |x| step(x) + step(x + 8)

other_helper : U16 -> U16
other_helper = |x| step(x) + (x + 7) * 3 + 2

main! = |_args| {
	echo!("same: ${Str.inspect(Stage.digests(written) == Stage.digests(spelled_out))}\n")
	echo!("renamed: ${Str.inspect(Stage.digests(written) == Stage.digests(renamed))}\n")
	echo!("constant: ${Str.inspect(Stage.result(written) != Stage.result(other_constant))}\n")
	echo!("helper: ${Str.inspect(Stage.result(written) != Stage.result(other_helper))}\n")
	echo!("shared: ${Str.inspect(Stage.digests(written).first() == Stage.digests(other_constant).first())}\n")
	Ok({})
}
