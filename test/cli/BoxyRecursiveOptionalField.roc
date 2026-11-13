# An optional field of a recursive nominal type, in a record that is the
# nominal's backing and in a record that is a tag payload. Both lowerings run
# it; Boxy once crashed here (beginPlannedTagVariant).
Tree := { label : Str, kids : List(Tree), note ?: Str }

Branch := [Leaf, Node({ left : Branch, right : Branch, tag ?: Str })]

count : Tree -> U64
count = |t| t.kids.fold(1, |acc, k| acc + count(k))

depth : Branch -> U64
depth = |b| match b {
	Leaf => 0
	Node(n) => {
		l = depth(n.left)
		r = depth(n.right)
		1 + (if l > r l else r)
	}
}

tags : Branch -> Str
tags = |b| match b {
	Leaf => ""
	Node(n) => "${n.?tag ?? "_"}${tags(n.left)}${tags(n.right)}"
}

main! = |_args| {
	leaf : Tree
	leaf = { label: "leaf", kids: [] }
	root : Tree
	root = { label: "root", kids: [leaf, leaf], note: "top" }
	echo!("count: ${count(root).to_str()} note: ${root.?note ?? "-"} leaf: ${leaf.?note ?? "-"}\n")
	b : Branch
	b = Node({ left: Leaf, right: Node({ left: Leaf, right: Leaf, tag: "x" }) })
	echo!("depth: ${depth(b).to_str()} tags: ${tags(b)}\n")
	Ok({})
}
