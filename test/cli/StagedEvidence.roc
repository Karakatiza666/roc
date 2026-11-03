# Which method answers each `where` requirement of a primitive's call (D7 of
# roc-reify-opaque-proposal.md). `List.sort` over `I64` and over a type whose
# written order is reversed are two descriptions: the second names the order
# as a row of the graph. `Dict.get` lists `is_eq` and then `to_hash`, the
# order of its `where` clause. A recursive type's written `is_eq` that compares
# its children with `List.is_eq` names its own row in that call's evidence.
# A `==` the compiler derives for a record reaches `List.is_eq`, `Dict.is_eq`
# or `Try.is_eq` with no planned call: the element type the receiver fixes
# answers each requirement through the method registry.
Show := {}.{
	evidence : Code(f) -> Str
	evidence = |code| {
		graph = Code.graph(code)
		rows = graph.rows().map(|row| Str.join_with(row.nodes.map(|node| Show.node(row.id, node.op)).keep_if(|text| !text.is_empty()), "; "))
		"rows ${graph.rows().len().to_str()}: ${Str.join_with(rows.keep_if(|text| !text.is_empty()), "; ")}"
	}

	node : U32, Code.Op -> Str
	node = |row, op| match op {
		Prim(p) => if p.evidence.is_empty() "" else "r${row.to_str()} ${p.owner}.${p.method} ${Show.list(p.evidence)}"
		_ => ""
	}

	list : List(Code.Evidence) -> Str
	list = |entries| "[${Str.join_with(entries.map(Show.one), ", ")}]"

	one : Code.Evidence -> Str
	one = |entry| {
		target = match entry.target {
			Prim(p) => if p.evidence.is_empty() "${p.owner}.${p.method}" else "${p.owner}.${p.method} ${Show.list(p.evidence)}"
			Row(r) => "row ${r.to_str()}"
			Derived(m) => "derived ${m}"
			Unreachable => "unreachable"
		}
		"${entry.method} @ ${entry.ty.name()} -> ${target}"
	}
}

# A transparent nominal whose written order is the reverse of its field's.
Pt := { x : I64 }.{
	order_relative_to : Pt, Pt -> [Before, Same, After]
	order_relative_to = |a, b| b.x.order_relative_to(a.x)
}

# A recursive nominal whose written `is_eq` compares its children.
Tree := { kids : List(Tree), v : I64 }.{
	is_eq : Tree, Tree -> Bool
	is_eq = |a, b| a.v == b.v and a.kids == b.kids
}

holds : List(Tree), Tree -> Bool
holds = |xs, t| xs.contains(t)

sort_i64 : List(I64) -> List(I64)
sort_i64 = |xs| xs.sort()

sort_pt : List(Pt) -> List(Pt)
sort_pt = |xs| xs.sort()

# A generic helper forwards its caller's order to `List.sort`.
sorted : List(a) -> List(a) where [a.order_relative_to : a, a -> [Before, Same, After]]
sorted = |xs| xs.sort()

sort_pt_helper : List(Pt) -> List(Pt)
sort_pt_helper = |xs| sorted(xs)

get_str : Dict(Str, I64), Str -> I64
get_str = |d, k| d.get(k) ?? 0

list_eq : { a : List(U16), b : List(U16) } -> Bool
list_eq = |r| { m: r.a } == { m: r.b }

dict_eq : { a : Dict(U16, Str), b : Dict(U16, Str) } -> Bool
dict_eq = |r| { m: r.a } == { m: r.b }

try_eq : { a : Try(U16, Str), b : Try(U16, Str) } -> Bool
try_eq = |r| { m: r.a } == { m: r.b }

nested_eq : { a : List({ tags : List(Str) }), b : List({ tags : List(Str) }) } -> Bool
nested_eq = |r| { m: r.a } == { m: r.b }

trees_eq : { a : List(List(Tree)), b : List(List(Tree)) } -> Bool
trees_eq = |r| { m: r.a } == { m: r.b }

main! = |_args| {
	echo!("${Show.evidence(sort_i64)}\n")
	echo!("${Show.evidence(sort_pt)}\n")
	echo!("helper ${Show.evidence(sort_pt_helper)}\n")
	echo!("${Show.evidence(get_str)}\n")
	echo!("${Show.evidence(holds)}\n")
	echo!("${Show.evidence(list_eq)}\n")
	echo!("${Show.evidence(dict_eq)}\n")
	echo!("${Show.evidence(try_eq)}\n")
	echo!("${Show.evidence(nested_eq)}\n")
	echo!("${Show.evidence(trees_eq)}\n")
	Ok({})
}
