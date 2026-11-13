# Rows a `Prim`'s evidence names (D7 of roc-reify-opaque-proposal.md) in the
# three views. A row that evidence names is a row of the site in every view
# (roc-reify-normal-form.md section 10, `Prim.evidence`).
# `Qt.order_relative_to` reads `b` before `a`, so N8f renumbers its row, and
# the evidence of `List.sort` names a convention row that keeps the method's
# order and calls the renumbered one.
# The direct call `a.order_relative_to(b)` names the renumbered row, so in
# `graph` and `outline` both rows stay. Two sorts at one type name one row.
# The written `is_eq` of the recursive `Tree` names its own row through the
# evidence of `List.is_eq`.
Stage := {}.{
	of_graph : Code(f) -> Str
	of_graph = |code| Stage.describe(Code.graph(code))

	inlined : Code.Inlined(f) -> Str
	inlined = |code| Stage.describe(code.inline())

	outlined : Code.Outlined(f) -> Str
	outlined = |code| Stage.describe(code.outline())

	describe : Code.Graph -> Str
	describe = |graph| {
		first = graph.root_row()
		others = graph.rows().keep_if(|other| other.id != first.id)
		shown = [first].concat(others).map(|each| "r${each.id.to_str()} = ${Stage.row(graph, each)}")
		Str.join_with(shown, " ; ")
	}

	row : Code.Graph, Code.Row -> Str
	row = |graph, described| {
		params = Str.join_with(described.params.map(|param| param.name()), ", ")
		"|${params}| -> ${described.result.name()} ${Stage.tree(graph.to_tree(described.id))}"
	}

	tree : Code.Tree -> Str
	tree = |t| match t {
		Op(o) => Stage.op(o.op, o.args)
		Param(k) => "p${k.to_str()}"
		Input(k) => "in${k.to_str()}"
		Arg(a) => "s${a.owner.to_str()}.${a.k.to_str()}"
		Out(o) => "n${o.node.to_str()}.${o.k.to_str()}"
		Def(n) => "n${n.to_str()}"
		Block(b) => {
			defs = b.defs.map(|d| "n${d.id.to_str()} = ${Stage.tree(d.value)}; ")
			last = match b.end {
				Value(vals) => Stage.all(vals)
				Jump(j) => "jump j${j.join.to_str()}(${Stage.all(j.args)})"
				Return(v) => "return ${Stage.tree(v)}"
				Continue(vals) => "continue(${Stage.all(vals)})"
				Break(vals) => "break(${Stage.all(vals)})"
				Branch(sw) => Stage.tree(sw)
			}
			if defs.is_empty() last else "{ ${Str.join_with(defs, "")}${last} }"
		}
	}

	all : List(Code.Tree) -> Str
	all = |ts| Str.join_with(ts.map(Stage.tree), ", ")

	op : Code.Op, List(Code.Tree) -> Str
	op = |o, args| match o {
		Lit(l) => Stage.lit(l)
		Prim(p) => "${p.owner}.${p.method}(${Stage.all(args)})${Stage.ev(p.evidence)}"
		Call(r) => "r${r.to_str()}(${Stage.all(args)})"
		Closure(r) => "closure r${r.to_str()}(${Stage.all(args)})"
		Record(names) => {
			fields = List.map2(names, args, |name, arg| "${name}: ${Stage.tree(arg)}")
			if fields.is_empty() "{}" else "{ ${Str.join_with(fields, ", ")} }"
		}
		Tuple => "(${Stage.all(args)})"
		List => "[${Stage.all(args)}]"
		Tag(name) => "${name}(${Stage.all(args)})"
		Wrap(name) => "${name}.(${Stage.all(args)})"
		Unwrap => "unwrap(${Stage.all(args)})"
		Field(name) => "${Stage.all(args)}.${name}"
		Index(i) => "${Stage.all(args)}.${i.to_str()}"
		Payload(name, i) => "${Stage.all(args)}.${name}.${i.to_str()}"
		Item => "item(${Stage.all(args)})"
		OptField(name) => "${Stage.all(args)}.?${name}"
		Switch(sw) => {
			scrutinee = Stage.all(args.take_first(1))
			arms = List.map2(sw.arms, args.drop_first(1), |arm, body| "${Stage.key(arm.key)} => ${Stage.tree(body)}")
			joins = args.drop_first(1 + sw.arms.len()).map_with_index(|body, i| " j${i.to_str()}: ${Stage.tree(body)}")
			"switch ${scrutinee} { ${Str.join_with(arms, " | ")} }${Str.join_with(joins, "")}"
		}
		And(_) => "and(${Stage.all(args)})"
		Or(_) => "or(${Stage.all(args)})"
		ForRange(r) => "for_range${if r.inclusive "=" else "<"}(${Stage.all(args)})"
		ForList(_) => "for_list(${Stage.all(args)})"
		Loop(_) => "loop(${Stage.all(args)})"
		Lambda(_) => "lambda(${Stage.all(args)})"
		Crash => "crash(${Stage.all(args)})"
		Derived(name, _) => "derived ${name}(${Stage.all(args)})"
	}

	ev : List(Code.Evidence) -> Str
	ev = |es| if es.is_empty() "" else " where [${Str.join_with(es.map(|e| match e.target { Row(r) => "${e.method} -> row ${r.to_str()}" Prim(p) => "${e.method} -> ${p.owner}.${p.method}" Derived(m) => "derived ${m}" Unreachable => "unreachable" }), ", ")}]"

	lit : Code.Lit -> Str
	lit = |value| match value {
		Bool(flag) => if flag "True" else "False"
		Int(number, _) => number.to_str()
		Frac(number, _) => number.to_str()
		Fixed(number) => number.to_str()
		Str(text) => "'${text}'"
		Bytes(bytes) => "bytes[${Str.join_with(bytes.map(|b| b.to_str()), " ")}]"
		Numeral(n) => "numeral ${Str.inspect(Dec.from_numeral(n))}"
	}

	key : Code.Key -> Str
	key = |k| match k {
		Tag(name) => name
		Lit(l) => Stage.lit(l)
		Len(n) => "len ${n.to_str()}"
		AtLeast(n) => "len >= ${n.to_str()}"
		Default => "_"
	}
}

Pt := { x : I64 }.{
	order_relative_to : Pt, Pt -> [Before, Same, After]
	order_relative_to = |a, b| b.x.order_relative_to(a.x)
}

Qt := { x : I64 }.{
	order_relative_to : Qt, Qt -> [Before, Same, After]
	order_relative_to = |a, b| b.x.order_relative_to(a.x)
}

Tree := { kids : List(Tree), v : I64 }.{
	is_eq : Tree, Tree -> Bool
	is_eq = |a, b| a.v == b.v and a.kids == b.kids
}

sort_qt : List(Qt), Qt, Qt -> (List(Qt), [Before, Same, After])
sort_qt = |xs, a, b| (xs.sort(), a.order_relative_to(b))

two_sorts : List(Pt), List(Pt) -> (List(Pt), List(Pt))
two_sorts = |xs, ys| (xs.sort(), ys.sort())

holds : List(Tree), Tree -> Bool
holds = |xs, t| xs.contains(t)

main! = |_args| {
	echo!("g qt: ${Stage.of_graph(sort_qt)}\n")
	echo!("i qt: ${Stage.inlined(sort_qt)}\n")
	echo!("o qt: ${Stage.outlined(sort_qt)}\n")
	echo!("g two: ${Stage.of_graph(two_sorts)}\n")
	echo!("i two: ${Stage.inlined(two_sorts)}\n")
	echo!("o two: ${Stage.outlined(two_sorts)}\n")
	echo!("g tree: ${Stage.of_graph(holds)}\n")
	echo!("i tree: ${Stage.inlined(holds)}\n")
	echo!("o tree: ${Stage.outlined(holds)}\n")
	Ok({})
}
