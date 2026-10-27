# The laws of the builtins (layer L) at a `Code.Lawful(f)` site.
#
# A `Code.Lawful(f)` site holds the `graph` view normalized with the laws of
# normal-form 3.16 as well, so a loop and the builtin it means are one value:
# a loop that appends to an empty list is `List.map`, one that appends its
# element under a test is `List.keep_if`, a `List.fold` of a known function
# is the loop that calls it, a `map` of a `map` is one `map`, and a length
# compared with 0 is `is_empty`. A `Code(f)` site keeps each form as written.
Stage := {}.{
	of_graph : Code(f) -> Str
	of_graph = |code| Stage.describe(Code.graph(code))

	lawful : Code.Lawful(f) -> Str
	lawful = |code| Stage.describe(code.graph())

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
		Prim(p) => "${p.owner}.${p.method}(${Stage.all(args)})"
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

	lit : Code.Lit -> Str
	lit = |value| match value {
		Bool(flag) => if flag "True" else "False"
		Int(number, _) => number.to_str()
		Frac(number, _) => number.to_str()
		Fixed(number) => number.to_str()
		Str(text) => "'${text}'"
		Bytes(bytes) => "bytes[${Str.join_with(bytes.map(|b| b.to_str()), " ")}]"
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

looped : List(U64) -> List(U64)
looped = |xs| {
	var $out = []
	for x in xs {
		$out = $out.append(x + 1)
	}
	$out
}

mapped : List(U64) -> List(U64)
mapped = |xs| xs.map(|x| x + 1)

kept_by_loop : List(U64) -> List(U64)
kept_by_loop = |xs| {
	var $out = []
	for x in xs {
		if x > 3 {
			$out = $out.append(x)
		}
	}
	$out
}

kept : List(U64) -> List(U64)
kept = |xs| xs.keep_if(|x| x > 3)

folded : List(U64) -> U64
folded = |xs| xs.fold(0, |s, x| s + x * 2)

summed_by_loop : List(U64) -> U64
summed_by_loop = |xs| {
	var $s = 0
	for x in xs {
		$s = $s + x * 2
	}
	$s
}

two_maps : List(U64) -> List(U64)
two_maps = |xs| xs.map(|x| x + 1).map(|y| y * 3)

one_map : List(U64) -> List(U64)
one_map = |xs| xs.map(|x| (x + 1) * 3)

collected : List(U64) -> List(U64)
collected = |xs| xs.iter().map(|x| x + 1).collect()

has_items : List(U64) -> Bool
has_items = |xs| xs.len() > 0

not_empty : List(U64) -> Bool
not_empty = |xs| !xs.is_empty()

Laws :: {}.{
	same : Code.Lawful(f), Code.Lawful(f) -> Bool
	same = |a, b| a == b
}

main! = |_args| {
	echo!("graph: ${Stage.of_graph(looped)}\n")
	echo!("lawful: ${Stage.lawful(looped)}\n")
	echo!("keep_if: ${Stage.lawful(kept_by_loop)}\n")
	echo!("fold: ${Stage.lawful(folded)}\n")
	echo!("fused: ${Stage.lawful(two_maps)}\n")
	echo!("collect: ${Stage.lawful(collected)}\n")
	echo!("len: ${Stage.lawful(has_items)}\n")
	echo!("map same: ${Str.inspect(Laws.same(looped, mapped))}\n")
	echo!("keep_if same: ${Str.inspect(Laws.same(kept_by_loop, kept))}\n")
	echo!("fold same: ${Str.inspect(Laws.same(folded, summed_by_loop))}\n")
	echo!("fused same: ${Str.inspect(Laws.same(two_maps, one_map))}\n")
	echo!("collect same: ${Str.inspect(Laws.same(collected, mapped))}\n")
	echo!("len same: ${Str.inspect(Laws.same(has_items, not_empty))}\n")
	Ok({})
}
