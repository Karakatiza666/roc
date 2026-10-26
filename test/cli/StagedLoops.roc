# What leaves a loop: `break`, and a `return` that crosses one.
#
# A loop body ends every path in `continue`, `break` or `return`, so a target
# with its own `break` emits one and a target that folds lowers them itself.
Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| {
		graph = Code.graph(code)
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

# `break` settles the loop at the state its `var`s have reached.
capped : List(U16) -> U16
capped = |xs| {
	var $total = 0
	for x in xs {
		if x > 5 {
			break
		}
		$total = $total + x
	}
	$total
}

# A branch that writes the state and then leaves, which is the shape Roc's own
# `List.fold_until` is written in.
until : List(U16) -> U16
until = |xs| {
	var $state = 0
	for x in xs {
		if x == 0 {
			$state = 99
			break
		}
		$state = $state + x
	}
	$state
}

# A loop that assigns no `var` carries nothing, and matters for what leaves
# it: it has no slots, and its `return` leaves the function.
find : List(U16), U16 -> [Found(U16), NotFound]
find = |xs, target| {
	for x in xs {
		if x == target {
			return Found(x)
		}
	}
	NotFound
}

# `x?` inside a loop leaves the function, so the `Err` branch is a `Return`
# where outside a loop it would be the statements written after it.
totalled : List(Try(U16, [Bad])) -> Try(U16, [Bad])
totalled = |ts| {
	var $total = 0
	for t in ts {
		h = t?
		$total = $total + h
	}
	Ok($total)
}

# Roc has no labelled `break`, so this one leaves the `while`.
nested : List(U16) -> U16
nested = |xs| {
	var $total = 0
	for x in xs {
		var $j = 0
		while $j < x {
			if $j > 3 {
				break
			}
			$j = $j + 1
		}
		$total = $total + $j
	}
	$total
}

# `while Bool.True { .. }` reaches the walk as a form of its own, and carries
# what a `while` carries.
spun : U16 -> U16
spun = |n| {
	var $i = 0
	while Bool.True {
		$i = $i + 1
		if $i > n {
			break
		}
	}
	$i
}

# A `?` written inside an expression is an exiting switch: its `Err` arm
# returns, and the expression continues in the `Ok` arm.
doubled : Try(U16, [Bad]) -> Try(U16, [Bad])
doubled = |t| Ok(t? * 2)

main! = |_args| {
	echo!("${Stage.describe(capped)}\n")
	echo!("${Stage.describe(until)}\n")
	echo!("${Stage.describe(find)}\n")
	echo!("${Stage.describe(totalled)}\n")
	echo!("${Stage.describe(nested)}\n")
	echo!("${Stage.describe(spun)}\n")
	echo!("${Stage.describe(doubled)}\n")
	Ok({})
}
