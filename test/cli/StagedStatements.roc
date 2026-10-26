# The statements a reified body can hold, and what each describes as.
#
# The normal form keeps no names and no statements: a destructuring binding is
# the reads it names, each version of a `var` is the value it holds, and a loop
# carries its state in slots from one turn to the next. A value read more than
# once stays one node.
#
# `test/cli/StagedLoops.roc` pins what leaves a loop.
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

Wrapped := [Pair(U16, U16)]

# A record pattern reads a field per name it binds.
fields : { a : U16, b : U16 } -> U16
fields = |r| {
	{ a, b } = r
	a + b
}

# A tuple pattern reads a position per name it binds, and a subject that is
# not already a name is bound once first.
positions : { pair : (U16, U16) } -> U16
positions = |r| {
	(a, b) = r.pair
	a + b
}

# A pattern that names a variant is a test as well as a binding, so it stays
# the `match` it is.
variant : Wrapped -> U16
variant = |w| {
	Pair(a, b) = w
	a + b
}

# A branch that returns early takes everything after it as its alternative.
early : U16 -> U16
early = |n| {
	if n > 10 {
		return 0
	}
	n + 1
}

# `x?` is the same rewrite around a binding: the `Err` branch returns, and the
# `Ok` branch has the value the binding holds.
forwarded : Try(U16, [Odd]) -> Try(U16, [Odd])
forwarded = |t| {
	h = t?
	Ok(h + 1)
}

# An `expect` asserts and hands back nothing, so the description passes over it.
asserted : U16 -> U16
asserted = |n| {
	expect n > 0
	n + 1
}

# Each assignment to a `var` binds a version of its own.
versions : U16 -> U16
versions = |n| {
	var $x = n
	$x = $x + 1
	$x = $x * 2
	$x
}

# A `var` written in one branch and read after it needs a join, which is the
# `if` hoisted into the binding.
joined : U16 -> U16
joined = |n| {
	var $x = n
	if n > 10 {
		$x = 0
	}
	$x
}

# Two `var`s travel together as a tuple, because one `If` per `var` would
# describe each branch once per `var`.
paired : U16 -> U16
paired = |n| {
	var $x = n
	var $y = 1
	if n > 10 {
		$x = 0
		$y = 2
	} else {
		$y = 3
	}
	$x + $y
}

# A loop is the fold it is: the state it carries is the `var` its body writes.
summed : List(U16) -> U16
summed = |xs| {
	var $total = 0
	for x in xs {
		$total = $total + x
	}
	$total
}

# A range reaches the walk as the call the checker resolves it to, and
# describes as the two ends it was written as.
counted : U16 -> U16
counted = |n| {
	var $total = 0
	for i in 0..<n {
		$total = $total + i
	}
	$total
}

# A `while` carries the same state, and its condition reads it too.
walked : U16 -> U16
walked = |n| {
	var $i = 0
	while $i < n {
		$i = $i + 1
	}
	$i
}

# A statement whose value is discarded is a binding nothing reads, which keeps
# its order and whatever it diverges on.
sequenced : U16 -> U16
sequenced = |n| {
	_ = n + 1
	n * 2
}

main! = |_args| {
	echo!("${Stage.describe(fields)}\n")
	echo!("${Stage.describe(positions)}\n")
	echo!("${Stage.describe(variant)}\n")
	echo!("${Stage.describe(early)}\n")
	echo!("${Stage.describe(forwarded)}\n")
	echo!("${Stage.describe(asserted)}\n")
	echo!("${Stage.describe(versions)}\n")
	echo!("${Stage.describe(joined)}\n")
	echo!("${Stage.describe(paired)}\n")
	echo!("${Stage.describe(summed)}\n")
	echo!("${Stage.describe(counted)}\n")
	echo!("${Stage.describe(walked)}\n")
	echo!("${Stage.describe(sequenced)}\n")
	Ok({})
}
