# An intrinsic is an annotated declaration with no body. Only reified code
# uses it, so a description names it as a `Prim`, at every site and whatever
# the site's cut says. A translator sees no difference between that `Prim`
# and any other: `Stage.op` reads every `Prim` with one closed record
# pattern, so an intrinsic's `Prim` has exactly the fields of a builtin's.
Db := {}.{
	Q(row) := { log : Str }.{
		new : {} -> Q(row)
		new = |_| Q.({ log: "" })

		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log}[${Stage.describe(code)}]" })

		show : Q(row) -> Str
		show = |q| q.log
	}
}

Text :: {}.{
	# An intrinsic function of a nominal.
	is_email : Str -> Bool
}

# An intrinsic at the top level, with a `where` clause.
similar : a, a -> Bool where [a.is_eq : a, a -> Bool]

# An intrinsic constant.
limit : U64

Clock := { n : U64 }.{
	# An intrinsic method.
	now : Clock -> Bool
}

Calendar := { day : U8 }.{
	now : Calendar -> Bool
	now = |c| c.day == 3
}

# A translator whose cut lists `Tr.twice`: a `Prim` by the cut. The cut
# does not list the intrinsic, and the intrinsic is a `Prim` all the same.
Tr := {}.{
	twice : U64 -> U64
	twice = |x| x * 2

	code_primitives = [Code.prim(Tr.twice)]

	show : Code(f) -> Str
	show = |code| Stage.describe(code)
}

# Unannotated, so its type has `where [a.now : a -> Bool]`. Each use of the
# fragment fixes the type, and the evidence of the use names the method.
now_frag = |q| Db.Q.filter(q, |x| x.t.now())

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
			if (defs.is_empty()) last else "{ ${Str.join_with(defs, "")}${last} }"
		}
	}

	all : List(Code.Tree) -> Str
	all = |ts| Str.join_with(ts.map(Stage.tree), ", ")

	op : Code.Op, List(Code.Tree) -> Str
	op = |o, args| match o {
		Lit(l) => Stage.lit(l)
		Prim({ owner, method, id: _, evidence }) => "${owner}.${method}(${Stage.all(args)})${Stage.evidence(evidence)}"
		Call(r) => "r${r.to_str()}(${Stage.all(args)})"
		Closure(r) => "closure r${r.to_str()}(${Stage.all(args)})"
		Record(names) => {
			fields = List.map2(names, args, |name, arg| "${name}: ${Stage.tree(arg)}")
			if (fields.is_empty()) "{}" else "{ ${Str.join_with(fields, ", ")} }"
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
		ForRange(r) => "for_range${if (r.inclusive) "=" else "<"}(${Stage.all(args)})"
		ForList(_) => "for_list(${Stage.all(args)})"
		Loop(_) => "loop(${Stage.all(args)})"
		Lambda(_) => "lambda(${Stage.all(args)})"
		Crash => "crash(${Stage.all(args)})"
		Derived(name, _) => "derived ${name}(${Stage.all(args)})"
	}

	evidence : List(Code.Evidence) -> Str
	evidence = |entries| if (entries.is_empty()) "" else " where [${Str.join_with(entries.map(Stage.entry), ", ")}]"

	entry : Code.Evidence -> Str
	entry = |e| {
		{ method: required, target, .. } = e
		shown = match target {
			Prim({ owner, method, id: _, evidence: _ }) => "${owner}.${method}"
			Row(r) => "r${r.to_str()}"
			Derived(name) => "derived ${name}"
			Unreachable => "unreachable"
		}
		"${required} -> ${shown}"
	}

	## The `Code.PrimId` of each `Prim` node of the root row, in node order.
	prim_ids : Code(f) -> List(Code.PrimId)
	prim_ids = |code| {
		graph = Code.graph(code)
		graph.root_row().nodes.keep_oks(|node| match node.op {
			Prim(p) => Ok(p.id)
			_ => Err(NotAPrim)
		})
	}

	lit : Code.Lit -> Str
	lit = |value| match value {
		Bool(flag) => if (flag) "True" else "False"
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

	root : Code(f) -> Str
	root = |code| {
		graph = Code.graph(code)
		Stage.tree(graph.to_tree(graph.root_row().id))
	}
}

main! = |_args| {
	people : Db.Q({ email : Str, n : U64 })
	people = Db.Q.new({})
	clocks : Db.Q({ t : Clock })
	clocks = Db.Q.new({})
	days : Db.Q({ t : Calendar })
	days = Db.Q.new({})
	echo!("call: ${people.filter(|p| Text.is_email(p.email)).show()}\n")
	echo!("where: ${people.filter(|p| similar(p.n, 3)).show()}\n")
	echo!("constant: ${people.filter(|p| p.n > limit).show()}\n")
	echo!("method: ${clocks.filter(|c| c.t.now()).show()}\n")
	echo!("fragment clock: ${now_frag(clocks).show()}\n")
	echo!("fragment calendar: ${now_frag(days).show()}\n")
	echo!("cut: ${Tr.show(|n| Tr.twice(n) > limit)}\n")
	ids = Stage.prim_ids(|s| Text.is_email(s))
	echo!("same id: ${Str.inspect(ids == [Code.prim(Text.is_email)])}\n")
	echo!("other id: ${Str.inspect(ids == [Code.prim(Tr.twice)])}\n")
	echo!("same print: ${Stage.root(|s| Text.is_email(s))} ${Stage.root(|s| Str.is_empty(s))}\n")
	Ok({})
}
