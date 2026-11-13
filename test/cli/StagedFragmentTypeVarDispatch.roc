# A method call inside a lambda at a `Code` position, on a type variable of
# the query fragment that holds the lambda. Each use of the fragment fixes the
# variable, and the evidence that the use supplies for the fragment's method
# requirement names the method. So the description at each use calls the
# method of the type that the use fixes.
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

Clock := { n : U64 }.{
	now : Clock -> Bool
	now = |c| c.n > 7
}

Pin := { k : U8 }.{
	is_eq : Pin, Pin -> Bool
	is_eq = |a, b| a.k == b.k + 1
}

Calendar := { day : U8 }.{
	now : Calendar -> Bool
	now = |c| c.day == 3
}

# Unannotated, so its type has `where [a.now : a -> Bool]`. A method call on
# the receiver is checked before the receiver's type is known, so the call
# names `Db.Q.filter`.
now_frag = |q| Db.Q.filter(q, |x| x.t.now())

# The same requirement, written.
now_where : Db.Q({ t : a }) -> Db.Q({ t : a }) where [a.now : a -> Bool]
now_where = |q| q.filter(|x| x.t.now())

# `==` on a type variable of the fragment: the use's evidence names the
# written `is_eq` of `Pin`, and a derived `is_eq` for a record.
eq_frag = |q| Db.Q.filter(q, |x| x.a == x.b)

# A call of a generic helper that dispatches on the fragment's variable: the
# call's evidence forwards to the fragment's evidence.
is_now = |t| t.now()
helper_frag = |q| Db.Q.filter(q, |x| is_now(x.t))

# A builtin method.
even_frag = |q| Db.Q.filter(q, |x| x.t.is_even())

# A fragment that calls a fragment, and adds a site of its own.
card = |q| Db.Q.filter(now_frag(q), |x| x.t.now() and x.u.now())

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
		Prim(p) => "${p.owner}.${p.method}(${Stage.all(args)})"
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
	clocks : Db.Q({ t : Clock })
	clocks = Db.Q.new({})
	days : Db.Q({ t : Calendar })
	days = Db.Q.new({})
	numbers : Db.Q({ t : U64 })
	numbers = Db.Q.new({})
	mixed : Db.Q({ t : Clock, u : Calendar })
	mixed = Db.Q.new({})
	echo!("unannotated clock: ${now_frag(clocks).show()}\n")
	echo!("unannotated calendar: ${now_frag(days).show()}\n")
	echo!("where clock: ${now_where(clocks).show()}\n")
	echo!("helper calendar: ${helper_frag(days).show()}\n")
	echo!("builtin: ${even_frag(numbers).show()}\n")
	pins : Db.Q({ a : Pin, b : Pin })
	pins = Db.Q.new({})
	recs : Db.Q({ a : { z : U8 }, b : { z : U8 } })
	recs = Db.Q.new({})
	echo!("eq pin: ${eq_frag(pins).show()}\n")
	echo!("eq rec: ${eq_frag(recs).show()}\n")
	echo!("card: ${card(mixed).show()}\n")
	Ok({})
}
