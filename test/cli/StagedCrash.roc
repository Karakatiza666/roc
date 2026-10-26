# `crash` in a reified body, both with a plain message and an interpolated one.
#
# A `match` over a closed union needs a way to say "this branch cannot happen",
# and a target whose own `switch` is not exhaustive needs that branch written.
# The message is a value rather than a `Str`, so an interpolated one arrives as
# the concatenation the checker made of it.
StagedCrash := {}.{
	describe : Code(f) -> Str
	describe = |code| {
		graph = Code.graph(code)
		first = graph.root_row()
		others = graph.rows().keep_if(|other| other.id != first.id)
		shown = [first].concat(others).map(|each| "r${each.id.to_str()} = ${StagedCrash.row(graph, each)}")
		Str.join_with(shown, " ; ")
	}

	row : Code.Graph, Code.Row -> Str
	row = |graph, described| {
		params = Str.join_with(described.params.map(|param| param.name()), ", ")
		"|${params}| -> ${described.result.name()} ${StagedCrash.tree(graph.to_tree(described.id))}"
	}

	tree : Code.Tree -> Str
	tree = |t| match t {
		Op(o) => StagedCrash.op(o.op, o.args)
		Param(k) => "p${k.to_str()}"
		Input(k) => "in${k.to_str()}"
		Arg(a) => "s${a.owner.to_str()}.${a.k.to_str()}"
		Out(o) => "n${o.node.to_str()}.${o.k.to_str()}"
		Def(n) => "n${n.to_str()}"
		Block(b) => {
			defs = b.defs.map(|d| "n${d.id.to_str()} = ${StagedCrash.tree(d.value)}; ")
			last = match b.end {
				Value(vals) => StagedCrash.all(vals)
				Jump(j) => "jump j${j.join.to_str()}(${StagedCrash.all(j.args)})"
				Return(v) => "return ${StagedCrash.tree(v)}"
				Continue(vals) => "continue(${StagedCrash.all(vals)})"
				Break(vals) => "break(${StagedCrash.all(vals)})"
				Branch(sw) => StagedCrash.tree(sw)
			}
			if defs.is_empty() last else "{ ${Str.join_with(defs, "")}${last} }"
		}
	}

	all : List(Code.Tree) -> Str
	all = |ts| Str.join_with(ts.map(StagedCrash.tree), ", ")

	op : Code.Op, List(Code.Tree) -> Str
	op = |o, args| match o {
		Lit(l) => StagedCrash.lit(l)
		Prim(p) => "${p.owner}.${p.method}(${StagedCrash.all(args)})"
		Call(r) => "r${r.to_str()}(${StagedCrash.all(args)})"
		Closure(r) => "closure r${r.to_str()}(${StagedCrash.all(args)})"
		Record(names) => {
			fields = List.map2(names, args, |name, arg| "${name}: ${StagedCrash.tree(arg)}")
			if fields.is_empty() "{}" else "{ ${Str.join_with(fields, ", ")} }"
		}
		Tuple => "(${StagedCrash.all(args)})"
		List => "[${StagedCrash.all(args)}]"
		Tag(name) => "${name}(${StagedCrash.all(args)})"
		Wrap(name) => "${name}.(${StagedCrash.all(args)})"
		Unwrap => "unwrap(${StagedCrash.all(args)})"
		Field(name) => "${StagedCrash.all(args)}.${name}"
		Index(i) => "${StagedCrash.all(args)}.${i.to_str()}"
		Payload(name, i) => "${StagedCrash.all(args)}.${name}.${i.to_str()}"
		Item => "item(${StagedCrash.all(args)})"
		OptField(name) => "${StagedCrash.all(args)}.?${name}"
		Switch(sw) => {
			scrutinee = StagedCrash.all(args.take_first(1))
			arms = List.map2(sw.arms, args.drop_first(1), |arm, body| "${StagedCrash.key(arm.key)} => ${StagedCrash.tree(body)}")
			joins = args.drop_first(1 + sw.arms.len()).map_with_index(|body, i| " j${i.to_str()}: ${StagedCrash.tree(body)}")
			"switch ${scrutinee} { ${Str.join_with(arms, " | ")} }${Str.join_with(joins, "")}"
		}
		And(_) => "and(${StagedCrash.all(args)})"
		Or(_) => "or(${StagedCrash.all(args)})"
		ForRange(r) => "for_range${if r.inclusive "=" else "<"}(${StagedCrash.all(args)})"
		ForList(_) => "for_list(${StagedCrash.all(args)})"
		Loop(_) => "loop(${StagedCrash.all(args)})"
		Lambda(_) => "lambda(${StagedCrash.all(args)})"
		Crash => "crash(${StagedCrash.all(args)})"
		Derived(name, _) => "derived ${name}(${StagedCrash.all(args)})"
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
		Lit(l) => StagedCrash.lit(l)
		Len(n) => "len ${n.to_str()}"
		AtLeast(n) => "len >= ${n.to_str()}"
		Default => "_"
	}
}

Color := [Red, Green, Blue]

shade : Color -> F32
shade = |c| match c {
	Red => 1.0
	Green => 0.0
	Blue => crash "no shade for Blue"
}

clamp : U16 -> U16
clamp = |n| if n > 10 { n } else { crash "too small: ${n.to_str()}" }

staged_match : Str
staged_match = StagedCrash.describe(shade)

staged_interpolated : Str
staged_interpolated = StagedCrash.describe(clamp)

main! = |_args| {
	echo!("${staged_match}\n")
	echo!("${staged_interpolated}\n")
	Ok({})
}
