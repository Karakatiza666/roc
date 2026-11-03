# A captured value that the description reads whole is one input slot, and
# the description reads its fields, items and backing as `Field`, `Index`
# and `Unwrap` of that slot (N18e). A value that the description reads only
# through field paths is one slot per path, as before. A whole read is an
# `OptField` of a record with an optional field, a value passed to a call
# such as `List.contains`, or a value the description builds into another.
Address : { city : Str, line : Str, zip ?: Str }

Plain : { city : Str, line : Str }

Order : { name : Str, ship : { to : Address } }

Query : { kind : [Any, Only(Str)], tags : List(Str), name : Str }

Holder : { places : List(Plain), city : Str }

Stage := {}.{
	render : Code(row -> Bool) -> Code.Bound(Str)
	render = |code| Code.bound(code, Stage.describe(code))

	holder : Code(Holder -> Bool) -> Code.Bound(Str)
	holder = |code| Stage.render(code)

	query : Code(Query -> Bool) -> Code.Bound(Str)
	query = |code| Stage.render(code)

	pick : Code(row -> out) -> Code.Bound(Str)
	pick = |code| Code.bound(code, Stage.describe(code))

	show : Code.Value -> Str
	show = |value| match value {
		Str(s) => "\"${s}\""
		Record(items) => "{${Str.join_with(items.map(Stage.show), ", ")}}"
		Tuple(items) => "(${Str.join_with(items.map(Stage.show), ", ")})"
		Tag(name, payloads) => "${name}(${Str.join_with(payloads.map(Stage.show), ", ")})"
		List(items) => "[${Str.join_with(items.map(Stage.show), ", ")}]"
		Wrap(inner) => "Wrap(${Stage.show(inner)})"
		Absent => "Absent"
		_ => "other"
	}

	run : Code.Bound(Str) -> Str
	run = |bound| "${bound.value()} inputs ${bound.inputs().len().to_str()}: ${Str.join_with(bound.inputs().map(Stage.show), "; ")}"

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

}

## An optional field read through `OptField` reads the record whole: one slot.
at : Address -> Str
at = |place| Stage.run(Stage.render(|c| c.address == place))

## A record with no optional field compares field by field: one slot per field.
plain : Plain -> Str
plain = |place| Stage.run(Stage.render(|c| c.address == place))

## `order.ship.to` is read whole and `order.name` by its path: two slots.
nested : Order -> Str
nested = |order| Stage.run(Stage.render(|o| o.to == order.ship.to and o.name == order.name))

## Item 0 of a tuple is read whole, item 1 by its path.
paired : (Address, Str) -> Str
paired = |pair| Stage.run(Stage.render(|c| c.address == pair.0 and c.id == pair.1))

## `List.contains` reads `place` whole, so its field is a field of that slot.
contained : Plain -> Str
contained = |place| Stage.run(Stage.holder(|r| r.places.contains(place) and r.city == place.city))

## A tag and a list are read whole, each by its own path: three slots.
queried : Query -> Str
queried = |query| Stage.run(Stage.query(|r| r.kind == query.kind and r.tags.contains(query.name) and query.tags.contains(r.name)))

## A record returned whole, with a field of it read too.
returned : Plain -> Str
returned = |place| Stage.run(Stage.pick(|r| if (r.city == place.city) Ok(place) else Err(r.city)))

main! = |args| {
	n = args.len().to_str()
	absent : Address
	absent = { city: "Oslo${n}", line: "Storgata 4" }
	present : Address
	present = { city: "Oslo${n}", line: "Storgata 4", zip: "0155" }
	echo!("at: ${at(present)}\n")
	echo!("plain: ${plain({ city: "Oslo${n}", line: "Storgata 4" })}\n")
	echo!("nested: ${nested({ name: "ada${n}", ship: { to: absent } })}\n")
	echo!("paired: ${paired((present, "c${n}"))}\n")
	echo!("contained: ${contained({ city: "Oslo${n}", line: "Storgata 4" })}\n")
	echo!("queried: ${queried({ kind: Only("k${n}"), tags: ["a", "b"], name: "ada" })}\n")
	echo!("returned: ${returned({ city: "Oslo${n}", line: "Storgata 4" })}\n")
	Ok({})
}
