# A derived `==` on a record with an optional field compares the field
# through its `OptField`, as the compiler compares the field's tagged slot
# `[#Missing, #Present(value)]`: the fields are equal where both records hold
# them with equal values, and where neither record holds them. A captured
# record is one input slot, its `Code.Value` `Absent` where it does not hold
# the field. The same holds for `!=`, for an optional field inside a nested
# record, a tag payload and a nominal, and for a stored row compared with a
# literal. A derived hash of such a record is left to the stage.
Address : { city : Str, zip ?: Str }

Customer : { id : Str, address : Address }

Order : { id : Str, ship : { to : Address } }

Where : [At(Address), Nowhere]

Place := { address : Address }.{
	is_eq : _
}

Hashed : { address : Address, h : Hasher }

Stage := {}.{
	render : Code(row -> Bool) -> Code.Bound(Str)
	render = |code| Code.bound(code, Stage.describe(code))

	customer : Code(Customer -> Bool) -> Code.Bound(Str)
	customer = |code| Stage.render(code)

	hash : Code(Hashed -> Hasher) -> Str
	hash = |code| Stage.describe(code)

	show : Code.Value -> Str
	show = |value| match value {
		Str(s) => "\"${s}\""
		Record(items) => "{${Str.join_with(items.map(Stage.show), ", ")}}"
		Tag(name, payloads) => "${name}(${Str.join_with(payloads.map(Stage.show), ", ")})"
		List(items) => "[${Str.join_with(items.map(Stage.show), ", ")}]"
		Wrap(inner) => "Wrap(${Stage.show(inner)})"
		Absent => "Absent"
		_ => "other"
	}

	run : Code.Bound(Str) -> Str
	run = |bound| "${bound.value()} inputs ${Str.join_with(bound.inputs().map(Stage.show), "; ")}"

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

at : Address -> Str
at = |place| Stage.run(Stage.render(|c| c.address == place))

not_at : Address -> Str
not_at = |place| Stage.run(Stage.render(|c| c.address != place))

shipped : Address -> Str
shipped = |place| Stage.run(Stage.render(|o| o.ship == { to: place }))

listed : List(Address) -> Str
listed = |places| Stage.run(Stage.render(|r| r.places == places))

tagged : Address -> Str
tagged = |place| Stage.run(Stage.render(|w| w == At(place)))

named : Address -> Str
named = |place| Stage.run(Stage.render(|p| p == Place.({ address: place })))

paris : Str
paris = Stage.run(Stage.customer(|c| c.address == { city: "Paris" }))

paris_zip : Str
paris_zip = Stage.run(Stage.customer(|c| c.address == { city: "Paris", zip: "75" }))

hashed : Str
hashed = Stage.hash(|r| r.address.to_hash(r.h))

## The same comparisons run as a program.
same : Address, Address -> Bool
same = |a, b| a == b

main! = |args| {
	n = args.len().to_str()
	present : Address
	present = { city: "Paris${n}", zip: "75" }
	absent : Address
	absent = { city: "Paris${n}" }
	echo!("at present: ${at(present)}\n")
	echo!("at absent: ${at(absent)}\n")
	echo!("not at: ${not_at(absent)}\n")
	echo!("shipped: ${shipped(absent)}\n")
	echo!("listed: ${listed([present, absent])}\n")
	echo!("tagged: ${tagged(present)}\n")
	echo!("named: ${named(absent)}\n")
	echo!("paris: ${paris}\n")
	echo!("paris zip: ${paris_zip}\n")
	echo!("hashed: ${hashed}\n")
	echo!("run: ${Str.inspect([same(present, present), same(absent, absent), same(present, absent), same(absent, present), same(present, { city: "Paris${n}", zip: "76" })])}\n")
	Ok({})
}
