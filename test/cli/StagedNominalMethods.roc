# Which comparison a nominal component gets: the one it writes, or the one the
# compiler derives.
#
# `==` and `.to_hash` dispatch to a nominal's own method before they look at
# the nominal's representation, and a derivation carries no dispatch plan, so
# the walk resolves the method itself. The checked method registries answer it,
# and they say which of the two it is: a written method describes as its body,
# and a derived one expands the backing.
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

# A nominal that writes both methods.
Point := { x : U16 }.{
	is_eq : Point, Point -> Bool
	is_eq = |a, b| a.x <= b.x

	to_hash : Point, Hasher -> Hasher
	to_hash = |a, h| a.x.to_hash(h)
}

# The same shape, deriving both.
Plain := { x : U16 }.{
	is_eq : _
	to_hash : _
}

# An opaque nominal that writes its own. Calling the method leaves the
# representation hidden, which is what the `Ty` of an opaque does everywhere
# else; a derived one over an opaque stays refused for the same reason.
Sealed :: { x : U16 }.{
	is_eq : Sealed, Sealed -> Bool
	is_eq = |a, b| a.x == b.x
}

# The written method is the comparison, so the description is its body: `<=`,
# where the backing would compare with `==`. Its row has one call, so the graph
# view inlines it.
written_eq : { a : Point, b : Point } -> Bool
written_eq = |r| { m: r.a } == { m: r.b }

# The derived one is the compiler's recipe, so the comparison is the backing's.
derived_eq : { a : Plain, b : Plain } -> Bool
derived_eq = |r| { m: r.a } == { m: r.b }

# `to_hash : value, Hasher -> Hasher`, so the value leads and the hasher follows.
written_hash : { p : Point, h : Hasher } -> Hasher
written_hash = |r| { m: r.p }.to_hash(r.h)

# The derived recipe feeds the hasher one component at a time.
derived_hash : { p : Plain, h : Hasher } -> Hasher
derived_hash = |r| { m: r.p }.to_hash(r.h)

# An opaque component describes as the call and nothing more.
sealed_eq : { a : Sealed, b : Sealed } -> Bool
sealed_eq = |r| { m: r.a } == { m: r.b }

# A builtin container writes its own `is_eq` like any other nominal, and the
# walk stops at a builtin's body, so the comparison is the name and nothing
# more. A translator resolves that name against what its own target provides,
# or rejects it by name.
list_eq : { a : List(U16), b : List(U16) } -> Bool
list_eq = |r| { m: r.a } == { m: r.b }

dict_eq : { a : Dict(U16, U16), b : Dict(U16, U16) } -> Bool
dict_eq = |r| { m: r.a } == { m: r.b }

try_eq : { a : Try(U16, Str), b : Try(U16, Str) } -> Bool
try_eq = |r| { m: r.a } == { m: r.b }

main! = |_args| {
	echo!("${Stage.describe(written_eq)}\n")
	echo!("${Stage.describe(derived_eq)}\n")
	echo!("${Stage.describe(written_hash)}\n")
	echo!("${Stage.describe(derived_hash)}\n")
	echo!("${Stage.describe(sealed_eq)}\n")
	echo!("${Stage.describe(list_eq)}\n")
	echo!("${Stage.describe(dict_eq)}\n")
	echo!("${Stage.describe(try_eq)}\n")
	Ok({})
}
