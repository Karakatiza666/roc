# A call of a method bound to another function by name, `method = f`.
#
# The checker records such a call against the alias: the edge fixes the alias's
# quantified variables and answers the alias's requirements, not the target's.
# The walk composes both through the alias's forwarded lookup, so the call
# describes as the function the alias names, as it does for a call of that
# function directly. A generic target is fixed by composing the edge's
# substitution through the alias's lookup, so a variable only a `where` clause
# names is fixed too, and a target with a `where` requirement is answered by
# the evidence the alias's lookup forwards from the alias's own requirements.
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

Pt := { x : U16 }.{
	doubled_x : Pt -> U16
	doubled_x = |p| p.x * 2

	twice : Pt -> U16
	twice = doubled_x
}

Holder(a) := { v : a }.{
	held : Holder(a) -> a
	held = |h| h.v

	get : Holder(a) -> a
	get = held
}

Named := { n : U16 }.{
	label : Named -> Str
	label = |x| x.n.to_str()

	name : Named -> Str
	name = label
}

Scaled(a) := { v : a }.{
	scaled : Scaled(a) -> a where [a.times : a, b -> a, b.from_numeral : Numeral -> Try(b, [InvalidNumeral(Str)])]
	scaled = |s| s.v * 2

	twice = scaled
}

# The alias carries an annotation of its own, so its requirements are the
# alias's, and the target's answer them by relating to the alias's callable.
Annotated(a) := { v : a }.{
	scaled : Annotated(a) -> a where [a.times : a, b -> a, b.from_numeral : Numeral -> Try(b, [InvalidNumeral(Str)])]
	scaled = |s| s.v * 2

	twice : Annotated(a) -> a where [a.times : a, b -> a, b.from_numeral : Numeral -> Try(b, [InvalidNumeral(Str)])]
	twice = scaled
}

# The methods carry no annotation, so the checker gives `scaled` the record
# `{ v : a }` its body reads for a parameter, and a call on an `Inferred(U16)`
# fixes that parameter to the nominal. The call reads the method at the
# callable the checker recorded for it, as Monotype specializes it there.
Inferred(a) := { v : a }.{
	scaled = |s| s.v * 2
	twice = scaled
}

# A call that fixes the record a method returns to the nominal: the row's
# result is the callable's, the nominal.
Made(a) := { v : a }.{
	make = |x| { v: x }
}

# A curried method whose first parameter the call fixes to the nominal: the
# inner lambda is read as the function the callable returns.
Curried(a) := { v : a }.{
	add_to = |s| |n| s.v + n
}

# A method that passes the parameter the call fixed to the nominal on to
# another method whose parameter is the same record: that call reads its
# callee at the nominal too.
Passing(a) := { v : a }.{
	inner = |s| s.v * 2
	outer = |s| Passing.inner(s)
}

# A lift nested inside a parameter: the checker gives `nested_read` the
# record `{ inner : { v : a } }`, and the call fixes the field, and the payload
# of `tag_read`'s `Got`, to `Inner(U16)`. The body passes that position on to
# `inner_read`, whose parameter is the same record, so that call reads its
# callee at the nominal too.
Inner(a) := { v : a }

inner_read = |s| s.v * 2

nested_read = |r| inner_read(r.inner)

tag_read = |t| match t {
	Got(s) => inner_read(s)
	Nothing => 0
}

loud : a -> Str where [a.name : a -> Str]
loud = |x| x.name()

# The plain case: `twice` is `doubled_x`.
plain : Pt -> U16
plain = |p| p.twice()

# The generic case: `get` is `held`, at the instantiation the call fixes.
generic : Holder(Str) -> Str
generic = |h| h.get()

# The `where` case: `loud` forwards its caller's `name`, which is `label`.
dispatched : Named -> Str
dispatched = |x| loud(x)

# The where-only case: `twice` is `scaled`, whose literal's type `b` is in no
# type, only in a `where` clause. The alias's lookup records what it copied `b`
# to, in the alias's own variables, and the call fixes those.
where_only : Scaled(U16) -> U16
where_only = |s| s.twice()

# The annotated alias, called as a method and as a direct call of its target.
annotated_alias : Annotated(U16) -> U16
annotated_alias = |s| s.twice()

annotated_target : Annotated(U16) -> U16
annotated_target = |s| Annotated.scaled(s)

# A direct call of the alias is accepted as a direct call of its target is.
direct_target : Scaled(U16) -> U16
direct_target = |s| Scaled.scaled(s)

direct_alias : Scaled(U16) -> U16
direct_alias = |s| Scaled.twice(s)

# The unannotated method, called as a method, through its alias, and directly.
inferred_direct : Inferred(U16) -> U16
inferred_direct = |x| x.scaled()

inferred_alias : Inferred(U16) -> U16
inferred_alias = |x| x.twice()

direct_inferred : Inferred(U16) -> U16
direct_inferred = |x| Inferred.scaled(x)

direct_inferred_alias : Inferred(U16) -> U16
direct_inferred_alias = |x| Inferred.twice(x)

lifted_result : U16 -> Made(U16)
lifted_result = |n| Made.make(n)

curried_lift : Curried(U16), U16 -> U16
curried_lift = |c, n| Curried.add_to(c)(n)

passed_on : Passing(U16) -> U16
passed_on = |x| x.outer()

nested_lift : Inner(U16) -> U16
nested_lift = |i| nested_read({ inner: i })

tag_lift : Inner(U16) -> U16
tag_lift = |i| tag_read(Got(i))

main! = |_args| {
	echo!("${Stage.describe(plain)}\n")
	echo!("${Stage.describe(generic)}\n")
	echo!("${Stage.describe(dispatched)}\n")
	echo!("${Stage.describe(where_only)}\n")
	echo!("annotated_alias: ${Stage.describe(annotated_alias)}\n")
	echo!("annotated_target: ${Stage.describe(annotated_target)}\n")
	echo!("direct_target: ${Stage.describe(direct_target)}\n")
	echo!("direct_alias: ${Stage.describe(direct_alias)}\n")
	echo!("inferred_direct: ${Stage.describe(inferred_direct)}\n")
	echo!("inferred_alias: ${Stage.describe(inferred_alias)}\n")
	echo!("direct_inferred: ${Stage.describe(direct_inferred)}\n")
	echo!("direct_inferred_alias: ${Stage.describe(direct_inferred_alias)}\n")
	echo!("lifted_result: ${Stage.describe(lifted_result)}\n")
	echo!("curried_lift: ${Stage.describe(curried_lift)}\n")
	echo!("passed_on: ${Stage.describe(passed_on)}\n")
	echo!("nested_lift: ${Stage.describe(nested_lift)}\n")
	echo!("tag_lift: ${Stage.describe(tag_lift)}\n")
	Ok({})
}
