# The clause translator: a reified Roc function in, a SurrealQL expression out.
#
# A clause is a Roc function over a row. The translator reads the root row of
# its `Code.Graph` as a tree and evaluates the tree with each parameter bound
# to what it stands for in SurrealQL. The row, a fetched link, an element of a
# list and a union arm are places in a document, so a field read off one is a
# path, and a list operation with a closure is a SurrealQL closure over `$vN`.
import Ql

Translate :: {}.{

	## What a value in a reified function stands for.
	##
	## `Row` is a record at a place: `Doc` is the record a statement is over
	## (`""` for the row itself, `$after`, `$this`), `Ref` is a record id that
	## a read traverses (`customer` after `Link.get`, an edge `$v1`), and `Obj`
	## is an object inside a record. `edge` says the record is a relation, whose
	## `from` and `to` are SurrealDB's `in` and `out`. `Expr` is a value that
	## needs no parentheses around it as an operand, and `Infix` one that does.
	## `Column` is `rows.map(f)` over a `Group`: the expression `f` reads, that
	## each aggregate writes for itself. `Moment` is the text of a datetime, and
	## holds the datetime expression.
	Binding := [
		Row({ at : Str, of : [Doc, Ref, Obj], edge : Bool }),
		Pair(Binding, Binding),
		ListOf({ at : Str, edges : Bool }),
		Union({ at : Str, variants : List({ name : Str, payloads : List(Code.Ty) }) }),
		Maybe(Str),
		Params,
		Group(Binding),
		Column(Str),
		Moment(Str),
		Expr(Str),
		Infix(Str),
		Fields(List({ name : Str, binding : Binding })),
	]

	## One step of a field path: `items[*].qty` is `Field("items")`, `Each`,
	## `Field("qty")`.
	Step := [Field(Str), Each].{
		is_eq : _
	}

	## What the translation of one row's tree reads: the graph its calls name,
	## what the row's parameters and kept nodes stand for, and how a parameter
	## of the statement is spelled.
	Env : {
		graph : Code.Graph,
		params : List(Binding),
		row : U32,
		nodes : List({ id : U32, binding : Binding, ty : Try(Code.Ty, [Untyped]) }),
		param : Str -> Str,
		depth : U64,
		random : Bool,
	}

	# ------------------------------------------------------------ bindings

	## The record a statement runs over: the table row (`""`), `$after` in an
	## event, `$this` in a field definition. `edge` is set for a relation table.
	document : Str, Bool -> Binding
	document = |at, edge| Binding.Row({ at, of: Doc, edge })

	## The edges of a relation table from the row: `->t` going out, `<-t`
	## coming in. Each element is an edge record.
	outgoing : Str -> Binding
	outgoing = |table| Binding.ListOf({ at: "->${Ql.ident(table)}", edges: Bool.True })

	incoming : Str -> Binding
	incoming = |table| Binding.ListOf({ at: "<-${Ql.ident(table)}", edges: Bool.True })

	## A value at a SurrealQL expression, bound by its type: a record is a
	## place to read fields from, a list takes list operations, a union is
	## matched, a `Try` (an optional field) is tested, anything else is a
	## scalar. `at("$value", ty)` is the value of a field `ASSERT`.
	at : Str, Code.Ty -> Binding
	at = |expr, ty| match ty {
		Record(_) => Binding.Row({ at: expr, of: Obj, edge: Bool.False })
		ListOf(_) => Binding.ListOf({ at: expr, edges: Bool.False })
		TagUnion(variants) => Binding.Union({ at: expr, variants })
		Named(name, backing) =>
			if name == "Builtin.Try" {
				Binding.Maybe(expr)
			} else if Translate.cut(name) != Other or name == "Builtin.Bool" {
				Binding.Expr(expr)
			} else {
				Translate.at(expr, backing)
			}
		_ => Binding.Expr(expr)
	}

	## A statement parameter `p.name` as a `LET` variable: `$name`.
	variable : Str -> Str
	variable = |name| "$${name}"

	## The name of captured value `k`, numbered from 1: `_1`, `_2`, ...
	input_name : U64 -> Str
	input_name = |k| "_${(k + 1).to_str()}"

	## Which nominal of `Surreal`'s cut (`Surreal.code_primitives`) a type or
	## a `Prim` owner is. Only the cut reaches a `Prim` with these owners.
	cut : Str -> [Link, Id, Datetime, Duration, Other]
	cut = |name| match name {
		"Surreal.Link" => Link
		"Surreal.Id" => Id
		"Surreal.Datetime" => Datetime
		"Surreal.Duration" => Duration
		_ => Other
	}

	# ------------------------------------------------------------ entry points

	## A reified function applied to what its parameters stand for. A clause
	## that reads rows may not call `Rand`: it would give other rows each time.
	evaluate : Code.Graph, List(Binding), (Str -> Str) -> Try(Binding, Ql.Error)
	evaluate = |graph, bindings, param| Translate.run(graph, bindings, param, Bool.False)

	## The same, as one SurrealQL expression, for a value that SurrealDB gives to
	## one row: a default, a computed field or an update. `Rand` is allowed.
	row_value : Code.Graph, List(Binding), (Str -> Str) -> Try(Str, Ql.Error)
	row_value = |graph, bindings, param| Translate.text(Translate.run(graph, bindings, param, Bool.True)?)

	run : Code.Graph, List(Binding), (Str -> Str), Bool -> Try(Binding, Ql.Error)
	run = |graph, bindings, param, random| {
		root = graph.root_row()
		if root.params.len() != bindings.len() {
			return Err(Unsupported("this clause takes ${bindings.len().to_str()} argument(s)"))
		}
		Translate.eval(graph.to_tree(root.id), { graph, params: bindings, row: root.id, nodes: [], param, depth: 0, random })
	}

	## The clause as one SurrealQL expression.
	render : Code.Graph, List(Binding), (Str -> Str) -> Try(Str, Ql.Error)
	render = |graph, bindings, param| Translate.text(Translate.evaluate(graph, bindings, param)?)

	## The fields of a record the clause builds, in name order, as SurrealQL
	## expressions. The names are Roc's; a caller spells them with `Ql.ident`.
	columns : Code.Graph, List(Binding), (Str -> Str) -> Try(List({ name : Str, surql : Str }), Ql.Error)
	columns = |graph, bindings, param| match Translate.evaluate(graph, bindings, param)? {
		Fields(fields) => fields.map_try(|f| Ok({ name: f.name, surql: Translate.text(f.binding)? }))
		_ => Err(Unsupported("a result row is a record, so each field has a name"))
	}

	## The `SET` list of an update patch `|o| { ..o, f: .. }`, whose last
	## parameter is the row. A field that reads the row's field of its own name
	## is unchanged and left out; every other field is `f = <expr>`, in name
	## order. The names are spelled as SurrealDB names them.
	assignments : Code.Graph, List(Binding), (Str -> Str) -> Try(List({ name : Str, surql : Str }), Ql.Error)
	assignments = |graph, bindings, param| {
		root = graph.root_row()
		last = (root.params.len() - 1).to_u32_wrap()
		edge = match bindings.last() {
			Ok(Row(r)) => r.edge
			_ => Bool.False
		}
		names = match Translate.unwrapped(Translate.body(graph.to_tree(root.id))) {
			Op({ op: Record(fields), args, .. }) =>
				List.map2(fields, args, |name, value| { name, value })
					.keep_if(|f| !Translate.reads_own(f.value, f.name, last))
					.map(|f| f.name)
			other if Translate.is_param(other, last) => []
			_ => return Err(Unsupported("an update returns the row, as `|o| { ..o, field: .. }`"))
		}
		if names.is_empty() {
			return Err(Unsupported("this update changes no field"))
		}
		if names.contains("id") {
			return Err(Unsupported("an update cannot change `id`, the record key"))
		}
		fields = match Translate.run(graph, bindings, param, Bool.True)? {
			Fields(all) => all
			_ => return Err(Unsupported("an update returns the row, as `|o| { ..o, field: .. }`"))
		}
		fields
			.keep_if(|f| names.contains(f.name))
			.map_try(|f| Ok({ name: Translate.spell_name(f.name, edge), surql: Translate.text(f.binding)? }))
	}

	## Whether a patch field is the row's field of the same name, unchanged.
	reads_own : Code.Tree, Str, U32 -> Bool
	reads_own = |tree, name, row| match tree {
		Op({ op: Field(read), args: [inner], .. }) => read == name and Translate.is_param(inner, row)
		_ => Bool.False
	}

	is_param : Code.Tree, U32 -> Bool
	is_param = |tree, k| match tree {
		Param(n) => n == k
		Op({ op: Unwrap, args: [inner], .. }) => Translate.is_param(inner, k)
		_ => Bool.False
	}

	unwrapped : Code.Tree -> Code.Tree
	unwrapped = |tree| match tree {
		Op({ op: Wrap(_), args: [inner], .. }) => inner
		other => other
	}

	## A row's tree without the block around it, where the block holds one
	## value and no definitions.
	body : Code.Tree -> Code.Tree
	body = |tree| match tree {
		Block({ defs: [], end: Value([one]) }) => one
		other => other
	}

	# ------------------------------------------------------------ field paths

	## The field path a path lambda reads: a chain of field reads, `.?` reads
	## and `List.map` with a closure that is itself a path.
	path_of : Code.Graph -> Try(List(Step), Ql.Error)
	path_of = |graph| {
		root = graph.root_row()
		if root.params.len() != 1 {
			return Err(Unsupported("a field path reads one row"))
		}
		Translate.steps(graph, graph.to_tree(root.id))
	}

	## The paths a key lambda reads: one path, or a record or tuple of them.
	paths_of : Code.Graph -> Try(List(List(Step)), Ql.Error)
	paths_of = |graph| {
		root = graph.root_row()
		if root.params.len() != 1 {
			return Err(Unsupported("a field path reads one row"))
		}
		# A row read twice (a nominal row's `Unwrap`) is a kept definition.
		(kept, value) = match graph.to_tree(root.id) {
			Block({ defs, end: Value([one]) }) => (defs, one)
			other => ([], other)
		}
		match value {
			Op({ op: Record(_), args, .. }) | Op({ op: Tuple, args, .. }) => args.map_try(|arg| Translate.steps_in(graph, kept, arg))
			single => Ok([Translate.steps_in(graph, kept, single)?])
		}
	}

	steps : Code.Graph, Code.Tree -> Try(List(Step), Ql.Error)
	steps = |graph, tree| Translate.steps_in(graph, [], tree)

	## The steps of a path, where `defs` are the kept definitions in scope.
	steps_in : Code.Graph, List({ id : U32, value : Code.Tree }), Code.Tree -> Try(List(Step), Ql.Error)
	steps_in = |graph, defs, tree| match tree {
		Param(_) => Ok([])
		Def(n) => match defs.find_last(|d| d.id == n) {
			Ok(d) => Translate.steps_in(graph, defs, d.value)
			Err(_) => Err(Unsupported("a value is read before its block computes it"))
		}
		Block({ defs: more, end: Value([one]) }) => Translate.steps_in(graph, defs.concat(more), one)
		Op({ op: Unwrap, args: [inner], .. }) => Translate.steps_in(graph, defs, inner)
		Op({ op: Field(name), args: [inner], .. }) | Op({ op: OptField(name), args: [inner], .. }) =>
			Ok(Translate.steps_in(graph, defs, inner)?.append(Step.Field(name)))
		Op({ op: Prim({ owner: "List", method: "map" }), args: [list, Op({ op: Closure(row), args: [], .. })], .. }) => {
			outer = Translate.steps_in(graph, defs, list)?
			inner = Translate.steps(graph, graph.to_tree(row))?
			Ok(outer.append(Step.Each).concat(inner))
		}
		Op({ op, .. }) => Err(Unsupported("a field path reads fields only; this one calls `${Translate.describe(op)}`"))
		_ => Err(Unsupported("a field path reads fields only"))
	}

	## A path as a field definition names it: `items[*].qty`.
	spell : List(Step) -> Str
	spell = |path| path.fold(
		"",
		|text, step| match step {
			Each => "${text}[*]"
			Field(name) => if (text.is_empty()) Ql.ident(name) else "${text}.${Ql.member(name)}"
		},
	)

	## What an op is, for a refusal that names it.
	describe : Code.Op -> Str
	describe = |op| match op {
		Prim({ owner, method }) => "${owner}.${method}"
		Call(_) => "a helper"
		Closure(_) | Lambda(_) => "a function"
		Lit(_) => "a literal"
		Record(_) => "a record"
		Tuple => "a tuple"
		List => "a list"
		Tag(name) => name
		Wrap(name) => name
		Index(_) => "a tuple position"
		Payload(name, _) => "the payload of ${name}"
		Item => "a list index"
		Switch(_) => "a branch"
		And(_) => "`and`"
		Or(_) => "`or`"
		ForRange(_) | ForList(_) | Loop(_) => "a loop"
		Crash => "`crash`"
		Derived(method, _) => method
		Unwrap | Field(_) | OptField(_) => "a field read"
	}

	# ------------------------------------------------------------ captured values

	## The SurrealQL value of a value captured from around the clause, by the
	## slot type the graph gives it. An `Id` is its record id, a `Datetime`
	## its datetime. A captured `Link` is refused. Capture its `id()` instead.
	captured : Code.Ty, Code.Value -> Try(Ql.Value, Ql.Error)
	captured = |ty, value| match (ty, value) {
		(Named(name, backing), Wrap(inner)) => match Translate.cut(name) {
			Id => match Translate.captured(backing, inner)? {
				Object(fields) => match (Translate.named_str(fields, "table"), Translate.named_str(fields, "key")) {
					(Ok(table), Ok(key)) => Ok(Ql.Value.Record({ table, key }))
					_ => Err(Unsupported("a captured id without its table and key"))
				}
				_ => Err(Unsupported("a captured id without its table and key"))
			}
			Datetime => match Translate.captured(backing, inner)? {
				Object(fields) => Translate.named_str(fields, "iso").map_ok(|iso| Ql.Value.Datetime(iso)).map_err(|_| Unsupported("a captured datetime without its text"))
				_ => Err(Unsupported("a captured datetime without its text"))
			}
			Link => Err(Unsupported("a captured `Link` has no SurrealQL value; capture its `id()`"))
			Duration => Err(Unsupported("a captured `Duration` has no SurrealQL value; build it in the clause, as `Time.hours(1)`"))
			Other => Translate.captured(backing, inner)
		}
		(_, Int(n)) => match n.to_i64_try() {
			Ok(i) => Ok(Ql.Value.Int(i))
			Err(_) => Err(Unsupported("a captured integer outside the range of a SurrealDB int"))
		}
		(_, Frac(f)) => Ok(Ql.Value.Float(f))
		(_, Dec(d)) => Ok(Ql.Value.Decimal(d))
		(_, Bool(b)) => Ok(Ql.Value.Bool(b))
		(_, Str(s)) => Ok(Ql.Value.Str(s))
		(Record(fields), Record(values)) => {
			pairs = List.map2(fields, values, |f, v| { f, v })
			Ok(Ql.Value.Object(pairs.map_try(|p| Ok({ name: p.f.name, value: Translate.captured(p.f.ty, p.v)? }))?))
		}
		(ListOf(item), List(values)) => Ok(Ql.Value.Array(values.map_try(|v| Translate.captured(item, v))?))
		(TagUnion(variants), Tag(name, payloads)) => {
			types = match variants.find_first(|v| v.name == name) {
				Ok(v) => v.payloads
				Err(_) => return Err(Unsupported("a captured tag `${name}` outside its union"))
			}
			values = List.map2(types, payloads, |t, v| { t, v }).map_try(|p| Translate.captured(p.t, p.v))?
			kind = { name: "kind", value: Ql.Value.Str(name) }
			match (types, values) {
				([], _) => Ok(Ql.Value.Str(name))
				([only], [Object(fields)]) if Translate.is_record(only) => Ok(Ql.Value.Object(List.concat([kind], fields)))
				(_, [one]) => Ok(Ql.Value.Object([kind, { name: "value", value: one }]))
				_ => Ok(Ql.Value.Object(List.concat([kind], values.map_with_index(|v, k| { name: "_${k.to_str()}", value: v }))))
			}
		}
		_ => Err(Unsupported("a captured `${ty.name()}` has no SurrealQL value"))
	}

	named_str : List({ name : Str, value : Ql.Value }), Str -> Try(Str, [Missing])
	named_str = |fields, name| match fields.find_first(|f| f.name == name) {
		Ok({ value: Str(s), .. }) => Ok(s)
		_ => Err(Missing)
	}

	## Whether a union payload of this type is encoded as the object's own
	## fields. `Link`, `Id` and `Datetime` are scalars to SurrealDB.
	is_record : Code.Ty -> Bool
	is_record = |ty| match ty {
		Record(_) => Bool.True
		Named(name, backing) => Translate.cut(name) == Other and !name.starts_with("Builtin.") and Translate.is_record(backing)
		_ => Bool.False
	}

	# ------------------------------------------------------------ text

	## A binding as a SurrealQL expression that stands on its own.
	text : Binding -> Try(Str, Ql.Error)
	text = |binding| match binding {
		Expr(s) | Infix(s) | Maybe(s) => Ok(s)
		Moment(s) => Ok("<string>${s}")
		ListOf(list) => Ok(list.at)
		Union(u) => Ok(u.at)
		Row(r) => match r.of {
			Doc => Ok(if (r.at.is_empty()) "$this" else r.at)
			Ref => Ok("${r.at}.*")
			Obj => Ok(r.at)
		}
		Fields(fields) => {
			parts = fields.map_try(|f| Ok("${Ql.member(f.name)}: ${Translate.text(f.binding)?}"))?
			Ok(if (parts.is_empty()) "{}" else "{ ${Str.join_with(parts, ", ")} }")
		}
		Pair(_, _) => Err(Unsupported("a pair has no SurrealQL value; take `.0` or `.1`"))
		Params => Err(Unsupported("the parameter record has no SurrealQL value; read one of its fields"))
		Group(_) | Column(_) => Err(Unsupported("a group's rows have no SurrealQL value; aggregate them with `len`, `keep_if(..).len()` or `map(..).sum()`"))
	}

	## A binding as the operand of an operator: an infix expression is
	## parenthesised, so nesting never depends on SurrealQL's precedence.
	operand : Binding -> Try(Str, Ql.Error)
	operand = |binding| match binding {
		Infix(s) => Ok("(${s})")
		other => Translate.text(other)
	}

	expr : Code.Tree, Env -> Try(Str, Ql.Error)
	expr = |tree, env| Translate.text(Translate.eval(tree, env)?)

	arg : Code.Tree, Env -> Try(Str, Ql.Error)
	arg = |tree, env| Translate.operand(Translate.eval(tree, env)?)

	# ------------------------------------------------------------ evaluation

	## What one tree stands for. A kept node is computed once, where its block
	## defines it, and each read of it is what it stands for.
	eval : Code.Tree, Env -> Try(Binding, Ql.Error)
	eval = |tree, env| match tree {
		Param(k) => match env.params.get(k.to_u64()) {
			Ok(binding) => Ok(binding)
			Err(_) => Err(Unsupported("this clause reads a parameter it does not take"))
		}
		Def(n) => match env.nodes.find_last(|entry| entry.id == n) {
			Ok(entry) => Ok(entry.binding)
			Err(_) => Err(Unsupported("a value is read before its block computes it"))
		}
		Input(k) => {
			spell_param = env.param
			ty = match env.graph.slots().get(k.to_u64()) {
				Ok(found) => found
				Err(_) => return Err(Unsupported("a captured value the graph has no slot for"))
			}
			Ok(Translate.at(spell_param(Translate.input_name(k.to_u64())), ty))
		}
		Arg(_) => Err(Translate.no_loop)
		Out(_) => Err(Unsupported("a branch that delivers several values has no SurrealQL form"))
		Block(block) => {
			inner = block.defs.fold_try(
				env,
				|acc, def| {
					value = Translate.eval(def.value, acc)?
					Ok({ ..acc, nodes: acc.nodes.append({ id: def.id, binding: value, ty: Translate.type_of(def.value, acc) }) })
				},
			)?
			match block.end {
				Value([one]) => Translate.eval(one, inner)
				Value(_) => Err(Unsupported("a branch that delivers several values has no SurrealQL form"))
				Return(_) | Jump(_) | Branch(_) => Err(Unsupported("a clause cannot leave early; every branch delivers its value"))
				Continue(_) | Break(_) => Err(Translate.no_loop)
			}
		}
		Op(node) => Translate.op(node.op, node.args, node.ty, env)
	}

	## The type of a value, where the tree or the graph states it.
	type_of : Code.Tree, Env -> Try(Code.Ty, [Untyped])
	type_of = |tree, env| match tree {
		Op({ ty, .. }) => Ok(ty)
		Param(k) => env.graph.row(env.row).params.get(k.to_u64()).map_err(|_| Untyped)
		Input(k) => env.graph.slots().get(k.to_u64()).map_err(|_| Untyped)
		Def(n) => match env.nodes.find_last(|entry| entry.id == n) {
			Ok(entry) => entry.ty
			Err(_) => Err(Untyped)
		}
		_ => Err(Untyped)
	}

	is_datetime : Code.Tree, Env -> Bool
	is_datetime = |tree, env| match Translate.type_of(tree, env) {
		Ok(Named(name, _)) => Translate.cut(name) == Datetime
		_ => Bool.False
	}

	no_loop : Ql.Error
	no_loop = Unsupported("a clause has no loop; use `any`, `all`, `map`, `keep_if` or `sum` over a list")

	## One operation, over the trees of its arguments and regions, with the
	## type of its result.
	op : Code.Op, List(Code.Tree), Code.Ty, Env -> Try(Binding, Ql.Error)
	op = |operation, args, ty, env| {
		first = |_| match args.first() {
			Ok(tree) => Translate.eval(tree, env)
			Err(_) => Err(Unsupported("an operation with no operand"))
		}
		match operation {
			Lit(literal) => Translate.literal(literal).map_ok(|s| Binding.Expr(s))
			Prim(prim) => Translate.prim(prim.owner, prim.method, args, ty, env)
			Call(row) => Translate.expand(row, args.map_try(|a| Translate.eval(a, env))?, env)
			Closure(_) | Lambda(_) => Err(Unsupported("a function in a clause means something only as the argument of a list operation"))
			Record(names) => {
				fields = List.map2(names, args, |name, value| { name, value }).map_try(|f| Ok({ name: f.name, binding: Translate.eval(f.value, env)? }))?
				Ok(Binding.Fields(fields))
			}
			Tuple => Err(Unsupported("a tuple has no SurrealQL value; a key of several fields is a record"))
			List => {
				items = args.map_try(|a| Translate.expr(a, env))?
				Ok(Binding.ListOf({ at: "[${Str.join_with(items, ", ")}]", edges: Bool.False }))
			}
			Item => Err(Unsupported("a list index has no SurrealQL form here; use `find_first` or `any`"))
			Tag(name) => Translate.tag(name, args, env)
			Wrap(name) => Translate.wrap(name, args, env)
			Unwrap => match args {
				[inner] if Translate.is_datetime(inner, env) => {
					# A datetime's `iso` is its text, which is how `==` on a
					# `Datetime` arrives. An equality compares the datetimes.
					Ok(Binding.Fields([{ name: "iso", binding: Binding.Moment(Translate.arg(inner, env)?) }]))
				}
				_ => first({})
			}
			Field(name) | OptField(name) => Translate.field(first({})?, name, ty, env)
			Index(position) => match first({})? {
				Pair(left, right) => if (position == 0) Ok(left) else Ok(right)
				_ => Err(Unsupported("only the pair of a row and its edges has positions `.0` and `.1`"))
			}
			Payload(tag, k) => Translate.payload(first({})?, tag, k, ty)
			Switch(sw) => Translate.switch(sw.arms.map(|a| a.key), sw.joins.len(), sw.outputs.len(), args, env)
			And(_) => Translate.connective("AND", args, env)
			Or(_) => Translate.connective("OR", args, env)
			ForRange(_) | ForList(_) | Loop(_) => Err(Translate.no_loop)
			Crash => Err(Unsupported("a clause cannot crash"))
			Derived(method, _) => Err(Unsupported("`${method}` is derived by the compiler and has no SurrealQL form; compare fields, or `match` on a union"))
		}
	}

	connective : Str, List(Code.Tree), Env -> Try(Binding, Ql.Error)
	connective = |word, args, env| {
		parts = args.map_try(|a| Translate.arg(a, env))?
		Ok(Binding.Infix(Str.join_with(parts, " ${word} ")))
	}

	field : Binding, Str, Code.Ty, Env -> Try(Binding, Ql.Error)
	field = |holder, name, ty, env| match holder {
		Row(r) => {
			spelled = Translate.spell_name(name, r.edge)
			path = if (r.at.is_empty()) spelled else "${r.at}.${if (r.edge) spelled else Ql.member(name)}"
			if name == "id" and r.of != Obj {
				# The key of a record: `c.id` is the `ada` of `customer:ada`.
				Ok(Binding.Expr("record::id(${if (r.of == Ref) r.at else path})"))
			} else {
				Ok(Translate.at(path, ty))
			}
		}
		Params => {
			spell_param = env.param
			Ok(Translate.at(spell_param(name), ty))
		}
		Fields(fields) => match fields.find_first(|f| f.name == name) {
			Ok(f) => Ok(f.binding)
			Err(_) => Err(Unsupported("this record has no `${name}`"))
		}
		Pair(_, _) => Err(Unsupported("a pair has no `${name}`; take `.0` or `.1` first"))
		Group(_) => Err(Unsupported("a group's rows have no single `${name}`; aggregate them"))
		_ => Err(Unsupported("`${name}` is read from a value that is not a record"))
	}

	## A field name as SurrealDB names it: an edge's `from` and `to` are `in`
	## and `out`, because `in` is a Roc keyword.
	spell_name : Str, Bool -> Str
	spell_name = |name, edge|
		if edge and name == "from" {
			"in"
		} else if edge and name == "to" {
			"out"
		} else {
			Ql.ident(name)
		}

	## A union literal in the union encoding of `Encode`: `'Cash'`,
	## `{ kind: 'Card', last4: .. }`, `{ kind: 'C', value: .. }`,
	## `{ kind: 'D', _0: .., _1: .. }`.
	tag : Str, List(Code.Tree), Env -> Try(Binding, Ql.Error)
	tag = |name, args, env| {
		kind = "kind: ${Ql.quote(name)}"
		match args {
			[] => Ok(Binding.Expr(Ql.quote(name)))
			[Op({ ty: payload_ty, .. }) as only] if Translate.is_record(payload_ty) => match Translate.eval(only, env)? {
				Fields(fields) => {
					parts = fields.map_try(|f| Ok("${Ql.member(f.name)}: ${Translate.text(f.binding)?}"))?
					Ok(Binding.Expr("{ ${Str.join_with(List.concat([kind], parts), ", ")} }"))
				}
				_ => Err(Unsupported("the payload of `${name}` is a record the clause does not build field by field"))
			}
			[only] => Ok(Binding.Expr("{ ${kind}, value: ${Translate.expr(only, env)?} }"))
			_ => {
				parts = args.map_with_index(|a, k| (a, k)).map_try(|(a, k)| Ok("_${k.to_str()}: ${Translate.expr(a, env)?}"))?
				Ok(Binding.Expr("{ ${Str.join_with(List.concat([kind], parts), ", ")} }"))
			}
		}
	}

	## A nominal value written in the clause. An `Id` or a `Datetime` of
	## literals is its SurrealQL literal; a user nominal is its backing.
	wrap : Str, List(Code.Tree), Env -> Try(Binding, Ql.Error)
	wrap = |name, args, env| {
		inner = match args {
			[one] => one
			_ => return Err(Unsupported("a nominal value with no backing"))
		}
		match Translate.cut(name) {
			Id => match (Translate.record_field(inner, "table"), Translate.record_field(inner, "key")) {
				(Ok(Op({ op: Lit(Str(table)), .. })), Ok(Op({ op: Lit(Str(key)), .. }))) => Ok(Binding.Expr(Ql.record_id(table, key)))
				(Ok(table), Ok(key)) => Ok(Binding.Expr("type::record(${Translate.expr(table, env)?}, ${Translate.expr(key, env)?})"))
				_ => Err(Unsupported("an id built without its table and key"))
			}
			Datetime => match Translate.record_field(inner, "iso") {
				Ok(Op({ op: Lit(Str(iso)), .. })) => Ok(Binding.Expr(Ql.literal(Ql.Value.Datetime(iso))))
				Ok(other) => Ok(Binding.Expr("<datetime>${Translate.arg(other, env)?}"))
				Err(_) => Err(Unsupported("a datetime built without its text"))
			}
			Link => Err(Unsupported("a `Link` written in a clause has no SurrealQL form; compare `link.id()` with an `Id`"))
			Duration => match Translate.record_field(inner, "nanos") {
				Ok(nanos) => Ok(Binding.Expr(Translate.call("duration::from_nanos", [Translate.expr(nanos, env)?])))
				Err(_) => Err(Unsupported("a duration built without its nanoseconds"))
			}
			Other =>
				if name == "Builtin.Try" {
					Err(Unsupported("a `Try` built in a clause has no SurrealQL form"))
				} else {
					Translate.eval(inner, env)
				}
		}
	}

	record_field : Code.Tree, Str -> Try(Code.Tree, [Missing])
	record_field = |tree, name| match tree {
		Op({ op: Record(names), args, .. }) => match List.map2(names, args, |n, a| { n, a }).find_first(|p| p.n == name) {
			Ok(p) => Ok(p.a)
			Err(_) => Err(Missing)
		}
		_ => Err(Missing)
	}

	## A payload read, by the union payload rule of `Encode`: a record
	## payload is the union object itself, one other payload is `value`,
	## several are `_0`, `_1`, ...
	payload : Binding, Str, U64, Code.Ty -> Try(Binding, Ql.Error)
	payload = |holder, tag_name, k, ty| match holder {
		Maybe(s) if tag_name == "Ok" => Ok(Translate.at(s, ty))
		Union(u) => match u.variants.find_first(|v| v.name == tag_name) {
			Ok({ payloads: [only], .. }) =>
				if Translate.is_record(only) {
					Ok(Binding.Row({ at: u.at, of: Obj, edge: Bool.False }))
				} else {
					Ok(Translate.at("${u.at}.value", ty))
				}
			Ok(_) => Ok(Translate.at("${u.at}._${k.to_str()}", ty))
			Err(_) => Err(Unsupported("the union has no `${tag_name}`"))
		}
		_ => Err(Unsupported("`${tag_name}` is read from a value that is not a union"))
	}

	# ------------------------------------------------------------ branches

	## A branch: a `match` on a union, a test of an optional value, a `Bool`
	## test, or a test of a value against literals (a guard arrives as one).
	switch : List(Code.Key), U64, U64, List(Code.Tree), Env -> Try(Binding, Ql.Error)
	switch = |keys, joins, outputs, args, env| {
		if joins != 0 or outputs != 1 {
			return Err(Unsupported("a clause cannot leave early; every branch delivers its value"))
		}
		scrutinee = match args.first() {
			Ok(tree) => tree
			Err(_) => return Err(Unsupported("a branch with nothing to test"))
		}
		arms = List.map2(keys, args.drop_first(1), |key, tree| { key, tree })
		arm = |name| match arms.find_first(|a| Translate.key_is(a.key, name)) {
			Ok(found) => Translate.expr(found.tree, env)
			Err(_) => Err(Unsupported("a branch in a clause has no `${name}` arm"))
		}
		match Translate.eval(scrutinee, env)? {
			Maybe(s) => {
				present = arm("Ok")?
				absent = arm("Err")?
				if present == s {
					fallback = match arms.find_first(|a| Translate.key_is(a.key, "Err")) {
						Ok(found) => Translate.arg(found.tree, env)?
						Err(_) => absent
					}
					Ok(Binding.Infix("${s} ?? ${fallback}"))
				} else {
					Ok(Binding.Expr("(IF ${s} IS NONE THEN ${absent} ELSE ${present} END)"))
				}
			}
			Union(u) => {
				tests = arms.map_try(
					|a| match a.key {
						Tag(name) => match u.variants.find_first(|v| v.name == name) {
							Ok({ payloads: [], .. }) => Ok({ test: "${u.at} = ${Ql.quote(name)}", value: Translate.expr(a.tree, env)? })
							Ok(_) => Ok({ test: "${u.at}.kind = ${Ql.quote(name)}", value: Translate.expr(a.tree, env)? })
							Err(_) => Err(Unsupported("the union has no `${name}`"))
						}
						_ => Err(Unsupported("a union is matched by its tags"))
					},
				)?
				Ok(Translate.chain(tests, Free))
			}
			scalar => {
				s = Translate.operand(scalar)?
				if keys.any(|k| Translate.key_is(k, "True")) {
					Ok(Translate.chain([{ test: Translate.text(scalar)?, value: arm("True")? }, { test: "", value: arm("False")? }], Free))
				} else {
					tests = arms.map_try(
						|a| match a.key {
							Lit(literal) => Ok({ test: "${s} = ${Translate.literal(literal)?}", value: Translate.expr(a.tree, env)? })
							Default => Ok({ test: "", value: Translate.expr(a.tree, env)? })
							_ => Err(Unsupported("a list pattern has no SurrealQL form"))
						},
					)?
					Ok(Translate.chain(tests, Fixed))
				}
			}
		}
	}

	## `IF .. THEN .. ELSE IF .. ELSE .. END`, from arms whose tests exclude
	## one another. The `ELSE` value is the one most arms give (the last such
	## arm on a tie), and every arm that gives it needs no test. With `Fixed`,
	## the last arm is the `ELSE`, because it is the `Default` of a literal
	## test and has no test of its own.
	chain : List({ test : Str, value : Str }), [Free, Fixed] -> Binding
	chain = |tests, choice| {
		count_of = |value| tests.count_if(|t| t.value == value)
		fallback = match choice {
			Fixed => tests.last().map_ok(|t| t.value) ?? ""
			Free => tests.fold("", |best, t| if (count_of(t.value) >= count_of(best)) t.value else best)
		}
		tested = tests.keep_if(|t| t.value != fallback)
		if tested.is_empty() {
			Binding.Expr(fallback)
		} else {
			branches = Str.join_with(tested.map(|t| "IF ${t.test} THEN ${t.value}"), " ELSE ")
			Binding.Expr("(${branches} ELSE ${fallback} END)")
		}
	}

	key_is : Code.Key, Str -> Bool
	key_is = |key, name| match key {
		Tag(tag_name) => tag_name == name
		Lit(Bool(flag)) => (if (flag) "True" else "False") == name
		Lit(_) | Len(_) | AtLeast(_) | Default => Bool.False
	}

	# ------------------------------------------------------------ builtins

	## The builtins and cut functions a clause may call, by owner and method.
	prim : Str, Str, List(Code.Tree), Code.Ty, Env -> Try(Binding, Ql.Error)
	prim = |owner, method, args, ty, env| {
		sql = |node| Translate.expr(node, env)
		opd = |node| Translate.arg(node, env)
		match (Translate.cut(owner), method, args) {
			(Link, "get", [link]) => match Translate.eval(link, env)? {
				Expr(path) => Ok(Binding.Row({ at: path, of: Ref, edge: Bool.False }))
				_ => Err(Unsupported("`get` traverses a stored link"))
			}
			(Link, "id", [link]) => Ok(Binding.Expr(sql(link)?))
			(Id, "is_eq", [a, b]) => Ok(Binding.Infix("${opd(a)?} = ${opd(b)?}"))
			(Id, "key", [id]) => Ok(Binding.Expr("record::id(${sql(id)?})"))
			(Id, "table", [id]) => Ok(Binding.Expr("record::tb(${sql(id)?})"))
			(Datetime, _, [lhs, rhs]) => Translate.binary(owner, method, lhs, rhs, env)
			(Other, _, _) if owner.starts_with("Surreal.") => Translate.library(owner, method, args, ty, env)
			(Other, _, _) => Translate.builtin(owner, method, args, env)
			_ => Err(Unsupported("`${owner}.${method}` has no SurrealQL form"))
		}
	}

	builtin : Str, Str, List(Code.Tree), Env -> Try(Binding, Ql.Error)
	builtin = |owner, method, args, env| {
		sql = |node| Translate.expr(node, env)
		opd = |node| Translate.arg(node, env)
		plain = |node| Translate.plain_list(node, env)
		string_fn = |name, s, x| Ok(Binding.Expr("string::${name}(${sql(s)?}, ${sql(x)?})"))
		whole = owner.starts_with("Num.I") or owner.starts_with("Num.U")
		dec = owner == "Num.Dec"
		match ("${owner}.${method}", args) {
			("Str.concat", _) => Ok(Binding.Infix(Str.join_with(args.map_try(opd)?, " + ")))
			("Str.starts_with", [s, x]) => string_fn("starts_with", s, x)
			("Str.ends_with", [s, x]) => string_fn("ends_with", s, x)
			("Str.contains", [s, x]) => string_fn("contains", s, x)
			("Str.is_empty", [s]) => Ok(Binding.Infix("${opd(s)?} = ''"))
			("Str.to_str", [s]) => Translate.eval(s, env)
			("Str.is_eq", [a, b]) => match Translate.moments(a, b, env)? {
				Moments(pair) => Ok(Binding.Infix("${pair.left} = ${pair.right}"))
				Texts => Translate.binary(owner, method, a, b, env)
			}
			("Str.repeat", [s, n]) => Ok(Binding.Expr(Translate.call("string::repeat", [sql(s)?, sql(n)?])))
			# `with_prefix(s, p)` is `p + s`.
			("Str.with_prefix", [s, p]) => Ok(Binding.Infix("${opd(p)?} + ${opd(s)?}"))
			("Str.join_with", [list, x]) => Ok(Binding.Expr(Translate.call("array::join", [plain(list)?, sql(x)?])))
			# Equal prefixes in bytes are equal in characters, so `string::len` cuts at the same place.
			("Str.drop_prefix", [s, p]) =>
				Ok(Binding.Expr("(IF string::starts_with(${sql(s)?}, ${sql(p)?}) THEN string::slice(${sql(s)?}, string::len(${sql(p)?})) ELSE ${sql(s)?} END)"))
			("Str.drop_suffix", [s, p]) =>
				Ok(Binding.Expr("(IF string::ends_with(${sql(s)?}, ${sql(p)?}) THEN string::slice(${sql(s)?}, 0, string::len(${sql(s)?}) - string::len(${sql(p)?})) ELSE ${sql(s)?} END)"))
			# `string::len` counts characters, so the byte count goes through `<bytes>`.
			("Str.count_utf8_bytes", [s]) => Ok(Binding.Expr("bytes::len(<bytes>${opd(s)?})"))
			# `string::trim` keeps U+200E and U+200F, which Roc removes.
			("Str.trim", [s]) => Ok(Binding.Expr("string::replace(${sql(s)?}, /^${Translate.blank}|${Translate.blank}$/, '')"))
			("Str.trim_start", [s]) => Ok(Binding.Expr("string::replace(${sql(s)?}, /^${Translate.blank}/, '')"))
			("Str.trim_end", [s]) => Ok(Binding.Expr("string::replace(${sql(s)?}, /${Translate.blank}$/, '')"))
			("Str.with_ascii_uppercased", [s]) => Ok(Binding.Expr(Translate.ascii_case(sql(s)?, "a", "z", "uppercase")))
			("Str.with_ascii_lowercased", [s]) => Ok(Binding.Expr(Translate.ascii_case(sql(s)?, "A", "Z", "lowercase")))
			("Str.caseless_ascii_equals", [s, x]) =>
				Ok(Binding.Infix("${Translate.ascii_case(sql(s)?, "A", "Z", "lowercase")} = ${Translate.ascii_case(sql(x)?, "A", "Z", "lowercase")}"))
			# `string::split` with an empty separator cuts every character, and Roc gives the whole text.
			("Str.split_on", [s, x]) => {
				split = "string::split(${sql(s)?}, ${sql(x)?})"
				pieces = match Translate.str_lit(x) {
					Ok("") => "[${sql(s)?}]"
					Ok(_) => split
					Err(_) => "(IF ${opd(x)?} = '' THEN [${sql(s)?}] ELSE ${split} END)"
				}
				Ok(Binding.ListOf({ at: pieces, edges: Bool.False }))
			}
			# `string::replace` with an empty needle puts the replacement between all characters, and Roc keeps the text.
			("Str.replace_each", [s, x, y]) => {
				replace = "string::replace(${sql(s)?}, ${sql(x)?}, ${sql(y)?})"
				match Translate.str_lit(x) {
					Ok("") => Translate.eval(s, env)
					Ok(_) => Ok(Binding.Expr(replace))
					Err(_) => Ok(Binding.Expr("(IF ${opd(x)?} = '' THEN ${sql(s)?} ELSE ${replace} END)"))
				}
			}
			("Try.is_ok", [m]) => Translate.none_test(m, "IS NOT NONE", env)
			("Try.is_err", [m]) => Translate.none_test(m, "IS NONE", env)
			("Try.ok_or", [m, d]) => match Translate.eval(m, env)? {
				Maybe(s) => Ok(Binding.Infix("${s} ?? ${opd(d)?}"))
				_ => Err(Unsupported("a clause gives a default only to an optional value"))
			}
			("List.len", [list]) => Translate.count(list, env)
			("List.is_empty", [list]) => Ok(Binding.Infix("${Translate.list_at(list, env)?}.len() = 0"))
			("List.contains", [list, x]) => Ok(Binding.Infix("${Translate.list_at(list, env)?} CONTAINS ${opd(x)?}"))
			("List.sum", [list]) => Translate.sum(list, env)
			("List.any", [list, f]) => Translate.lambda(list, f, "any", env)
			("List.all", [list, f]) => Translate.lambda(list, f, "all", env)
			("List.map", [list, f]) => Translate.lambda(list, f, "map", env)
			("List.keep_if", [list, f]) => Translate.lambda(list, f, "filter", env)
			("List.drop_if", [list, f]) => Translate.lambda(list, f, "drop", env)
			("List.count_if", [list, f]) => Translate.lambda(list, f, "count", env)
			("List.find_first", [list, f]) => Translate.lambda(list, f, "find", env)
			# An empty list gives `NONE` here, and a float `NULL` from `math::max`.
			("List.first", [list]) => Ok(Binding.Maybe(Translate.call("array::first", [plain(list)?])))
			("List.last", [list]) => Ok(Binding.Maybe(Translate.call("array::last", [plain(list)?])))
			("List.min", [list]) => Ok(Binding.Maybe(Translate.call("array::min", [plain(list)?])))
			("List.max", [list]) => Ok(Binding.Maybe(Translate.call("array::max", [plain(list)?])))
			("List.get", [list, i]) => Ok(Binding.Maybe(Translate.call("array::at", [plain(list)?, sql(i)?])))
			("List.take_first", [list, n]) => {
				source = Translate.list_parts(list, env)?
				Ok(Binding.ListOf({ at: Translate.call("array::slice", [source.at, "0", sql(n)?]), edges: source.edges }))
			}
			("List.drop_first", [list, n]) => {
				source = Translate.list_parts(list, env)?
				Ok(Binding.ListOf({ at: Translate.call("array::slice", [source.at, sql(n)?]), edges: source.edges }))
			}
			("List.rev", [list]) => {
				source = Translate.list_parts(list, env)?
				Ok(Binding.ListOf({ at: Translate.call("array::reverse", [source.at]), edges: source.edges }))
			}
			("List.concat", [a, b]) => Ok(Binding.ListOf({ at: Translate.call("array::concat", [plain(a)?, plain(b)?]), edges: Bool.False }))
			("List.append", [list, x]) => Ok(Binding.ListOf({ at: Translate.call("array::append", [plain(list)?, sql(x)?]), edges: Bool.False }))
			("List.prepend", [list, x]) => Ok(Binding.ListOf({ at: Translate.call("array::prepend", [plain(list)?, sql(x)?]), edges: Bool.False }))
			# `List.join` flattens one level, as `array::flatten` does.
			("List.join", [list]) => Ok(Binding.ListOf({ at: Translate.call("array::flatten", [plain(list)?]), edges: Bool.False }))
			("List.is_eq", [a, b]) => Ok(Binding.Infix("${plain(a)?} = ${plain(b)?}"))
			("Bool.not", [x]) => match x {
				Op({ op: Prim({ method: "is_eq", .. }), args: [lhs, rhs], .. }) => match Translate.moments(lhs, rhs, env)? {
					Moments(pair) => Ok(Binding.Infix("${pair.left} != ${pair.right}"))
					Texts => Ok(Binding.Infix("${opd(lhs)?} != ${opd(rhs)?}"))
				}
				_ => Ok(Binding.Infix("!${opd(x)?}"))
			}
			("Num.Dec.to_i64_try", [d]) => {
				truncated = "(IF ${opd(d)?} >= 0 THEN math::floor(${sql(d)?}) ELSE math::ceil(${sql(d)?}) END)"
				Ok(Binding.Maybe("(IF ${opd(d)?} > -9223372036854775809dec AND ${opd(d)?} < 9223372036854775808dec THEN <int>${truncated} ELSE NONE END)"))
			}
			(_, [n]) if whole and method.starts_with("to_") and method.ends_with("_try") => Translate.int_try(method, n, env)
			(_, [n]) if owner.starts_with("Num.") => match method {
				"negate" => Ok(Binding.Infix("-${opd(n)?}"))
				"abs" => Ok(Binding.Expr("math::abs(${sql(n)?})"))
				"to_dec" => Ok(Binding.Expr("<decimal>${opd(n)?}"))
				"to_f64" | "to_f32" => Ok(Binding.Expr("<float>${opd(n)?}"))
				# SurrealDB integers are already `int` (I64). The conversions that Roc allows without a check are the identity.
				"to_i16" | "to_i32" | "to_i64" | "to_i128" | "to_u16" | "to_u32" | "to_u64" | "to_u128" | "to_i64_wrap" if whole => Translate.eval(n, env)
				"to_i64" | "to_i64_wrap" =>
					Err(Unsupported("`${method}` on `${owner}` cuts the fraction, and SurrealDB's `<int>` raises an error on one; use `to_i64_try`"))
				"from_str" => Err(Unsupported("`from_str` accepts more forms than SurrealDB casts; parse in Roc and store a number"))
				"is_zero" if whole or dec => Ok(Binding.Infix("${opd(n)?} = 0"))
				"is_negative" if whole or dec => Ok(Binding.Infix("${opd(n)?} < 0"))
				"is_positive" if whole or dec => Ok(Binding.Infix("${opd(n)?} > 0"))
				"is_even" if whole => Ok(Binding.Infix("${opd(n)?} % 2 = 0"))
				"is_odd" if whole => Ok(Binding.Infix("${opd(n)?} % 2 != 0"))
				"to_str" if whole => Ok(Binding.Expr("<string>${opd(n)?}"))
				"to_str" if dec => Err(Unsupported("`to_str` on `Dec` prints differently: Roc `3.0`, SurrealDB `3`; compare the number"))
				# SurrealDB `math::round` rounds a tie to even, and Roc rounds it away from zero.
				"round" if dec =>
					Ok(Binding.Expr("(IF ${opd(n)?} >= 0 THEN math::floor(${opd(n)?} + 0.5dec) ELSE math::ceil(${opd(n)?} - 0.5dec) END)"))
				"floor" if dec => Ok(Binding.Expr("math::floor(${sql(n)?})"))
				"ceiling" if dec => Ok(Binding.Expr("math::ceil(${sql(n)?})"))
				# SurrealDB has no `math::trunc`.
				"trunc" if dec => Ok(Binding.Expr("(IF ${opd(n)?} >= 0 THEN math::floor(${sql(n)?}) ELSE math::ceil(${sql(n)?}) END)"))
				"is_zero" | "is_negative" | "is_positive" | "to_str" => Err(Translate.float_note(owner, method))
				_ => Err(Unsupported("`${owner}.${method}` has no SurrealQL form"))
			}
			(_, [a, b]) if owner.starts_with("Num.") => match method {
				"max" | "min" if whole or dec => Ok(Binding.Expr("math::${method}([${sql(a)?}, ${sql(b)?}])"))
				"pow" if whole => Ok(Binding.Expr(Translate.call("math::pow", [sql(a)?, sql(b)?])))
				"pow" if dec => Err(Unsupported("`pow` on `Dec` keeps 18 digits in Roc and 28 in SurrealDB; the two differ"))
				# `mod_by` is the floored modulus: the sign of the divisor.
				"mod_by" if whole => Ok(Binding.Expr("(((${opd(a)?} % ${opd(b)?}) + ${opd(b)?}) % ${opd(b)?})"))
				"is_multiple_of" if whole =>
					if Translate.is_nonzero(b) {
						Ok(Binding.Infix("${opd(a)?} % ${opd(b)?} = 0"))
					} else {
						Ok(Binding.Expr("(IF ${opd(b)?} = 0 THEN ${opd(a)?} = 0 ELSE ${opd(a)?} % ${opd(b)?} = 0 END)"))
					}
				"max" | "min" | "pow" => Err(Translate.float_note(owner, method))
				_ => Translate.binary(owner, method, a, b, env)
			}
			(_, [lhs, rhs]) if owner == "Str" => Translate.binary(owner, method, lhs, rhs, env)
			_ => Err(Unsupported("`${owner}.${method}` has no SurrealQL form"))
		}
	}

	## The operands of an equality where one text is the text of a datetime. The datetimes are compared,
	## because SurrealDB prints a fraction with 3, 6 or 9 digits and Roc does not. The other text must be a literal.
	moments : Code.Tree, Code.Tree, Env -> Try([Moments({ left : Str, right : Str }), Texts], Ql.Error)
	moments = |lhs, rhs, env| {
		not_literal = Unsupported("the text of a datetime is compared with a datetime or a literal; SurrealDB prints a fraction with 3, 6 or 9 digits, so other texts differ")
		literal = |tree| match Translate.str_lit(tree) {
			Ok(iso) => Ok(Ql.literal(Ql.Value.Datetime(iso)))
			Err(_) => Err(not_literal)
		}
		match (Translate.eval(lhs, env)?, Translate.eval(rhs, env)?) {
			(Moment(a), Moment(b)) => Ok(Moments({ left: a, right: b }))
			(Moment(a), _) => Ok(Moments({ left: a, right: literal(rhs)? }))
			(_, Moment(b)) => Ok(Moments({ left: b, right: literal(lhs)? }))
			_ => Ok(Texts)
		}
	}

	## The package functions of `Surreal` that are one SurrealQL function of the same arguments.
	functions : List({ owner : Str, method : Str, surql : Str })
	functions = [
		{ owner: "Surreal.Text", method: "is_email", surql: "string::is_email" },
		{ owner: "Surreal.Text", method: "is_url", surql: "string::is_url" },
		{ owner: "Surreal.Text", method: "is_domain", surql: "string::is_domain" },
		{ owner: "Surreal.Text", method: "is_ip", surql: "string::is_ip" },
		{ owner: "Surreal.Text", method: "is_ipv4", surql: "string::is_ipv4" },
		{ owner: "Surreal.Text", method: "is_ipv6", surql: "string::is_ipv6" },
		{ owner: "Surreal.Text", method: "is_uuid", surql: "string::is_uuid" },
		{ owner: "Surreal.Text", method: "is_ulid", surql: "string::is_ulid" },
		{ owner: "Surreal.Text", method: "is_semver", surql: "string::is_semver" },
		{ owner: "Surreal.Text", method: "is_alpha", surql: "string::is_alpha" },
		{ owner: "Surreal.Text", method: "is_alphanum", surql: "string::is_alphanum" },
		{ owner: "Surreal.Text", method: "is_numeric", surql: "string::is_numeric" },
		{ owner: "Surreal.Text", method: "is_latitude", surql: "string::is_latitude" },
		{ owner: "Surreal.Text", method: "is_longitude", surql: "string::is_longitude" },
		{ owner: "Surreal.Text", method: "is_datetime", surql: "string::is_datetime" },
		{ owner: "Surreal.Text", method: "matches", surql: "string::matches" },
		{ owner: "Surreal.Text", method: "is_ascii", surql: "string::is_ascii" },
		{ owner: "Surreal.Text", method: "is_hexadecimal", surql: "string::is_hexadecimal" },
		{ owner: "Surreal.Text", method: "similarity_jaro", surql: "string::similarity::jaro" },
		{ owner: "Surreal.Text", method: "similarity_jaro_winkler", surql: "string::similarity::jaro_winkler" },
		{ owner: "Surreal.Text", method: "distance_levenshtein", surql: "string::distance::levenshtein" },
		{ owner: "Surreal.Text", method: "distance_damerau_levenshtein", surql: "string::distance::damerau_levenshtein" },
		{ owner: "Surreal.Text", method: "distance_normalized_levenshtein", surql: "string::distance::normalized_levenshtein" },
		{ owner: "Surreal.Hash", method: "sha256", surql: "crypto::sha256" },
		{ owner: "Surreal.Hash", method: "blake3", surql: "crypto::blake3" },
		{ owner: "Surreal.Hash", method: "md5", surql: "crypto::md5" },
		{ owner: "Surreal.Hash", method: "sha1", surql: "crypto::sha1" },
		{ owner: "Surreal.Hash", method: "sha512", surql: "crypto::sha512" },
		{ owner: "Surreal.Array", method: "distinct", surql: "array::distinct" },
		{ owner: "Surreal.Array", method: "union", surql: "array::union" },
		{ owner: "Surreal.Array", method: "intersect", surql: "array::intersect" },
		{ owner: "Surreal.Array", method: "complement", surql: "array::complement" },
		{ owner: "Surreal.Time", method: "now", surql: "time::now" },
		{ owner: "Surreal.Time", method: "floor", surql: "time::floor" },
		{ owner: "Surreal.Time", method: "ceil", surql: "time::ceil" },
		{ owner: "Surreal.Time", method: "round", surql: "time::round" },
		{ owner: "Surreal.Time", method: "wday", surql: "time::wday" },
		{ owner: "Surreal.Time", method: "yday", surql: "time::yday" },
		{ owner: "Surreal.Time", method: "week", surql: "time::week" },
		{ owner: "Surreal.Time", method: "unix", surql: "time::unix" },
		{ owner: "Surreal.Time", method: "unix_millis", surql: "time::millis" },
		{ owner: "Surreal.Time", method: "unix_micros", surql: "time::micros" },
		{ owner: "Surreal.Time", method: "nano", surql: "time::nano" },
		{ owner: "Surreal.Time", method: "format", surql: "time::format" },
		{ owner: "Surreal.Time", method: "from_unix", surql: "time::from_unix" },
		{ owner: "Surreal.Time", method: "year", surql: "time::year" },
		{ owner: "Surreal.Time", method: "month", surql: "time::month" },
		{ owner: "Surreal.Time", method: "day", surql: "time::day" },
		{ owner: "Surreal.Time", method: "hour", surql: "time::hour" },
		{ owner: "Surreal.Time", method: "minute", surql: "time::minute" },
		{ owner: "Surreal.Time", method: "second", surql: "time::second" },
		{ owner: "Surreal.Rand", method: "ulid", surql: "rand::ulid" },
		{ owner: "Surreal.Rand", method: "int", surql: "rand::int" },
		{ owner: "Surreal.Math", method: "mean", surql: "math::mean" },
		{ owner: "Surreal.Math", method: "median", surql: "math::median" },
		{ owner: "Surreal.Math", method: "stddev", surql: "math::stddev" },
		{ owner: "Surreal.Math", method: "variance", surql: "math::variance" },
	]

	## A function of `Surreal.Text`, `Hash`, `Array`, `Time`, `Math` or `Rand`. The few that
	## are not one SurrealQL call of their arguments have their own rule.
	library : Str, Str, List(Code.Tree), Code.Ty, Env -> Try(Binding, Ql.Error)
	library = |owner, method, args, ty, env| {
		sql = |node| Translate.expr(node, env)
		opd = |node| Translate.arg(node, env)
		name = "${owner}.${method}"
		if owner == "Surreal.Rand" and !env.random {
			return Err(Unsupported("`${name}` gives a new value on every call: use it in a default, a computed field or an update"))
		}
		match (name, args) {
			# A `uuid` is its own type in SurrealDB, and a `string` column refuses it.
			("Surreal.Rand.uuid", []) => Ok(Binding.Expr("<string>rand::uuid()"))
			# The unit is a tag that the clause writes: `Month` is `'month'`.
			("Surreal.Time.group", [time, Op({ op: Tag(unit), args: [], .. })]) => Ok(Binding.Expr(Translate.call("time::group", [sql(time)?, Ql.quote(unit.with_ascii_lowercased())])))
			("Surreal.Time.group", _) => Err(Unsupported("the unit of `Time.group` is a tag that the clause writes, as `Month`"))
			("Surreal.Time.plus", [time, span]) => Ok(Binding.Infix("${opd(time)?} + ${opd(span)?}"))
			("Surreal.Time.minus", [time, span]) => Ok(Binding.Infix("${opd(time)?} - ${opd(span)?}"))
			# `math::percentile` of a group's rows gives `NULL` in SurrealDB.
			("Surreal.Math.percentile", [list, percent]) => {
				values = Translate.aggregate_list(list, env)?
				if values.grouped {
					Err(Unsupported("`math::percentile` is not an aggregate in SurrealDB; use it on a list"))
				} else {
					Ok(Binding.Expr(Translate.call("math::percentile", [values.text, sql(percent)?])))
				}
			}
			_ => match Translate.functions.find_first(|f| f.owner == owner and f.method == method) {
				Ok(found) =>
					if owner == "Surreal.Math" {
						match args {
							[list] => Translate.aggregate_arg(found.surql, list, env)
							_ => Err(Unsupported("`${name}` takes a list"))
						}
					} else {
						Ok(Translate.at(Translate.call(found.surql, args.map_try(sql)?), ty))
					}
				Err(_) => Err(Unsupported("`${name}` has no SurrealQL form"))
			}
		}
	}

	## A call to a SurrealQL function: `name(a, b)`.
	call : Str, List(Str) -> Str
	call = |name, parts| "${name}(${Str.join_with(parts, ", ")})"

	## The characters that Roc's `Str.trim` removes, as a SurrealQL regex class.
	blank : Str
	blank = "[\\s\\u{200E}\\u{200F}]+"

	## The text with the letters from `low` to `high` changed by a SurrealQL
	## function. It works per character, because `string::uppercase` also
	## changes the letters outside ASCII, and Roc does not.
	ascii_case : Str, Str, Str, Str -> Str
	ascii_case = |input, low, high, fn|
		"array::join(string::split(${input}, '').map(|$ch| IF $ch >= '${low}' AND $ch <= '${high}' THEN string::${fn}($ch) ELSE $ch END), '')"

	## The text of a string literal, when the tree is one.
	str_lit : Code.Tree -> Try(Str, [NotLiteral])
	str_lit = |tree| match tree {
		Op({ op: Lit(Str(found)), .. }) => Ok(found)
		_ => Err(NotLiteral)
	}

	## Whether a tree is an integer literal other than zero.
	is_nonzero : Code.Tree -> Bool
	is_nonzero = |tree| match tree {
		Op({ op: Lit(Int(n, _)), .. }) => n != 0
		_ => Bool.False
	}

	## What a float operation differs in, for a refusal.
	float_note : Str, Str -> Ql.Error
	float_note = |owner, method| Unsupported("`${method}` on `${owner}` differs from SurrealDB for NaN, -0.0 and how a float prints; use `Dec` or an integer")

	## A conversion `to_<int>_try` of an integer: `NONE` when the value is
	## outside the range of the target. A value of a SurrealDB int is always
	## inside the range that has no bound.
	int_try : Str, Code.Tree, Env -> Try(Binding, Ql.Error)
	int_try = |method, n, env| {
		target = method.drop_prefix("to_").drop_suffix("_try")
		(lo, hi) = match Translate.int_range(target) {
			Ok(range) => range
			Err(_) => return Err(Unsupported("`${method}` has no SurrealQL form"))
		}
		value = Translate.arg(n, env)?
		tests = List.concat(if (lo.is_empty()) [] else ["${value} >= ${lo}"], if (hi.is_empty()) [] else ["${value} <= ${hi}"])
		if tests.is_empty() {
			Ok(Binding.Maybe(value))
		} else {
			Ok(Binding.Maybe("(IF ${Str.join_with(tests, " AND ")} THEN ${Translate.expr(n, env)?} ELSE NONE END)"))
		}
	}

	## The bounds of an integer type by its Roc name. A bound is empty when
	## no value of a SurrealDB int is beyond it.
	int_range : Str -> Try((Str, Str), [NotInt])
	int_range = |name| match name {
		"i8" => Ok(("-128", "127"))
		"i16" => Ok(("-32768", "32767"))
		"i32" => Ok(("-2147483648", "2147483647"))
		"i64" | "i128" => Ok(("", ""))
		"u8" => Ok(("0", "255"))
		"u16" => Ok(("0", "65535"))
		"u32" => Ok(("0", "4294967295"))
		"u64" | "u128" => Ok(("0", ""))
		_ => Err(NotInt)
	}

	none_test : Code.Tree, Str, Env -> Try(Binding, Ql.Error)
	none_test = |tree, test, env| match Translate.eval(tree, env)? {
		Maybe(s) => Ok(Binding.Infix("${s} ${test}"))
		_ => Err(Unsupported("a clause tests presence only of an optional value"))
	}

	## The list a list operation runs over, as the start of a method chain.
	list_at : Code.Tree, Env -> Try(Str, Ql.Error)
	list_at = |tree, env| Ok(Translate.list_parts(tree, env)?.at)

	## The same, with whether its elements are the edges of a relation.
	list_parts : Code.Tree, Env -> Try({ at : Str, edges : Bool }, Ql.Error)
	list_parts = |tree, env| match Translate.eval(tree, env)? {
		ListOf(list) => Ok(list)
		Group(_) | Column(_) => Err(Unsupported("a group's rows take `len`, `keep_if(..).len()` and `map(..).sum()`"))
		other => Ok({ at: Translate.operand(other)?, edges: Bool.False })
	}

	## A list of values. The edges of a relation are records with `in` and
	## `out`, so an operation that gives one element or a new list refuses them.
	plain_list : Code.Tree, Env -> Try(Str, Ql.Error)
	plain_list = |tree, env| {
		source = Translate.list_parts(tree, env)?
		if source.edges {
			Err(Unsupported("the edges of a relation take `keep_if`, `map`, `any`, `all` and `len`"))
		} else {
			Ok(source.at)
		}
	}

	## `len`: over a group's rows `count()`, or `count(f)` after `keep_if(f)`;
	## over a list `.len()`.
	count : Code.Tree, Env -> Try(Binding, Ql.Error)
	count = |list, env| match list {
		Op({ op: Prim({ owner: "List", method: "keep_if" }), args: [rows, Op({ op: Closure(row), args: captures, .. })], .. }) =>
			match Translate.eval(rows, env)? {
				Group(source) => Ok(Binding.Expr("count(${Translate.over_group(row, captures, source, env)?})"))
				_ => Ok(Binding.Expr("${Translate.list_at(list, env)?}.len()"))
			}
		_ => match Translate.eval(list, env)? {
			Group(_) => Ok(Binding.Expr("count()"))
			_ => Ok(Binding.Expr("${Translate.list_at(list, env)?}.len()"))
		}
	}

	## `sum`: `map(f).sum()` over a group's rows is `math::sum(f)`, and over a
	## list `math::sum` of the list.
	sum : Code.Tree, Env -> Try(Binding, Ql.Error)
	sum = |list, env| Translate.aggregate_arg("math::sum", list, env)

	## An aggregate function of a list: over a group's rows `fn(f)` for
	## `map(f)`, and over a list `fn` of the list.
	aggregate_arg : Str, Code.Tree, Env -> Try(Binding, Ql.Error)
	aggregate_arg = |function, list, env| Ok(Binding.Expr(Translate.call(function, [Translate.aggregate_list(list, env)?.text])))

	## The text of the list of an aggregate, and whether it is a group's rows.
	aggregate_list : Code.Tree, Env -> Try({ text : Str, grouped : Bool }, Ql.Error)
	aggregate_list = |list, env| match Translate.eval(list, env)? {
		Column(found) => Ok({ text: found, grouped: Bool.True })
		_ => Ok({ text: Translate.list_at(list, env)?, grouped: Bool.False })
	}

	## A closure over a group's rows: its parameter is the row the group
	## aggregates, so `|o| o.total` is `total`.
	over_group : U32, List(Code.Tree), Binding, Env -> Try(Str, Ql.Error)
	over_group = |row, captures, source, env| {
		values = captures.map_try(|c| Translate.eval(c, env))?
		Translate.text(Translate.expand(row, values.append(source), env)?)
	}

	## A list operation with a closure: `xs.any(|$v1| ..)`. The closure's row
	## is expanded with its captured values and its element bound to `$vN`,
	## where `N` is the row's id, so a nested closure never shadows its
	## parent's variable.
	lambda : Code.Tree, Code.Tree, Str, Env -> Try(Binding, Ql.Error)
	lambda = |list, f, name, env| {
		(row, captures) = match f {
			Op({ op: Closure(r), args: c, .. }) => (r, c)
			_ => return Err(Unsupported("`${name}` takes a function the clause writes or names"))
		}
		source = Translate.eval(list, env)?
		(list_text, edges) = match source {
			ListOf(l) => (l.at, l.edges)
			Group(rows) if name == "map" => return Ok(Binding.Column(Translate.over_group(row, captures, rows, env)?))
			Group(_) | Column(_) => return Err(Unsupported("a group's rows take `len`, `keep_if(..).len()` and `map(..).sum()`"))
			other => (Translate.operand(other)?, Bool.False)
		}
		var_name = "$v${row.to_str()}"
		element_ty = match env.graph.row(row).params.last() {
			Ok(found) => found
			Err(_) => return Err(Unsupported("`${name}` takes a function of one element"))
		}
		element =
			if edges {
				Binding.Row({ at: var_name, of: Ref, edge: Bool.True })
			} else {
				Translate.at(var_name, element_ty)
			}
		values = captures.map_try(|c| Translate.eval(c, env))?
		result = Translate.expand(row, values.append(element), env)?
		closure = |inner| "|${var_name}| ${inner}"
		match name {
			"any" | "all" => Ok(Binding.Expr("${list_text}.${name}(${closure(Translate.text(result)?)})"))
			"map" => Ok(Binding.ListOf({ at: "${list_text}.map(${closure(Translate.text(result)?)})", edges: Bool.False }))
			"filter" => Ok(Binding.ListOf({ at: "${list_text}.filter(${closure(Translate.text(result)?)})", edges }))
			"drop" => Ok(Binding.ListOf({ at: "${list_text}.filter(${closure("!${Translate.operand(result)?}")})", edges }))
			"count" => Ok(Binding.Expr("${list_text}.filter(${closure(Translate.text(result)?)}).len()"))
			_ => Ok(Binding.Maybe("${list_text}.find(${closure(Translate.text(result)?)})"))
		}
	}

	## A call to one of the application's own functions, expanded with its
	## parameters bound to what the arguments stand for.
	expand : U32, List(Binding), Env -> Try(Binding, Ql.Error)
	expand = |row, values, env| {
		if env.depth > 32 or env.graph.row(row).recursive {
			return Err(Unsupported("a function that calls itself has no SurrealQL form"))
		}
		Translate.eval(env.graph.to_tree(row), { ..env, params: values, row, nodes: [], depth: env.depth + 1 })
	}

	literal : Code.Lit -> Try(Str, Ql.Error)
	literal = |value| match value {
		Int(n, _) => Ok(n.to_str())
		Frac(f, _) => Ok(Ql.float(f))
		Fixed(d) => Ok(Ql.literal(Ql.Value.Decimal(d)))
		Bool(b) => Ok(if (b) "true" else "false")
		Str(s) => Ok(Ql.quote(s))
		Bytes(_) => Err(Unsupported("a byte literal has no SurrealQL form"))
	}

	## A two-operand builtin as its SurrealQL operator. The normal form puts
	## an integer literal first in a comparison (`3 < qty`); a comparison
	## whose left operand is the only literal is written the other way round,
	## with the mirrored operator.
	binary : Str, Str, Code.Tree, Code.Tree, Env -> Try(Binding, Ql.Error)
	binary = |owner, method, lhs, rhs, env| {
		mirrored = Translate.mirror(method)
		flip = Translate.is_literal(lhs) and !Translate.is_literal(rhs) and !mirrored.is_empty()
		symbol = Translate.operator(owner, if (flip) mirrored else method)?
		left = Translate.arg(if (flip) rhs else lhs, env)?
		right = Translate.arg(if (flip) lhs else rhs, env)?
		Ok(Binding.Infix("${left} ${symbol} ${right}"))
	}

	mirror : Str -> Str
	mirror = |method| match method {
		"is_lt" => "is_gt"
		"is_gt" => "is_lt"
		"is_lte" => "is_gte"
		"is_gte" => "is_lte"
		"is_eq" => "is_eq"
		_ => ""
	}

	## Whether a tree is a constant: a literal, or a record, list or nominal
	## of them, such as an `Id` or a `Datetime` written in.
	is_literal : Code.Tree -> Bool
	is_literal = |tree| match tree {
		Op({ op: Lit(_), .. }) => Bool.True
		Op({ op: Wrap(_), args, .. }) => args.all(Translate.is_literal)
		Op({ op: Record(_), args, .. }) => args.all(Translate.is_literal)
		Op({ op: List, args, .. }) => args.all(Translate.is_literal)
		_ => Bool.False
	}

	## The SurrealQL operator of a builtin's method. SurrealDB's `/` between
	## ints truncates toward zero and its `%` follows the dividend, as Roc's
	## `//` and `%` on integers do.
	operator : Str, Str -> Try(Str, Ql.Error)
	operator = |owner, method| {
		whole = owner.starts_with("Num.I") or owner.starts_with("Num.U")
		match method {
			"plus" => Ok("+")
			"minus" => Ok("-")
			"times" => Ok("*")
			"div_by" => Ok("/")
			"div_trunc_by" =>
				if whole {
					Ok("/")
				} else {
					Err(Unsupported("`//` on `${owner}` truncates a fraction, and SurrealDB's `/` does not; divide with `/`"))
				}
			"rem_by" =>
				if whole {
					Ok("%")
				} else {
					Err(Unsupported("`%` on `${owner}` has no SurrealQL form; SurrealDB's `%` is for integers here"))
				}
			"is_lt" => Ok("<")
			"is_gt" => Ok(">")
			"is_lte" => Ok("<=")
			"is_gte" => Ok(">=")
			"is_eq" => Ok("=")
			_ => Err(Unsupported("`${owner}.${method}` has no SurrealQL form"))
		}
	}
}
