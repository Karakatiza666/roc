app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import Helper

# A call inside a description crosses a module boundary, and so does the call
# inside the description that call reaches.
#
# `Helper.twice` is named here and described from `Helper`'s published view.
# Its own body calls `Deeper.inner`, which this application never imports: the
# binding the checker resolved names the artifact rather than an import, so the
# walk reaches it through the artifacts available to this one. Rows are listed
# in the order the root reaches them. Each callee is called twice, so the graph
# view keeps it a row.
Stage := {}.{
	describe : Code(F32 -> F32) -> Str
	describe = |code| Stage.all_rows(code)

	all_rows : Code(f) -> Str
	all_rows = |code| {
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

	root : Code(f) -> Str
	root = |code| {
		graph = Code.graph(code)
		Stage.tree(graph.to_tree(graph.root_row().id))
	}
}

bump : F32 -> F32
bump = |x| Helper.twice(x) + Helper.twice(x * 3.0)

main! = || Stdout.line!(Stage.describe(bump))
