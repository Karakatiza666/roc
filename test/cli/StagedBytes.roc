# An embedded file in a reified body.
#
# A file embedded as `List(U8)` describes as a single `Bytes` literal rather
# than one `Int` node per byte, because a file is as large as it is and a
# translator wants the blob as one value. A file embedded as `Str` is a `Str`
# literal instead.
import "staged_bytes_blob.bin" as blob : List(U8)
import "staged_bytes_text.txt" as source : Str

StagedBytes := {}.{
	describe : Code(f) -> Str
	describe = |code| {
		graph = Code.graph(code)
		first = graph.root_row()
		others = graph.rows().keep_if(|other| other.id != first.id)
		shown = [first].concat(others).map(|each| "r${each.id.to_str()} = ${StagedBytes.row(graph, each)}")
		Str.join_with(shown, " ; ")
	}

	row : Code.Graph, Code.Row -> Str
	row = |graph, described| {
		params = Str.join_with(described.params.map(|param| param.name()), ", ")
		"|${params}| -> ${described.result.name()} ${StagedBytes.tree(graph.to_tree(described.id))}"
	}

	tree : Code.Tree -> Str
	tree = |t| match t {
		Op(o) => StagedBytes.op(o.op, o.args)
		Param(k) => "p${k.to_str()}"
		Arg(a) => "s${a.owner.to_str()}.${a.k.to_str()}"
		Out(o) => "n${o.node.to_str()}.${o.k.to_str()}"
		Def(n) => "n${n.to_str()}"
		Block(b) => {
			defs = b.defs.map(|d| "n${d.id.to_str()} = ${StagedBytes.tree(d.value)}; ")
			last = match b.end {
				Value(vals) => StagedBytes.all(vals)
				Jump(j) => "jump j${j.join.to_str()}(${StagedBytes.all(j.args)})"
				Return(v) => "return ${StagedBytes.tree(v)}"
				Continue(vals) => "continue(${StagedBytes.all(vals)})"
				Break(vals) => "break(${StagedBytes.all(vals)})"
				Branch(sw) => StagedBytes.tree(sw)
			}
			if defs.is_empty() last else "{ ${Str.join_with(defs, "")}${last} }"
		}
	}

	all : List(Code.Tree) -> Str
	all = |ts| Str.join_with(ts.map(StagedBytes.tree), ", ")

	op : Code.Op, List(Code.Tree) -> Str
	op = |o, args| match o {
		Lit(l) => StagedBytes.lit(l)
		Prim(p) => "${p.owner}.${p.method}(${StagedBytes.all(args)})"
		Call(r) => "r${r.to_str()}(${StagedBytes.all(args)})"
		Closure(r) => "closure r${r.to_str()}(${StagedBytes.all(args)})"
		Record(names) => {
			fields = List.map2(names, args, |name, arg| "${name}: ${StagedBytes.tree(arg)}")
			if fields.is_empty() "{}" else "{ ${Str.join_with(fields, ", ")} }"
		}
		Tuple => "(${StagedBytes.all(args)})"
		List => "[${StagedBytes.all(args)}]"
		Tag(name) => "${name}(${StagedBytes.all(args)})"
		Wrap(name) => "${name}.(${StagedBytes.all(args)})"
		Unwrap => "unwrap(${StagedBytes.all(args)})"
		Field(name) => "${StagedBytes.all(args)}.${name}"
		Index(i) => "${StagedBytes.all(args)}.${i.to_str()}"
		Payload(name, i) => "${StagedBytes.all(args)}.${name}.${i.to_str()}"
		Item => "item(${StagedBytes.all(args)})"
		OptField(name) => "${StagedBytes.all(args)}.?${name}"
		Switch(sw) => {
			scrutinee = StagedBytes.all(args.take_first(1))
			arms = List.map2(sw.arms, args.drop_first(1), |arm, body| "${StagedBytes.key(arm.key)} => ${StagedBytes.tree(body)}")
			joins = args.drop_first(1 + sw.arms.len()).map_with_index(|body, i| " j${i.to_str()}: ${StagedBytes.tree(body)}")
			"switch ${scrutinee} { ${Str.join_with(arms, " | ")} }${Str.join_with(joins, "")}"
		}
		And(_) => "and(${StagedBytes.all(args)})"
		Or(_) => "or(${StagedBytes.all(args)})"
		ForRange(r) => "for_range${if r.inclusive "=" else "<"}(${StagedBytes.all(args)})"
		ForList(_) => "for_list(${StagedBytes.all(args)})"
		Loop(_) => "loop(${StagedBytes.all(args)})"
		Lambda(_) => "lambda(${StagedBytes.all(args)})"
		Crash => "crash(${StagedBytes.all(args)})"
		Derived(name, _) => "derived ${name}(${StagedBytes.all(args)})"
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
		Lit(l) => StagedBytes.lit(l)
		Len(n) => "len ${n.to_str()}"
		AtLeast(n) => "len >= ${n.to_str()}"
		Default => "_"
	}
}

embedded_bytes : U8 -> List(U8)
embedded_bytes = |_n| blob

embedded_text : U8 -> Str
embedded_text = |_n| source

staged_bytes : Str
staged_bytes = StagedBytes.describe(embedded_bytes)

staged_text : Str
staged_text = StagedBytes.describe(embedded_text)

main! = |_args| {
	echo!("${staged_bytes}\n")
	echo!("${staged_text}\n")
	Ok({})
}
