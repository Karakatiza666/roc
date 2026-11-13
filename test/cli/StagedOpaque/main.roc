# The functions and constants of an opaque type are its primitives (D1 of
# roc-reify-opaque-proposal.md). The type lives in a path package, so the
# rule reads the module that declares the type, not the site's module. A
# direct call and a method call of one function are one `Prim`; a constant
# that calls one folds to that call; a constant of the type is a `Prim` with
# no arguments; and a function whose type names no opaque type of its module
# is read by its body.
app [main!] { pt: "pt/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pt.Time
import pt.Cal
import pt.Util

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

Event : { id : I64, at : Time }

direct : Event, Time -> Bool
direct = |r, c| Time.is_before(r.at, c)

method : Event, Time -> Bool
method = |r, c| r.at.is_before(c)

operator : Event, Time -> Bool
operator = |r, c| r.at < c

cutoff : Time
cutoff = Time.from_nanos(5)

before_cutoff : Event -> Bool
before_cutoff = |r| r.at < cutoff

after_epoch : Event -> Bool
after_epoch = |r| Time.epoch < r.at

week : U8 -> U8
week = |x| x + Time.days_in_week

doubled : I64 -> I64
doubled = |x| Util.double(x) + 1

parsed : Str -> Cal.Time
parsed = |s| Cal.parse(s)

nested : Cal.Time, Cal.Time -> Bool
nested = |a, b| a < b

# This module declares no opaque type, so its own helper over `Time` is read
# by its body.
later : Time, Time -> Bool
later = |a, b| b.is_before(a)

reversed : Event, Time -> Bool
reversed = |r, c| later(r.at, c)

main! = || {
	Stdout.line!("direct: ${Stage.describe(direct)}")
	Stdout.line!("method: ${Stage.describe(method)}")
	Stdout.line!("one node: ${Str.inspect(Stage.describe(direct) == Stage.describe(method))}")
	Stdout.line!("operator: ${Stage.describe(operator)}")
	Stdout.line!("cutoff: ${Stage.describe(before_cutoff)}")
	Stdout.line!("epoch: ${Stage.describe(after_epoch)}")
	Stdout.line!("week: ${Stage.describe(week)}")
	Stdout.line!("doubled: ${Stage.describe(doubled)}")
	Stdout.line!("parsed: ${Stage.describe(parsed)}")
	Stdout.line!("nested: ${Stage.describe(nested)}")
	Stdout.line!("reversed: ${Stage.describe(reversed)}")
}
