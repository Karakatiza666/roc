# A `match` over a tag union, described and then compiled by a translator.
#
# The translator reads the branches the compiler wrote and emits a rule per
# branch, which is what every use of reification over tags looks like: a `match`
# in Roc becomes a dispatch in the target.
Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| Stage.node(Code.ir(code))

	node : Code.Ir -> Str
	node = |ir| match ir {
		Lambda(_p, body, _m) => Stage.node(body)
		Param(name, _m) => name
		Local(name, _m) => name
		Lit(lit, _m) => Stage.lit(lit)
		MakeTag(name, payloads, _m) => "${name}(${Str.join_with(payloads.map(Stage.node), " ")})"
		Binop(op, lhs, rhs, _m) => "(${Stage.node(lhs)} ${op} ${Stage.node(rhs)})"
		Match(subject, branches, _m) =>
			"match ${Stage.node(subject)} { ${Str.join_with(branches.map(Stage.branch), " ")} }"
		_ => "other"
	}

	lit : Code.Lit -> Str
	lit = |value| match value {
		Bool(flag) => if flag "True" else "False"
		Int(number, _t) => number.to_str()
		Frac(number, _t) => number.to_str()
		Fixed(number) => number.to_str()
		Str(text) => text
		Bytes(bytes) => "bytes(${bytes.len().to_str()})"
	}

	branch : Code.Branch -> Str
	branch = |b| {
		guard = match b.guard {
			NoGuard => ""
			Guard(g) => " if ${Stage.node(g)}"
		}
		"${Str.join_with(b.patterns.map(Stage.pattern), " | ")}${guard} => ${Stage.node(b.value)}"
	}

	pattern : Code.Pattern -> Str
	pattern = |p| match p {
		Bind(name, _m) => name
		Anything(_m) => "_"
		Variant(name, args, _m) => "${name}(${Str.join_with(args.map(Stage.pattern), " ")})"
		PatLit(value, _m) => Stage.lit(value)
		PatTuple(items, _m) => "(${Str.join_with(items.map(Stage.pattern), " ")})"
		PatRecord(fs, _m) => "{${Str.join_with(fs.map(|f| "${f.name}: ${Stage.pattern(f.pattern)}"), " ")}}"
		PatAs(inner, name, _m) => "${Stage.pattern(inner)} as ${name}"
		PatGuard(inner, cond, _m) => "${Stage.pattern(inner)} when ${Stage.node(cond)}"
		PatList(items, _m) => "[${Str.join_with(items.map(Stage.pattern), " ")}]"
		PatListRest(before, rest, after, _m) =>
			"[${Str.join_with(before.map(Stage.pattern), " ")} ${Stage.bound(rest)} ${Str.join_with(after.map(Stage.pattern), " ")}]"
		PatStr(prefix, steps, end, _m) => {
			tail = match end {
				Exact => ""
				Tail => ".."
			}
			"'${prefix}'${Str.join_with(steps.map(|s| "${Stage.bound(s.capture)}'${s.delimiter}'"), "")}${tail}"
		}
	}

	bound : [Ignored, Named(Str)] -> Str
	bound = |b| match b {
		Ignored => ".."
		Named(name) => "..${name}"
	}
}

Color := [Red, Green(F32), Blue]

shade : Color -> F32
shade = |c| match c {
	Red | Blue => 1.0
	Green(v) if v > 0.0 => v
	Green(_) => 0.0
}

staged : Str
staged = Stage.describe(shade)

main! = |_args| {
	echo!("${staged}\n")
	Ok({})
}
