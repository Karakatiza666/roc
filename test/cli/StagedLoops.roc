# What leaves a loop: `break`, and a `return` that crosses one.
#
# Everywhere else an escape is the branch the description makes of the
# statements written after it, because that is what it transfers to. What
# these two transfer to is the turns that have not run, which no branch says,
# so each takes a node. The nodes carry what the author wrote rather than a
# `[Continue, Break]` step result, so a target with its own `break` emits one
# and a target that folds lowers them itself.
Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| Stage.node(code.ir())

	node : Code.Ir -> Str
	node = |ir| match ir {
		Lambda(_, body, _) => Stage.node(body)
		Param(name, _) => name
		Local(name, _) => name
		Let(name, bound, rest, _) => "let ${name} = ${Stage.node(bound)}; ${Stage.node(rest)}"
		Binop(op, lhs, rhs, _) => "(${Stage.node(lhs)} ${op} ${Stage.node(rhs)})"
		If(cond, then, els, _) => "if ${Stage.node(cond)} { ${Stage.node(then)} } else { ${Stage.node(els)} }"
		Match(subject, branches, _) =>
			"match ${Stage.node(subject)} { ${Str.join_with(branches.map(Stage.branch), " ")} }"
		MakeTag(name, args, _) => "${name}(${Str.join_with(args.map(Stage.node), " ")})"
		MakeTuple(items, _) => "(${Str.join_with(items.map(Stage.node), " ")})"
		MakeRecord(fields, _) => "{${Str.join_with(fields.map(Stage.field), " ")}}"
		For(loop, _) =>
			"for ${loop.item} in ${Stage.node(loop.source)} carrying ${Stage.carried(loop.carried)} { ${Stage.node(loop.body)} }"
		While(loop, _) =>
			"while ${Stage.carried(loop.carried)} as long as ${Stage.node(loop.cond)} { ${Stage.node(loop.body)} }"
		Break(state, _) => "break ${Stage.node(state)}"
		Return(value, _) => "return ${Stage.node(value)}"
		Lit(value, _) => Stage.lit(value)
		_ => "other"
	}

	field : { name : Str, value : Code.Ir } -> Str
	field = |f| "${f.name}: ${Stage.node(f.value)}"

	carried : List({ initial : Code.Ir, name : Str }) -> Str
	carried = |entries| "[${Str.join_with(entries.map(Stage.entry), ", ")}]"

	entry : { initial : Code.Ir, name : Str } -> Str
	entry = |e| "${e.name} = ${Stage.node(e.initial)}"

	lit : Code.Lit -> Str
	lit = |value| match value {
		Bool(flag) => if flag "True" else "False"
		Int(number, _) => number.to_str()
		Frac(number, _) => number.to_str()
		Fixed(number) => number.to_str()
		Str(text) => "'${text}'"
		Bytes(bytes) => "bytes(${bytes.len().to_str()})"
	}

	branch : Code.Branch -> Str
	branch = |b| "${Str.join_with(b.patterns.map(Stage.pattern), " | ")} => ${Stage.node(b.value)}"

	pattern : Code.Pattern -> Str
	pattern = |p| match p {
		Bind(name, _) => name
		Anything(_) => "_"
		Variant(name, args, _) => "${name}(${Str.join_with(args.map(Stage.pattern), " ")})"
		_ => "?"
	}
}

# `break` settles the loop at the state its `var`s have reached.
capped : List(U16) -> U16
capped = |xs| {
	var $total = 0
	for x in xs {
		if x > 5 {
			break
		}
		$total = $total + x
	}
	$total
}

# A branch that writes the state and then leaves, which is the shape Roc's own
# `List.fold_until` is written in.
until : List(U16) -> U16
until = |xs| {
	var $state = 0
	for x in xs {
		if x == 0 {
			$state = 99
			break
		}
		$state = $state + x
	}
	$state
}

# A loop that assigns no `var` carries nothing, and matters for what leaves
# it: the state is `{}` and the node binds a name nothing reads.
find : List(U16), U16 -> [Found(U16), NotFound]
find = |xs, target| {
	for x in xs {
		if x == target {
			return Found(x)
		}
	}
	NotFound
}

# `x?` inside a loop leaves the function, so the `Err` branch is a `Return`
# where outside a loop it would be the statements written after it.
totalled : List(Try(U16, [Bad])) -> Try(U16, [Bad])
totalled = |ts| {
	var $total = 0
	for t in ts {
		h = t?
		$total = $total + h
	}
	Ok($total)
}

# Roc has no labelled `break`, so this one leaves the `while`.
nested : List(U16) -> U16
nested = |xs| {
	var $total = 0
	for x in xs {
		var $j = 0
		while $j < x {
			if $j > 3 {
				break
			}
			$j = $j + 1
		}
		$total = $total + $j
	}
	$total
}

# `while Bool.True { .. }` reaches the walk as a form of its own, and carries
# what a `while` carries.
spun : U16 -> U16
spun = |n| {
	var $i = 0
	while Bool.True {
		$i = $i + 1
		if $i > n {
			break
		}
	}
	$i
}

# A `return` written inside an expression wants no node: lifting the `match`
# the `?` desugars to out past the expression that holds it leaves no
# transfer at all.
doubled : Try(U16, [Bad]) -> Try(U16, [Bad])
doubled = |t| Ok(t? * 2)

main! = |_args| {
	echo!("${Stage.describe(capped)}\n")
	echo!("${Stage.describe(until)}\n")
	echo!("${Stage.describe(find)}\n")
	echo!("${Stage.describe(totalled)}\n")
	echo!("${Stage.describe(nested)}\n")
	echo!("${Stage.describe(spun)}\n")
	echo!("${Stage.describe(doubled)}\n")
	Ok({})
}
