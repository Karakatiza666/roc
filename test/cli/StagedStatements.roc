# The statements a reified body can hold, and what each describes as.
#
# Every one of them needs a name the author did not write, which is why they
# are one fixture: a destructuring binding names the fields it reads, a `var`
# names each version it settles, and a loop names the state it carries from
# one turn to the next. The `Ir` has no assignment, so each of these describes
# as a binding rather than as a statement.
#
# `test/cli/StagedLoops.roc` pins what leaves a loop, which is the one thing
# here that takes a node of its own.
Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| Stage.node(code.ir())

	node : Code.Ir -> Str
	node = |ir| match ir {
		Lambda(_, body, _) => Stage.node(body)
		Param(name, _) => name
		Local(name, _) => name
		Let(name, bound, rest, _) => "let ${name} = ${Stage.node(bound)}; ${Stage.node(rest)}"
		Field(record, name, _) => "${Stage.node(record)}.${name}"
		Index(tuple, at, _) => "${Stage.node(tuple)}.${at.to_str()}"
		Binop(op, lhs, rhs, _) => "(${Stage.node(lhs)} ${op} ${Stage.node(rhs)})"
		If(cond, then, els, _) => "if ${Stage.node(cond)} { ${Stage.node(then)} } else { ${Stage.node(els)} }"
		Match(subject, branches, _) =>
			"match ${Stage.node(subject)} { ${Str.join_with(branches.map(Stage.branch), " ")} }"
		MakeTag(name, args, _) => "${name}(${Str.join_with(args.map(Stage.node), " ")})"
		MakeTuple(items, _) => "(${Str.join_with(items.map(Stage.node), " ")})"
		Range(from, to, reach, _) => "${Stage.node(from)}${Stage.reach(reach)}${Stage.node(to)}"
		For(loop, _) =>
			"for ${loop.item} in ${Stage.node(loop.source)} carrying ${Stage.carried(loop.carried)} { ${Stage.node(loop.body)} }"
		While(loop, _) =>
			"while ${Stage.carried(loop.carried)} as long as ${Stage.node(loop.cond)} { ${Stage.node(loop.body)} }"
		Lit(value, _) => Stage.lit(value)
		_ => "other"
	}

	carried : List({ initial : Code.Ir, name : Str }) -> Str
	carried = |entries| "[${Str.join_with(entries.map(Stage.entry), ", ")}]"

	entry : { initial : Code.Ir, name : Str } -> Str
	entry = |e| "${e.name} = ${Stage.node(e.initial)}"

	reach : [Exclusive, Inclusive] -> Str
	reach = |end| match end {
		Exclusive => "..<"
		Inclusive => "..="
	}

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

Wrapped := [Pair(U16, U16)]

# A record pattern reads a field per name it binds.
fields : { a : U16, b : U16 } -> U16
fields = |r| {
	{ a, b } = r
	a + b
}

# A tuple pattern reads a position per name it binds, and a subject that is
# not already a name is bound once first.
positions : { pair : (U16, U16) } -> U16
positions = |r| {
	(a, b) = r.pair
	a + b
}

# A pattern that names a variant is a test as well as a binding, so it stays
# the `match` it is.
variant : Wrapped -> U16
variant = |w| {
	Pair(a, b) = w
	a + b
}

# A branch that returns early takes everything after it as its alternative.
early : U16 -> U16
early = |n| {
	if n > 10 {
		return 0
	}
	n + 1
}

# `x?` is the same rewrite around a binding: the `Err` branch returns, and the
# `Ok` branch has the value the binding holds.
forwarded : Try(U16, [Odd]) -> Try(U16, [Odd])
forwarded = |t| {
	h = t?
	Ok(h + 1)
}

# An `expect` asserts and hands back nothing, so the description passes over it.
asserted : U16 -> U16
asserted = |n| {
	expect n > 0
	n + 1
}

# Each assignment to a `var` binds a version of its own.
versions : U16 -> U16
versions = |n| {
	var $x = n
	$x = $x + 1
	$x = $x * 2
	$x
}

# A `var` written in one branch and read after it needs a join, which is the
# `if` hoisted into the binding.
joined : U16 -> U16
joined = |n| {
	var $x = n
	if n > 10 {
		$x = 0
	}
	$x
}

# Two `var`s travel together as a tuple, because one `If` per `var` would
# describe each branch once per `var`.
paired : U16 -> U16
paired = |n| {
	var $x = n
	var $y = 1
	if n > 10 {
		$x = 0
		$y = 2
	} else {
		$y = 3
	}
	$x + $y
}

# A loop is the fold it is: the state it carries is the `var` its body writes.
summed : List(U16) -> U16
summed = |xs| {
	var $total = 0
	for x in xs {
		$total = $total + x
	}
	$total
}

# A range reaches the walk as the call the checker resolves it to, and
# describes as the two ends it was written as.
counted : U16 -> U16
counted = |n| {
	var $total = 0
	for i in 0..<n {
		$total = $total + i
	}
	$total
}

# A `while` carries the same state, and its condition reads it too.
walked : U16 -> U16
walked = |n| {
	var $i = 0
	while $i < n {
		$i = $i + 1
	}
	$i
}

# A statement whose value is discarded is a binding nothing reads, which keeps
# its order and whatever it diverges on.
sequenced : U16 -> U16
sequenced = |n| {
	_ = n + 1
	n * 2
}

main! = |_args| {
	echo!("${Stage.describe(fields)}\n")
	echo!("${Stage.describe(positions)}\n")
	echo!("${Stage.describe(variant)}\n")
	echo!("${Stage.describe(early)}\n")
	echo!("${Stage.describe(forwarded)}\n")
	echo!("${Stage.describe(asserted)}\n")
	echo!("${Stage.describe(versions)}\n")
	echo!("${Stage.describe(joined)}\n")
	echo!("${Stage.describe(paired)}\n")
	echo!("${Stage.describe(summed)}\n")
	echo!("${Stage.describe(counted)}\n")
	echo!("${Stage.describe(walked)}\n")
	echo!("${Stage.describe(sequenced)}\n")
	Ok({})
}
