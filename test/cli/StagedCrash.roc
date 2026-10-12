# `crash` in a reified body, both with a plain message and an interpolated one.
#
# A `match` over a closed union needs a way to say "this branch cannot happen",
# and a target whose own `switch` is not exhaustive needs that branch written.
# The message is an `Ir` rather than a `Str`, so an interpolated one arrives as
# the concatenation the checker made of it.
StagedCrash := {}.{
	describe : Code(f) -> Str
	describe = |code| StagedCrash.node(code.ir())

	node : Code.Ir -> Str
	node = |ir| match ir {
		Lambda(_, body, _) => StagedCrash.node(body)
		Param(name, _) => name
		Local(name, _) => name
		Let(name, bound, rest, _) => "let ${name} = ${StagedCrash.node(bound)}; ${StagedCrash.node(rest)}"
		Call(callee, args, _) => "${callee}(${Str.join_with(args.map(StagedCrash.node), ", ")})"
		Lit(value, _) => StagedCrash.lit(value)
		Crash(message, _) => "crash(${StagedCrash.node(message)})"
		Binop(op, lhs, rhs, _) => "(${StagedCrash.node(lhs)} ${op} ${StagedCrash.node(rhs)})"
		If(cond, then, els, _) => "if ${StagedCrash.node(cond)} { ${StagedCrash.node(then)} } else { ${StagedCrash.node(els)} }"
		Match(subject, branches, _) =>
			"match ${StagedCrash.node(subject)} { ${Str.join_with(branches.map(StagedCrash.branch), " ")} }"
		_ => "other"
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
	branch = |b| "${Str.join_with(b.patterns.map(StagedCrash.pattern), " | ")} => ${StagedCrash.node(b.value)}"

	pattern : Code.Pattern -> Str
	pattern = |p| match p {
		Variant(name, _, _) => name
		Anything(_) => "_"
		_ => "?"
	}
}

Color := [Red, Green, Blue]

shade : Color -> F32
shade = |c| match c {
	Red => 1.0
	Green => 0.0
	Blue => crash "no shade for Blue"
}

clamp : U16 -> U16
clamp = |n| if n > 10 { n } else { crash "too small: ${n.to_str()}" }

staged_match : Str
staged_match = StagedCrash.describe(shade)

staged_interpolated : Str
staged_interpolated = StagedCrash.describe(clamp)

main! = |_args| {
	echo!("${staged_match}\n")
	echo!("${staged_interpolated}\n")
	Ok({})
}
