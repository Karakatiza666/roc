# A parameter written as an open record, described at the record its `Code`
# position fixes.
#
# The row is a quantified variable, so a site fixes it the way it fixes any
# other. One definition here describes at two records: one site fixes the row
# to a second field and the other fixes it to nothing, and each takes a row of
# its own because the instantiation key digests what the row was fixed to. The
# third names the row twice, so fixing it once fixes what the body builds.
Stage := {}.{
	wide : Code({ n : U16, m : U16 } -> U16) -> Str
	wide = |code| Stage.node(Code.ir(code))

	narrow : Code({ n : U16 } -> U16) -> Str
	narrow = |code| Stage.node(Code.ir(code))

	rebuild : Code({ n : U16, m : U16 } -> { n : U16, m : U16 }) -> Str
	rebuild = |code| Stage.node(Code.ir(code))

	node : Code.Ir -> Str
	node = |ir| match ir {
		Lambda(params, body, _) => {
			taken = params.map(|p| "${p.name} : ${p.ty.name()}")
			"(fn ${Str.join_with(taken, " ")} ${Stage.node(body)})"
		}
		Param(name, _) => name
		Lit(lit, _) => match lit {
			Int(value, _) => value.to_str()
			_ => "?"
		}
		Binop(op, lhs, rhs, _) => "(${op} ${Stage.node(lhs)} ${Stage.node(rhs)})"
		Field(subject, name, _) => "(. ${Stage.node(subject)} ${name})"
		MakeRecord(entries, _) => {
			written = entries.map(|e| "${e.name}=${Stage.node(e.value)}")
			"(rec ${Str.join_with(written, " ")})"
		}
		_ => "?"
	}
}

take_n : { n : U16, ..rest } -> U16
take_n = |r| r.n

## The same row stands in the parameter and in the result, so the site fixes
## both at once and the update writes every field the record has.
bump : { n : U16, ..rest } -> { n : U16, ..rest }
bump = |r| { ..r, n: r.n + 1 }

widened : Str
widened = Stage.wide(take_n)

exact : Str
exact = Stage.narrow(take_n)

updated : Str
updated = Stage.rebuild(bump)

main! = |_args| {
	echo!("widened: ${widened}\n")
	echo!("exact: ${exact}\n")
	echo!("updated: ${updated}\n")
	Ok({})
}
