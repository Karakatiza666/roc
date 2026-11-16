# Two functions whose types stay open where they are reified, and the report
# for each.
#
# The lambda never reads its first parameter, so only the `Code(f)` position
# could fix that parameter's type, and `f` leaves it open. The report points
# at the parameter and names it. `same` has no annotation, so checking
# inferred a type variable for it that the `Code(f)` position does not fix.
# No operator constrains that variable, so it has no numeric default either.
Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

same = |x| x

unused : Str
unused = Stage.describe(|_ignored, n| n + 1.I64)

inferred : Str
inferred = Stage.describe(same)

main! = |_args| {
	echo!("${unused} ${inferred}\n")
	Ok({})
}
