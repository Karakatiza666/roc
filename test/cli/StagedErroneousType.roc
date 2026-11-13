# A staged function whose parameter type the checker already rejected.
#
# `Twig` is a recursive alias, which Roc refuses, so `Rose` carries an
# erroneous type. The alias is what the reader needs to hear about, and the
# constant holding the site must not be evaluated on the way there: evaluating
# it instantiates `Rose`, and an erroneous type has no instantiation.
Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

Twig : List(Rose)
Rose := [Tip, Fan(Twig)]

count : Rose -> F32
count = |_r| 1.0

staged : Str
staged = Stage.describe(count)

main! = |_args| {
	echo!("${staged}\n")
	Ok({})
}
