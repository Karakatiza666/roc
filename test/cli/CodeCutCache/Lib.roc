# A translator's cut is a top-level constant after its type, which no body
# that reaches the translator names. The warm-cache test edits the cut, so
# the description of the site in `shown` changes while the text of `shown`
# and of the type stays the same.
Lib := {}.{
	code_primitives = cut

	describe : Code(I64 -> I64) -> Str
	describe = |code| Str.inspect(Code.graph(code).rows().map(|row| row.nodes.len()))
}

cut : List(Code.PrimId)
cut = [Code.prim(double)]

double : I64 -> I64
double = |x| x * 2

triple : I64 -> I64
triple = |x| x * 3

shown : Str
shown = Lib.describe(|x| double(triple(x)))

expect shown == "[3]"
