# A translator can refuse a function and point at the line it came from.
# `roc check refused.roc` reports the refusal at the `x.sqrt()` below.
import Calc

root : F64 -> F64
root = |x| x.sqrt() + 1.0

expr = Calc.to_expr_or_stop(root)

main! = |_args| {
	echo!("${expr}\n")
	Ok({})
}
