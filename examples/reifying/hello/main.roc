# Read this first. `Calc.to_expr` is a translator: it turns a Roc function
# into an arithmetic expression, while the compiler runs.
import Calc

# An ordinary Roc function. The `expect` below calls it.
area : F64, F64 -> F64
area = |w, h| w * h + 1.0

# `Calc` has no operator for `sqrt`, so a translation of this one is refused.
root : F64 -> F64
root = |x| x.sqrt() + 1.0

main! = |_args| {
	echo!("${Str.inspect(Calc.to_expr(area))}\n")
	Ok({})
}

# The function, called.
expect area(3.0, 4.0) == 13.0

# The same function, translated. `p0` is `w` and `p1` is `h`.
expect Calc.to_expr(area) == Ok("((p0 * p1) + 1)")

# A refusal that is an `Err`. `refused.roc` shows the refusal that stops the build.
expect Calc.to_expr(root) == Err(Unsupported("`sqrt` has no operator here"))
