# A lambda at a `Code` position calls a function value that is a parameter
# of the function around it. Each call of that function can pass a
# different function, and its body exists only when the program runs, so
# the walk refuses the read by name. The report says what to write instead:
# a `Code(f)` parameter passed on, a template, or named functions.
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout

# The translator's format: it writes each number as its decimal digits.
Fmt := [Default].{
	default : () -> Fmt
	default = || Default

	encode_i128 : I128, List(U8) -> Try(List(U8), [])
	encode_i128 = |n, out| Ok(out.concat(n.to_str().to_utf8()))
}

Stage := {}.{
	keep : Code.Binds(Code(I64 -> Bool), Fmt) -> Code.Bound(Str)
	keep = |code| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")

	plain : Code(I64 -> Bool) -> Code.Bound(Str)
	plain = |code| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")
}

binds : (I64 -> Bool) -> Str
binds = |pred| Stage.keep(|x| pred(x)).value()

plain : (I64 -> Bool) -> Str
plain = |pred| Stage.plain(|x| pred(x)).value()

# What to write instead: take the function as a `Code` and pass it on.
passed_on : Code(I64 -> Bool) -> Str
passed_on = |pred| Stage.plain(pred).value()

main! = || {
	Stdout.line!(passed_on(|y| y > 2))
	Stdout.line!(binds(|y| y > 2))
	Stdout.line!(plain(|y| y > 2))
}
