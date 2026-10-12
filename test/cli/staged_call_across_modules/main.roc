app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import Helper

# A call inside a description crosses a module boundary, and so does the call
# inside the description that call reaches.
#
# `Helper.twice` is named here and described from `Helper`'s published view.
# Its own body calls `Deeper.inner`, which this application never imports: the
# binding the checker resolved names the artifact rather than an import, so the
# walk reaches it through the artifacts available to this one. Each row is named
# by the module that defines it, and a callee comes before its caller.
Stage := {}.{
	describe : Code(F32 -> F32) -> Str
	describe = |code| {
		rows = Code.definitions(code).map(|d| "${d.name} = ${Stage.node(d.ir)}")
		"${Str.join_with(rows, " ; ")} || ${Stage.node(Code.ir(code))}"
	}

	node : Code.Ir -> Str
	node = |ir| match ir {
		Lambda(_p, body, _m) => "lambda -> ${Stage.node(body)}"
		Param(name, _m) => name
		Lit(l, _m) => match l {
			Int(value, _t) => value.to_str()
			Frac(value, _t) => value.to_str()
			Fixed(value) => value.to_str()
			Bool(value) => if value "True" else "False"
			Str(value) => value
			Bytes(bytes) => "bytes(${bytes.len().to_str()})"
		}
		Binop(op, lhs, rhs, _m) => "(${Stage.node(lhs)} ${op} ${Stage.node(rhs)})"
		Call(name, args, _m) => "${name}(${Str.join_with(args.map(Stage.node), " ")})"
		_ => "?"
	}
}

bump : F32 -> F32
bump = |x| Helper.twice(x) + 1.0

main! = || Stdout.line!(Stage.describe(bump))
