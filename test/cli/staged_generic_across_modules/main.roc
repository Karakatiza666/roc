app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import Shader

# A generic callee in another module describes once per instantiation.
#
# The scheme is written in `Shader`'s own types and the type each call fixes it
# to is written here, so a row is read under a substitution that reaches across
# the boundary. The stage prints what each row's parameters take, which is the
# instantiation rather than the name that reaches it.
Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| Str.join_with(Code.definitions(code).map(Stage.row), " ; ")

	row : { ir : Code.Ir, name : Str } -> Str
	row = |d| match d.ir {
		Lambda(params, _body, _m) => "${d.name}(${Str.join_with(params.map(|p| Stage.ty(p.ty)), ", ")})"
		_ => d.name
	}

	ty : Code.Ty -> Str
	ty = |t| match t {
		F32 => "F32"
		Str => "Str"
		_ => "?"
	}
}

mix : F32 -> F32
mix = |x| Shader.id(x) + Shader.pick(x, "s")

main! = || Stdout.line!(Stage.describe(mix))
