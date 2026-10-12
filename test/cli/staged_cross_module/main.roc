app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import Maker

Stage := {}.{
	## The staged body, printed with its literals in place and led by where it
	## was written, which is the module that defines it rather than this one.
	shape : Code(f) -> Str
	shape = |code| match Code.ir(code) {
		Lambda(_, body, meta) => "${meta.region.module_name}:${meta.region.start_line.to_str()} ${Stage.node(body)}"
		_ => "other"
	}

	## A generic function in another module, described at the type this site
	## fixes it to.
	twinned : Code(Str -> (Str, Str)) -> Str
	twinned = |code| match Code.ir(code) {
		Lambda(params, _body, meta) =>
			"${meta.ty.name()} at ${Str.join_with(params.map(|p| p.ty.name()), ", ")}"
		_ => "other"
	}

	node : Code.Ir -> Str
	node = |ir| match ir {
		Param(name, _) => name
		Lit(lit, _) => match lit {
			Int(value, _) => value.to_str()
			Frac(value, _) => value.to_str()
			Fixed(value) => value.to_str()
			Bool(value) => if value "True" else "False"
			Str(value) => value
			Bytes(bytes) => "bytes(${bytes.len().to_str()})"
		}
		Binop(op, lhs, rhs, _) => "(${op} ${Stage.node(lhs)} ${Stage.node(rhs)})"
		Call(callee, args, _) => "(call ${callee} ${Str.join_with(args.map(Stage.node), " ")})"
		_ => "?"
	}
}

main! = || {
	Stdout.line!("${Stage.shape(Maker.double)}")
	Stdout.line!("${Stage.shape(Maker.scaled(3.0))}")
	Stdout.line!("${Stage.twinned(Maker.twin)}")
	Stdout.line!("${Stage.shape(Maker.twice(|y| y + 1.0))}")
}
