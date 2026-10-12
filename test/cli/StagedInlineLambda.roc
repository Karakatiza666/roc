# A lambda written where a `Code` is expected, described where it stands.
#
# Three things reach a `Code(f)` position, and all three describe here. A name
# leads to a top-level definition, which the walk reads. A call to a template
# hands back the lambda that template returns, described once per call with the
# call's arguments written in. A lambda written at the position itself is the
# third: nothing names it, so the walk reads the lambda and the description
# takes its place.
Stage := {}.{
	render : Code(U16 -> U16) -> Str
	render = |code| Stage.node(Code.ir(code))

	node : Code.Ir -> Str
	node = |ir| match ir {
		Lambda(params, body, _) => "(fn ${Str.join_with(params.map(|p| p.name), " ")} ${Stage.node(body)})"
		Param(name, _) => name
		Lit(lit, _) => match lit {
			Int(value, _) => value.to_str()
			_ => "?"
		}
		Binop(op, lhs, rhs, _) => "(${op} ${Stage.node(lhs)} ${Stage.node(rhs)})"
		Call(callee, args, _) => "(${callee} ${Str.join_with(args.map(Stage.node), " ")})"
		_ => "?"
	}
}

double : U16 -> U16
double = |x| x * 2

## A template, so the lambda it returns keeps standing for every call of it.
add : U16 -> Code(U16 -> U16)
add = |n| |x| x + n

in_place : Str
in_place = Stage.render(|x| double(x) + 1)

by_name : Str
by_name = Stage.render(double)

from_template : Str
from_template = Stage.render(add(7))

## The same lambda inside a function body, which lowering compiles where a
## top-level constant is evaluated instead.
in_function : U16 -> Str
in_function = |_n| Stage.render(|x| double(x) + 1)

main! = |_args| {
	echo!("in place: ${in_place}\n")
	echo!("by name: ${by_name}\n")
	echo!("template: ${from_template}\n")
	echo!("in a function: ${in_function(3)}\n")
	Ok({})
}
