# A recursive nominal, described and read back by a translator.
#
# `Tree` reaches itself, so its `Code.Ty` is a `Named` whose backing refers back
# to it as `Recursive` of the same name. The translator below resolves that
# reference the way the description means it, innermost enclosing `Named` first,
# and prints the type and the body it was handed.
Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| match Code.ir(code) {
		Lambda(params, body, _m) =>
			"${Str.join_with(params.map(|p| Stage.ty(p.ty)), ", ")} : ${Stage.node(body)}"
		_ => "not a lambda"
	}

	ty : Code.Ty -> Str
	ty = |t| match t {
		Named(name, backing) => "${name} = ${Stage.ty(backing)}"
		Recursive(name) => "^${name}"
		TagUnion(vs) => "[${Str.join_with(vs.map(Stage.variant), ", ")}]"
		U16 => "U16"
		_ => "?"
	}

	variant : { name : Str, payloads : List(Code.Ty) } -> Str
	variant = |v| "${v.name}(${Str.join_with(v.payloads.map(Stage.ty), ", ")})"

	node : Code.Ir -> Str
	node = |ir| match ir {
		Param(name, _m) => name
		Local(name, _m) => name
		MakeTag(name, payloads, _m) => "${name}(${Str.join_with(payloads.map(Stage.node), ", ")})"
		Match(subject, branches, _m) =>
			"match ${Stage.node(subject)} { ${Str.join_with(branches.map(Stage.branch), " ")} }"
		_ => "?"
	}

	branch : Code.Branch -> Str
	branch = |b| "${Str.join_with(b.patterns.map(Stage.pattern), " | ")} => ${Stage.node(b.value)}"

	pattern : Code.Pattern -> Str
	pattern = |p| match p {
		Bind(name, _m) => name
		Anything(_m) => "_"
		Variant(name, args, _m) => "${name}(${Str.join_with(args.map(Stage.pattern), ", ")})"
		_ => "?"
	}
}

Tree := [Leaf, Node(Tree, Tree)]

graft : Tree -> Tree
graft = |t| match t {
	Leaf => Tree.Node(Tree.Leaf, Tree.Leaf)
	Node(l, _r) => Tree.Node(l, t)
}

# A type parameter changes which id a use carries and not which nominal it is,
# so `Fruit(U16)` reaches itself the same way `Tree` does.
Fruit(a) := [Bare, Grown(Fruit(a), a)]

pick : Fruit(U16) -> Fruit(U16)
pick = |f| match f {
	Bare => f
	Grown(inner, _n) => inner
}

staged : Str
staged = Stage.describe(graft)

staged_parametric : Str
staged_parametric = Stage.describe(pick)

main! = |_args| {
	echo!("${staged}\n")
	echo!("${staged_parametric}\n")
	Ok({})
}
