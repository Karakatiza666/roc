# A call whose result is a nominal type built on `Code.Bound` binds the
# run-time reads of the lambdas its chain carries (R5 option A' of the Gap 1
# design). The opt-in is the call's whole type, read through aliases: an
# opaque nominal (`::`), a nominal (`:=`), an alias of a nominal, a nominal
# over an alias, a nominal over a nominal, and a nominal whose backing is its
# own parameter.

## A nominal error type keeps the result types closed.
Error := [Bad(Str)]

## The shape a query library gives its users: the `Try` is inside.
Prepared(out) :: Code.Bound(Try(out, Error)).{
	inputs : Prepared(out) -> List(Code.Value)
	inputs = |Prepared.(b)| b.inputs()

	value : Prepared(out) -> Try(out, Error)
	value = |Prepared.(b)| b.value()
}

Ready := Code.Bound(Str)

BoundStr : Code.Bound(Str)

ReadyAlias : Ready

ViaAlias :: BoundStr

Outer :: Prepared(Str)

Wrap(a) :: a

Q := [Q(Str)].{
	from : Str -> Q
	from = |name| Q(name)

	filter : Q, Code(U16 -> Bool) -> Q
	filter = |Q(text), code| Q("${text} slots ${Code.graph(code).slots().len().to_str()} from ${code.first_slot().to_str()}")

	prepared : Q -> Prepared(Str)
	prepared = |Q(text)| Prepared.(Code.Bound.of(Ok(text)))

	ready : Q -> Ready
	ready = |Q(text)| Ready.(Code.Bound.of(text))

	ready_alias : Q -> ReadyAlias
	ready_alias = |Q(text)| Ready.(Code.Bound.of(text))

	via_alias : Q -> ViaAlias
	via_alias = |Q(text)| ViaAlias.(Code.Bound.of(text))

	outer : Q -> Outer
	outer = |Q(text)| Outer.(Prepared.(Code.Bound.of(Ok(text))))

	wrapped : Q -> Wrap(Code.Bound(Str))
	wrapped = |Q(text)| Wrap.(Code.Bound.of(text))
}

shown : Str, List(Code.Value) -> Str
shown = |text, inputs| {
	values = inputs.map(
		|value| match value {
			Int(n) => n.to_str()
			_ => "other"
		},
	)
	"${text} inputs [${Str.join_with(values, ", ")}]"
}

opaque : U16 -> Str
opaque = |n| {
	p = Q.from("opaque").filter(|m| m > n).filter(|m| m != n + 1).prepared()
	shown(p.value() ?? "err", p.inputs())
}

transparent : U16 -> Str
transparent = |n| {
	Ready.(b) = Q.from("transparent").filter(|m| m < n).ready()
	shown(b.value(), b.inputs())
}

aliased : U16 -> Str
aliased = |n| {
	Ready.(b) = Q.from("aliased").filter(|m| m > n).ready_alias()
	shown(b.value(), b.inputs())
}

alias : U16 -> Str
alias = |n| {
	ViaAlias.(b) = Q.from("alias").filter(|m| m == n).via_alias()
	shown(b.value(), b.inputs())
}

nested : U16 -> Str
nested = |n| {
	Outer.(p) = Q.from("nested").filter(|m| m >= n).outer()
	shown(p.value() ?? "err", p.inputs())
}

parameter : U16 -> Str
parameter = |n| {
	Wrap.(b) = Q.from("parameter").filter(|m| m <= n).wrapped()
	shown(b.value(), b.inputs())
}

main! = |args| {
	n = args.len().to_u16_wrap()
	echo!("${opaque(n + 3)}\n${opaque(n + 7)}\n${transparent(n + 4)}\n${aliased(n + 9)}\n${alias(n + 5)}\n${nested(n + 6)}\n${parameter(n + 8)}\n")
	Ok({})
}
