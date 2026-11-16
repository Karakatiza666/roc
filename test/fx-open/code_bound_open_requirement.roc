app [main!] { pf: platform "./platform/main.roc" }

import pf.Stdout

# A generic `Code.Bound` call at the error row the platform's requirement
# leaves open: the platform's call of `main!` is its closing use, and binds
# the call's inputs there.
Q := [Q(Str)].{
	from : Str -> Q
	from = |name| Q(name)

	filter : Q, Code(U16 -> Bool) -> Q
	filter = |Q(text), code| Q("${text} where slots ${Code.graph(code).slots().len().to_str()}")

	ready : Q -> Code.Bound(Try({}, [Exit(I32), ..e]))
	ready = |Q(_text)| Code.Bound.of(Ok({}))
}

fetch : U16 -> Code.Bound(Try({}, [Exit(I32), ..e]))
fetch = |least| Q.from("meds").filter(|m| m > least).ready()

main! : List(Str) => Try({}, [Exit(I32), ..e])
main! = |_args| {
	bound = fetch(3)
	Stdout.line!("inputs ${Str.inspect(bound.inputs())}")
	bound.value()
}
