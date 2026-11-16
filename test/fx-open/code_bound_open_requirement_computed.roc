app [main!] { pf: platform "./platform/main.roc" }

import pf.Stdout

# `main!` computes a function with a generic `Code.Bound` call at the error
# row the platform's requirement leaves open. `main!` does not generalize, so
# the row closes when the app module finishes checking, and the use of `run!`
# inside `main!` is the closing use.
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

run! : List(Str) => Try({}, [Exit(I32), ..e])
run! = |_args| {
	bound = fetch(3)
	Stdout.line!("inputs ${Str.inspect(bound.inputs())}")
	bound.value()
}

main! = if Bool.True run! else run!
