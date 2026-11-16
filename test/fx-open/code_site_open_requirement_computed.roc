app [main!] { pf: platform "./platform/main.roc" }

import pf.Stdout

# `main!` computes a function that holds a Code site at the error row the
# platform's requirement leaves open. `main!` does not generalize, so the row
# closes when the app module finishes checking, and the use of `run!` inside
# `main!` is the closing use.
describe : Try({}, [Exit(I32), ..e]) -> Str
describe = |result| check(result, |r| match r {
	Ok(_) => Bool.True
	Err(_) => Bool.False
})

check : a, Code(a -> Bool) -> Str
check = |_value, code| "params ${Code.graph(code).root_row().params.len().to_str()}"

run! : List(Str) => Try({}, [Exit(I32), ..e])
run! = |_args| {
	result = Ok({})
	Stdout.line!(describe(result))
	result
}

main! = if Bool.True run! else run!
