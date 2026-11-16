app [main!] { pf: platform "./platform/main.roc" }

import pf.Stdout

# `main!` closes the error row the platform's requirement leaves open, so
# `main!` is no generic function, and its use of `describe` is the closing
# use of the Code site.
describe : Try({}, [Exit(I32), ..e]) -> Str
describe = |result| check(result, |r| match r {
	Ok(_) => Bool.True
	Err(_) => Bool.False
})

check : a, Code(a -> Bool) -> Str
check = |_value, code| "params ${Code.graph(code).root_row().params.len().to_str()}"

main! : List(Str) => Try({}, [Exit(I32)])
main! = |_args| {
	result = Ok({})
	Stdout.line!(describe(result))
	result
}
