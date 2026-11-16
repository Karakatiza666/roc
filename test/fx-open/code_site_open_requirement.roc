app [main!] { pf: platform "./platform/main.roc" }

import pf.Stdout

# The platform's requirement leaves the error row of `main!` open, so
# `main!` stays generic, and its Code site is at that row. The platform's
# call is the closing use: it seals the row to the empty tag union, as
# lowering does, and describes the site there.
describe : Try({}, [Exit(I32), ..e]) -> Str
describe = |result| check(result, |r| match r {
	Ok(_) => Bool.True
	Err(_) => Bool.False
})

check : a, Code(a -> Bool) -> Str
check = |_value, code| "params ${Code.graph(code).root_row().params.len().to_str()}"

main! : List(Str) => Try({}, [Exit(I32), ..e])
main! = |_args| {
	result = Ok({})
	Stdout.line!(describe(result))
	result
}
