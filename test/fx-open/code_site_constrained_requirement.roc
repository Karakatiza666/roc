app [main!] { pf: platform "./platform/main.roc" }

import pf.Stdout

# The error row of `main!` stays open with a method its `where` clause
# requires. The platform's call is the closing use, and it fixes the row to
# the empty tag union, which has no `zap`, so the Code site in `describe` is
# refused at `main!`.
describe : Try({}, [Exit(I32), ..e]) -> Str where [e.zap : e -> Str]
describe = |result| check(result, |r| match r {
	Ok(_) => Bool.True
	Err(_) => Bool.False
})

check : a, Code(a -> Bool) -> Str
check = |_value, code| "params ${Code.graph(code).root_row().params.len().to_str()}"

main! : List(Str) => Try({}, [Exit(I32), ..e]) where [e.zap : e -> Str]
main! = |_args| {
	result = Ok({})
	Stdout.line!(describe(result))
	result
}
