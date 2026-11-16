app [main!] { pf: platform "./platform/main.roc" }

import pf.Stdout

# The platform's requirement `main! : () => {}` leaves nothing open, so the
# use of `describe` in `main!` is the closing use of its Code site.
describe : [A, ..e] -> Str
describe = |value| check(value, |v| match v {
	A => Bool.True
	_ => Bool.False
})

check : a, Code(a -> Bool) -> Str
check = |_value, code| "params ${Code.graph(code).root_row().params.len().to_str()}"

main! = || Stdout.line!(describe(A))
