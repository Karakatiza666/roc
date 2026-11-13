# A name a block in a top-level value binds is not fixed when its value
# reads what changes when the program runs: a `var`, which is written again,
# and a parameter of a lambda the value holds (R12).
app [main!] { st: "st/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import st.Stage

mutable = {
	var $n = "ruth"
	$n = Str.concat($n, "!")
	Stage.bind($n)
}

maker = {
	prefix = "id-"
	|k| {
		n = Str.concat(prefix, k)
		Stage.bind(n)
	}
}

main! = || {
	Stdout.line!(mutable.value())
	Stdout.line!(maker("tia").value())
}
