# A name a block in a top-level value binds to a value fixed while the
# compiler runs is fixed too, so a value at a `Code` position that reads it
# is a literal, as the value written there is (R12).
app [main!] { st: "st/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import st.Stage

shown_bound : Code.Bound(Str) -> Str
shown_bound = |b| "${b.value()} inputs ${b.inputs().len().to_str()}"

text = {
	n = "ruth"
	Stage.bind(n)
}

record = {
	t = "vet"
	r = { table: t, key: "ruth" }
	Stage.bind(r)
}

nested = {
	a = "o"
	b = {
		c = Str.concat(a, "k")
		c
	}
	Stage.bind(b)
}

destructured = {
	{ table, key } = { table: "vet", key: "tia" }
	Stage.bind({ table, key })
}

main! = || {
	Stdout.line!("text: ${shown_bound(text)}")
	Stdout.line!("record: ${shown_bound(record)}")
	Stdout.line!("nested: ${shown_bound(nested)}")
	Stdout.line!("destructured: ${shown_bound(destructured)}")
}
