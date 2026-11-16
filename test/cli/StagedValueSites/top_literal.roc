# A literal written at a `Code` position in a top-level value is fixed while
# the compiler runs, so it is described as a literal, as it is through a
# name or inside a function (R12). A call that binds inputs gets none.
app [main!] { st: "st/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import st.Stage

shown_bound : Code.Bound(Str) -> Str
shown_bound = |b| "${b.value()} inputs ${b.inputs().len().to_str()}"

text = Stage.bind("ruth")

record = Stage.bind({ table: "vet", key: "ruth" })

nested = Stage.bind([{ key: "a" }, { key: "b" }])

main! = || {
	Stdout.line!("text: ${shown_bound(text)}")
	Stdout.line!("record: ${shown_bound(record)}")
	Stdout.line!("nested: ${shown_bound(nested)}")
}
