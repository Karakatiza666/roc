# A fixed value at a `Code` position is computed through the functions it
# calls, also through an operation of an opaque type (R12). Only the type of
# the value must hold no opaque type. A value whose type holds one has no
# literal, and is refused.
app [main!] { st: "st/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import st.Stage
import st.Table
import st.Id

MyId := { table : Str, key : Str }

Opq :: { name : Str }.{
	id : Opq, Str -> MyId
	id = |Opq.(t), key| MyId.({ table: t.name, key })
}

opq : Opq
opq = Opq.({ name: "vet" })

vets : Table
vets = Table.named("vet")

show_id : Code(MyId) -> Str
show_id = |code| Stage.describe(code)

show_table_id : Code(Id) -> Str
show_table_id = |code| Stage.describe(code)

ruth : MyId
ruth = opq.id("ruth")

top = show_id(ruth)

inline = show_id(opq.id("ruth"))

in_function : U64 -> Str
in_function = |_n| show_id(opq.id("ruth"))

package_id = show_table_id(vets.id("tia"))

main! = || {
	Stdout.line!("top: ${top}")
	Stdout.line!("inline: ${inline}")
	Stdout.line!("in function: ${in_function(1)}")
	Stdout.line!("package: ${package_id}")
}
