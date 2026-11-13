# Record extension shapes that both lowerings read through a `:=` nominal's
# backing (design.md "Record Extension Well-Formedness"): nested, chained,
# generic, from another module, with head fields, as constants and inspected.
# `--specialize=no` (Boxy) runs it too.
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import Person

Ref(r) := { ..r }
Ref2(r) := { z : I64, ..r }
Tagged(r) := { tag : Str, ..r }
Pair(a) := { first : a, label : Str }
Ext(r) : { z : I64, ..r }
Mid(r) : { m : Str, ..r }

Owner := { id : Str, name : Str }

nested : Ref(Ref(Owner)) -> Str
nested = |o| o.name

chained : Ref2(Tagged(Owner)) -> Str
chained = |o| "${o.tag} ${o.name} ${o.z.to_str()}"

generic : Ref(Pair(I64)) -> Str
generic = |o| "${o.label} ${o.first.to_str()}"

imported : Ref2(Person) -> Str
imported = |o| "${o.name} ${o.age.to_str()} ${o.z.to_str()}"

interleaved : Mid(Person) -> Str
interleaved = |o| "${o.m} ${o.name} ${o.age.to_str()}"

head_const : Ref2(Owner)
head_const = Ref2.{ z: 9, id: "n", name: "Nan" }

ext_const : Ext(Owner)
ext_const = { z: 4, id: "e", name: "Eve" }

main! = || {
	Stdout.line!("nested: ${nested(Ref.{ id: "a", name: "Ada" })}")
	Stdout.line!("chained: ${chained(Ref2.{ z: 2, tag: "t", id: "b", name: "Bob" })}")
	Stdout.line!("generic: ${generic(Ref.{ first: 5, label: "five" })}")
	Stdout.line!("imported: ${imported(Ref2.{ z: 3, age: 40, name: "Pat" })}")
	mid : Mid(Person)
	mid = { m: "mid", age: 7, name: "Max" }
	Stdout.line!("interleaved: ${interleaved(mid)}")
	Stdout.line!("inspect mid: ${Str.inspect(mid)}")
	Stdout.line!("head const: ${Str.inspect(head_const)}")
	Stdout.line!("ext const: ${Str.inspect(ext_const)}")
}
