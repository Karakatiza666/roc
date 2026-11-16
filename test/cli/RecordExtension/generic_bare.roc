# A function generic over `r` in `Ref(r) := { ..r }`, a nominal that is only
# its extension, called where `r` is a record, an alias of a record, a `:=`
# nominal and a nominal of another module (design.md "Record Extension
# Well-Formedness"). The Monotype lowering runs it. Boxy (`--specialize=no`)
# does not yet lower a record that is only a row variable (`{ ..r }`), also
# without a nominal.
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import Person

Ref(r) := { ..r }

Point := { x : F64, y : F64 }
Size : { w : F64, h : F64 }

kind_of : Ref(r) -> Str
kind_of = |_item| "ref"

x_of : Ref({ x : F64, ..r }) -> F64
x_of = |item| item.x

main! = || {
	id : Ref({ id : U64 })
	id = Ref.{ id: 7 }
	size : Ref(Size)
	size = Ref.{ w: 3, h: 4 }
	point : Ref(Point)
	point = Ref.{ x: 1, y: 2 }
	person : Ref(Person)
	person = Ref.{ age: 40, name: "Pat" }
	Stdout.line!("record: ${kind_of(id)} ${id.id.to_str()}")
	Stdout.line!("alias: ${kind_of(size)} ${size.w.to_str()}")
	Stdout.line!("nominal: ${kind_of(point)} ${x_of(point).to_str()}")
	Stdout.line!("imported: ${kind_of(person)} ${person.name}")
}
