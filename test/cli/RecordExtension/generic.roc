# A function generic over the row variable of a record extension slot, called
# where the slot holds a record, an alias of a record, a `:=` nominal, a
# nominal of another module, and a nested extension (design.md "Record
# Extension Well-Formedness"). A method on the nominal is generic the same
# way. `--specialize=no` (Boxy) runs it too.
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import Person

Labeled(r) := { label : Str, ..r }.{
	shout : Labeled(r) -> Str
	shout = |item| "${item.label}!"
}
Ref2(r) := { z : I64, ..r }
Tagged(r) : { tag : Str, ..r }

Point := { x : F64, y : F64 }
Size : { w : F64, h : F64 }

label_of : Labeled(r) -> Str
label_of = |item| item.label

nested_label : Ref2(Labeled(r)) -> Str
nested_label = |item| "${item.label} ${item.z.to_str()}"

z_and_tag : Ref2({ tag : Str, ..r }) -> Str
z_and_tag = |item| "${item.tag} ${item.z.to_str()}"

tagged_of : Tagged(r) -> Str
tagged_of = |item| item.tag

pin : Labeled(Point)
pin = Labeled.{ label: "pin", x: 1, y: 2 }

box : Labeled(Size)
box = Labeled.{ label: "box", w: 3, h: 4 }

tag : Labeled({ id : U64 })
tag = Labeled.{ label: "tag", id: 7 }

pat : Labeled(Person)
pat = Labeled.{ label: "pat", age: 40, name: "Pat" }

main! = || {
	Stdout.line!("nominal: ${label_of(pin)} ${pin.x.to_str()}")
	Stdout.line!("alias: ${label_of(box)} ${box.w.to_str()}")
	Stdout.line!("record: ${label_of(tag)} ${tag.id.to_str()}")
	Stdout.line!("imported: ${label_of(pat)} ${pat.name}")
	inner : Ref2(Labeled(Point))
	inner = Ref2.{ z: 4, label: "inner", x: 5, y: 6 }
	Stdout.line!("nested: ${nested_label(inner)}")
	Stdout.line!("chained: ${z_and_tag(Ref2.{ z: 2, tag: "t", id: 9.U64 })}")
	tagged : Tagged(Point)
	tagged = { tag: "aliased", x: 1, y: 2 }
	Stdout.line!("alias row: ${tagged_of(tagged)}")
	Stdout.line!("method: ${pin.shout()} ${box.shout()} ${pat.shout()}")
}
