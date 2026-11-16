# A record extension slot accepts a record-backed `:=` nominal, through a
# nominal and through an alias, with head fields and with a self link
# (design.md "Record Extension Well-Formedness", structural proposal t1, t6,
# t7, t9, t10).
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout

Ref(r) := { ..r }
Ref2(r) := { z : I64, ..r }
Ext(r) : { z : I64, ..r }
A(r) : { ..r }

Owner := { id : Str, name : Str }
Boss := { id : Str, boss : [None, Some(Ref(Boss))] }

through_nominal : Ref(Owner) -> Str
through_nominal = |o| o.name

with_head : Ref2(Owner) -> Str
with_head = |o| "${o.name} ${o.z.to_str()}"

through_alias : Ext(Owner) -> Str
through_alias = |o| "${o.name} ${o.z.to_str()}"

through_bare_alias : A(Owner) -> Str
through_bare_alias = |o| o.name

boss_id : Boss -> Str
boss_id = |b| match b.boss {
	None => "none"
	Some(up) => up.id
}

main! = || {
	Stdout.line!("nominal: ${through_nominal(Ref.{ id: "a", name: "Ada" })}")
	Stdout.line!("head: ${with_head(Ref2.{ z: 2, id: "b", name: "Bob" })}")
	Stdout.line!("alias: ${through_alias({ z: 3, id: "c", name: "Cy" })}")
	Stdout.line!("bare alias: ${through_bare_alias({ id: "d", name: "Di" })}")
	low : Boss
	low = { id: "2", boss: Some(Ref.{ id: "1", boss: None }) }
	Stdout.line!("self link: ${boss_id(low)}")
}
