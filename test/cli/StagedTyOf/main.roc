# `Code.ty_of(proxy)` is the description of the type the call fixes, equal
# to the `result` of `|x| x` at that type. In a generic function it is
# computed at each use that fixes the type, as `Code.type_id` is (D6, Q8 of
# roc-reify-structural-proposal.md). A field default is in the description
# (D5): `Default` of its value where it is a literal, and `DefaultComputed`
# for a call. The defaults are declared in a package.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Med
import pa.Tbl

Pet := { name : Str, kind : [Cat, Dog] }
Owner := { name : Str, age : U32, pets : List(Pet) }

A := { x : I64 ?? 1 }
B := { x : I64 ?? 2 }

owner_proxy : Code.Proxy(Owner)
owner_proxy = Code.proxy()

record_proxy : Code.Proxy({ a : U64, b : Str })
record_proxy = Code.proxy()

list_proxy : Code.Proxy(List(Owner))
list_proxy = Code.proxy()

med_proxy : Code.Proxy(Med)
med_proxy = Code.proxy()

a_proxy : Code.Proxy(A)
a_proxy = Code.proxy()

b_proxy : Code.Proxy(B)
b_proxy = Code.proxy()

result_of : Code(t -> t) -> Code.Ty
result_of = |code| code.graph().root_row().result

same_owner : Owner -> Owner
same_owner = |o| o

same_record : { a : U64, b : Str } -> { a : U64, b : Str }
same_record = |r| r

same_list : List(Owner) -> List(Owner)
same_list = |l| l

same_med : Med -> Med
same_med = |m| m

ty_at : Code.Proxy(t) -> Code.Ty
ty_at = |p| Code.ty_of(p)

presences : Code.Ty -> Str
presences = |ty| match ty {
	Named(_, _, Record(fields)) => Str.join_with(fields.map(|f| "${f.name}=${Str.inspect(f.presence)}"), ", ")
	_ => "not a named record"
}

owners : Tbl.Tbl(Owner)
owners = Tbl.table("owner")

meds : Tbl.Tbl(Med)
meds = Tbl.table("med")

main! = || {
	Stdout.line!("owner: ${Str.inspect(Code.ty_of(owner_proxy) == result_of(same_owner))}")
	Stdout.line!("record: ${Str.inspect(Code.ty_of(record_proxy) == result_of(same_record))}")
	Stdout.line!("list: ${Str.inspect(Code.ty_of(list_proxy) == result_of(same_list))}")
	Stdout.line!("med: ${Str.inspect(Code.ty_of(med_proxy) == result_of(same_med))}")
	Stdout.line!("generic: ${Str.inspect(ty_at(owner_proxy) == Code.ty_of(owner_proxy))}")
	Stdout.line!("generic record: ${Str.inspect(ty_at(record_proxy) == Code.ty_of(record_proxy))}")
	Stdout.line!("table owner: ${Str.inspect(owners.ty() == Code.ty_of(owner_proxy))}")
	Stdout.line!("table med: ${Str.inspect(meds.ty() == Code.ty_of(med_proxy))}")
	Stdout.line!("table ids: ${Str.inspect(owners.id() == Code.type_id(owner_proxy) and meds.id() == Code.type_id(med_proxy))}")
	Stdout.line!("defaults differ: ${Str.inspect(Code.ty_of(a_proxy) != Code.ty_of(b_proxy))}")
	Stdout.line!("presence: ${presences(Code.ty_of(med_proxy))}")
}
