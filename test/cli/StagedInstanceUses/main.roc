# A use of a generic function that computes `Code.ty_of`, `Code.type_id` or
# a `Code` site at its own type variables is described at each use (D1).
# This holds for a method of a `::` type, here or in a package, called by
# dispatch or by its qualified name, or reached through another generic
# function. It holds too where the function does not read its parameter:
# its body depends on no run-time value, but it depends on the type the use
# fixes, so the compiler does not compute it once. A use in a top-level
# `expect` is a closing use too, here through a type declared inside
# another `::` type and a method chain.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Tb

Owner := { name : Str }

owner_proxy : Code.Proxy(Owner)
owner_proxy = Code.proxy()

result_at : Code.Proxy(t), Code(t -> t) -> Code.Ty
result_at = |_p, code| code.graph().root_row().result

Lt(row) :: { name : Str }.{
	make : Str -> Lt(row)
	make = |name| Lt.({ name: name })

	ty : Lt(row) -> Code.Ty
	ty = |lt| {
		_ = lt
		proxy : Code.Proxy(row)
		proxy = Code.proxy()
		Code.ty_of(proxy)
	}

	id : Lt(row) -> Code.TypeId
	id = |_lt| {
		proxy : Code.Proxy(row)
		proxy = Code.proxy()
		Code.type_id(proxy)
	}

	same : Lt(row) -> Code.Ty
	same = |_lt| {
		proxy : Code.Proxy(row)
		proxy = Code.proxy()
		result_at(proxy, |x| x)
	}
}

Nt(row) := { name : Str }.{
	ty : Nt(row) -> Code.Ty
	ty = |_nt| {
		proxy : Code.Proxy(row)
		proxy = Code.proxy()
		Code.ty_of(proxy)
	}
}

via_local : Lt(row) -> Code.Ty
via_local = |lt| lt.ty()

via_package : Tb.Tb(row) -> Code.TypeId
via_package = |tb| tb.id()

ty_at : List(row) -> Code.Ty
ty_at = |_l| {
	proxy : Code.Proxy(row)
	proxy = Code.proxy()
	Code.ty_of(proxy)
}

id_at : List(row) -> Code.TypeId
id_at = |_l| {
	proxy : Code.Proxy(row)
	proxy = Code.proxy()
	Code.type_id(proxy)
}

ty_of_proxy : Code.Proxy(t) -> Code.Ty
ty_of_proxy = |p| Code.ty_of(p)

forward_at : List(row) -> Code.Ty
forward_at = |_l| {
	proxy : Code.Proxy(row)
	proxy = Code.proxy()
	ty_of_proxy(proxy)
}

Outer :: {}.{
	Tbl(row) :: { name : Str }.{
		define : Tbl(row) -> Def(row)
		define = |Tbl.(t)| {
			proxy : Code.Proxy(row)
			proxy = Code.proxy()
			Def.({ name: t.name, ty: Code.ty_of(proxy) })
		}
	}

	Def(row) :: { name : Str, ty : Code.Ty }.{
		ty : Def(row) -> Code.Ty
		ty = |Def.(d)| d.ty
	}

	table : Str -> Tbl(row)
	table = |name| Tbl.({ name: name })
}

outer_owners : Outer.Tbl(Owner)
outer_owners = Outer.table("owner")

expect outer_owners.define().ty() == Code.ty_of(owner_proxy)
local_owners : Lt(Owner)
local_owners = Lt.make("owner")

owner_list : List(Owner)
owner_list = []

expect local_owners.id() == Code.type_id(owner_proxy)
expect ty_at(owner_list) == Code.ty_of(owner_proxy)
expect forward_at(owner_list) == Code.ty_of(owner_proxy)

main! = || {
	owner_ty = Code.ty_of(owner_proxy)
	owner_id = Code.type_id(owner_proxy)
	locals : Lt(Owner)
	locals = Lt.make("owner")
	packaged : Tb.Tb(Owner)
	packaged = Tb.make("owner")
	nominal : Nt(Owner)
	nominal = Nt.({ name: "owner" })
	owners : List(Owner)
	owners = []
	Stdout.line!("local dispatch: ${Str.inspect(locals.ty() == owner_ty and locals.id() == owner_id)}")
	Stdout.line!("local qualified: ${Str.inspect(Lt.ty(locals) == owner_ty and Lt.id(locals) == owner_id)}")
	Stdout.line!("local site: ${Str.inspect(locals.same() == owner_ty)}")
	Stdout.line!("local forward: ${Str.inspect(via_local(locals) == owner_ty)}")
	Stdout.line!("package dispatch: ${Str.inspect(packaged.ty() == owner_ty and packaged.id() == owner_id)}")
	Stdout.line!("package qualified: ${Str.inspect(Tb.ty(packaged) == owner_ty and Tb.id(packaged) == owner_id)}")
	Stdout.line!("package forward: ${Str.inspect(via_package(packaged) == owner_id)}")
	Stdout.line!("nominal unused: ${Str.inspect(nominal.ty() == owner_ty)}")
	Stdout.line!("unused ty: ${Str.inspect(ty_at(owners) == owner_ty)}")
	Stdout.line!("unused id: ${Str.inspect(id_at(owners) == owner_id)}")
	Stdout.line!("unused forward: ${Str.inspect(forward_at(owners) == owner_ty)}")
}
