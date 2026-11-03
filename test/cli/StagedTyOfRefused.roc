# `Code.ty_of` of a proxy whose type the call leaves open is refused at the
# call, and at a use of a generic function that leaves it open, where the
# report names the call the use reaches. `Code.type_id` in a generic
# function is refused at a use that fixes its proxy to no nominal. Both are
# refused in a method the compiler calls with no written use (Q17), and
# `Code.ty_of` is only ever called.
open_proxy = Code.proxy()

ty_at : Code.Proxy(t) -> Code.Ty
ty_at = |p| Code.ty_of(p)

id_at : Code.Proxy(t) -> Code.TypeId
id_at = |p| Code.type_id(p)

record_proxy : Code.Proxy({ a : U64 })
record_proxy = Code.proxy()

Shown(a) := { value : a }.{
	to_inspect : Shown(a) -> Str
	to_inspect = |_| {
		proxy : Code.Proxy(a)
		proxy = Code.proxy()
		Str.inspect(Code.ty_of(proxy))
	}
}

main! = |_args| {
	echo!("${Str.inspect(Code.ty_of(open_proxy))}\n")
	echo!("${Str.inspect(ty_at(record_proxy))}\n")
	echo!("${Str.inspect(id_at(record_proxy))}\n")
	echo!("${Str.inspect(ty_at(open_proxy))}\n")
	echo!("${Str.inspect([record_proxy].map(Code.ty_of))}\n")
	Ok({})
}
