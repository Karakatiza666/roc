# An opaque table handle. Its methods compute the description and the
# identity of its row type at each use that fixes `row` (D1, D6). A method
# of a `::` type is a primitive for a description, but the program runs it,
# so a use of it carries the instance table of the method. `id` does not
# read its parameter, so its body is a value the compiler could compute
# once, but that value depends on `row`.
Tb(row) :: { name : Str }.{
	make : Str -> Tb(row)
	make = |name| Tb.({ name: name })

	ty : Tb(row) -> Code.Ty
	ty = |tb| {
		_ = tb
		proxy : Code.Proxy(row)
		proxy = Code.proxy()
		Code.ty_of(proxy)
	}

	id : Tb(row) -> Code.TypeId
	id = |_tb| {
		proxy : Code.Proxy(row)
		proxy = Code.proxy()
		Code.type_id(proxy)
	}
}
