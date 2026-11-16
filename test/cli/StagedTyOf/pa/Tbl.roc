# A table handle that holds the description and the identity of its row
# type, computed where a use fixes `row` (D6, Q8).
Tbl(row) := { name : Str, ty : Code.Ty, id : Code.TypeId }.{
	table : Str -> Tbl(row)
	table = |name| {
		proxy : Code.Proxy(row)
		proxy = Code.proxy()
		Tbl.({ name, ty: Code.ty_of(proxy), id: Code.type_id(proxy) })
	}

	ty : Tbl(row) -> Code.Ty
	ty = |Tbl.(t)| t.ty

	id : Tbl(row) -> Code.TypeId
	id = |Tbl.(t)| t.id
}
