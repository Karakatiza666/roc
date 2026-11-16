# The argument of `Code.prim` names a top-level or imported definition, and
# `Code.prim` and `Code.type_id` are called, not read as values. The proxy of
# `Code.type_id` names a nominal type its caller fixes; in a generic function,
# the use of the function fixes it (Q8). The old tuple form of
# `code_primitives` is a type error whose hint says how to write the list.
Lib := {}.{
	max_by : List(a), (a -> k) -> Try(a, [Empty]) where [k.is_lt : k, k -> Bool]
	max_by = |xs, key| xs.fold(Err(Empty), |best, x| match best {
		Ok(b) => if key(b) < key(x) Ok(x) else Ok(b)
		Err(_) => Ok(x)
	})
}

Tr := {}.{
	code_primitives = (Lib.max_by,)

	size : Code(f) -> U64
	size = |code| code.graph().root_row().nodes.len()
}

local_id : U64 -> Code.PrimId
local_id = |n| {
	x = n + 1
	Code.prim(x)
}

open_id : Code.Proxy(t) -> Code.TypeId
open_id = |p| Code.type_id(p)

record_proxy : Code.Proxy({ a : U64 })
record_proxy = Code.proxy()

as_value = [1, 2].map(Code.prim)

main! = |_args| {
	echo!("${Str.inspect(Code.type_id(record_proxy) == Code.type_id(record_proxy))}\n")
	echo!("${Str.inspect(open_id(record_proxy))}\n")
	Ok({})
}
