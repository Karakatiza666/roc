# `Code.prim(f)` is the `PrimId` of the definition `f` names, and
# `Code.type_id(proxy)` is the `TypeId` of the nominal the proxy names. Each
# equals the id the description of a call or a type of that definition
# carries. A generic function with a `where` clause can be in a cut. A
# nominal of the builtin module that the checker marks as no builtin, such as
# `Hasher` or `Code.PrimId`, is named and identified as a builtin is.
Time :: { nanos : I128 }.{
	from_nanos : I128 -> Time
	from_nanos = |n| Time.{ nanos: n }

	is_before : Time, Time -> Bool
	is_before = |a, b| a.nanos < b.nanos
}

Lib := {}.{
	max_by : List(a), (a -> k) -> Try(a, [Empty]) where [k.is_lt : k, k -> Bool]
	max_by = |xs, key| xs.fold(Err(Empty), |best, x| match best {
		Ok(b) => if key(b) < key(x) Ok(x) else Ok(b)
		Err(_) => Ok(x)
	})
}

Tr := {}.{
	twice : U64 -> U64
	twice = |x| x * 2

	code_primitives = [Code.prim(Tr.twice), Code.prim(Lib.max_by)]

	ids : Code(f) -> List(Code.PrimId)
	ids = |code| code.graph().root_row().nodes.keep_oks(|node| match node.op {
		Prim(p) => Ok(p.id)
		_ => Err(NotPrim)
	})

	types : Code(f) -> List(Code.TypeId)
	types = |code| code.graph().root_row().params.keep_oks(|ty| match ty {
		Opaque(_, id, _) => Ok(id)
		_ => Err(NotOpaque)
	})

	names : Code(f) -> Str
	names = |code| Str.join_with(code.graph().root_row().nodes.keep_oks(|node| match node.op {
		Prim(p) => Ok("${p.owner}.${p.method}")
		_ => Err(NotPrim)
	}), ", ")

	type_names : Code(f) -> Str
	type_names = |code| Str.join_with(code.graph().root_row().params.map(|ty| ty.name()), ", ")
}

before : Time, Time -> Bool
before = |a, b| a.is_before(b)

wobble : U64 -> U64
wobble = |x| Tr.twice(x) + 1

biggest : List(I64) -> Try(I64, [Empty])
biggest = |xs| Lib.max_by(xs, |x| x)

joined : Str, Str -> Str
joined = |a, b| Str.concat(a, b)

holds : Dict(Str, I64), Str -> Bool
holds = |d, k| d.contains(k)

hashes : Hasher, Code.PrimId -> Hasher
hashes = |h, _p| h

hasher_proxy : Code.Proxy(Hasher)
hasher_proxy = Code.proxy()

prim_id_proxy : Code.Proxy(Code.PrimId)
prim_id_proxy = Code.proxy()

time_proxy : Code.Proxy(Time)
time_proxy = Code.proxy()

dict_proxy : Code.Proxy(Dict(Str, I64))
dict_proxy = Code.proxy()

main! = |_args| {
	echo!("is_before: ${Str.inspect(Tr.ids(before) == [Code.prim(Time.is_before)])}\n")
	echo!("twice: ${Str.inspect(Tr.ids(wobble).first() == Ok(Code.prim(Tr.twice)))}\n")
	echo!("twice is not concat: ${Str.inspect(Code.prim(Str.concat) != Code.prim(Tr.twice))}\n")
	echo!("concat: ${Str.inspect(Tr.ids(joined) == [Code.prim(Str.concat)])}\n")
	echo!("time type: ${Str.inspect(Tr.types(before) == [Code.type_id(time_proxy), Code.type_id(time_proxy)])}\n")
	echo!("dict type: ${Str.inspect(Tr.types(holds) == [Code.type_id(dict_proxy)])}\n")
	echo!("time is not dict: ${Str.inspect(Code.type_id(time_proxy) != Code.type_id(dict_proxy))}\n")
	echo!("max_by: ${Tr.names(biggest)}\n")
	echo!("concat name: ${Tr.names(joined)}\n")
	echo!("dict name: ${Tr.type_names(holds)}\n")
	echo!("hasher type: ${Str.inspect(Tr.types(hashes) == [Code.type_id(hasher_proxy), Code.type_id(prim_id_proxy)])}\n")
	echo!("hasher name: ${Tr.type_names(hashes)}\n")
	Ok({})
}
