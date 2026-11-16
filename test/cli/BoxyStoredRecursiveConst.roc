# Compile-time constants of a recursive type, restored from the const store
# under Boxy. The layout stores a field on the type's cycle boxed: the second
# payload of `Named`, the `ty` field of a `Record` entry, and the second item
# of the tuple `pair`. The restore boxes each such field.
Ty := [Leaf, Named(Str, Ty), ListOf(Ty), Record(List({ name : Str, ty : Ty }))]

depth : Ty -> U64
depth = |ty| match ty {
	Leaf => 0
	Named(_, inner) => depth(inner) + 1
	ListOf(inner) => depth(inner) + 1
	Record(fields) => fields.fold(0, |acc, field| acc.max(depth(field.ty))) + 1
}

wrap : Str, Ty -> Ty
wrap = |name, inner| Ty.Named(name, Ty.ListOf(inner))

named : Ty
named = wrap("a", Ty.Record([{ name: "x", ty: wrap("b", Ty.Leaf) }]))

pair : (Str, Ty)
pair = ("p", wrap("c", Ty.Leaf))

expect depth(named) == 5
expect depth(pair.1) == 2
