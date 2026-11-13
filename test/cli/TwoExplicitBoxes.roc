# A recursive type whose record holds two explicit boxes of the type itself,
# and the type itself. The two boxes have the same contents, so they must be
# one layout, or two refcount helpers get the same symbol name.
TwoExplicitBoxes := {}

T := [Nil, Cons({ a : Box(T), b : Box(T), t : T, s : Str })]

leaf : Str -> T
leaf = |s| Cons({ a: Box.box(Nil), b: Box.box(Nil), t: Nil, s })

depth : T -> I64
depth = |t| match t {
	Nil => 0
	Cons(r) => 1 + depth(Box.unbox(r.a)) + depth(Box.unbox(r.b)) + depth(r.t)
}

expect {
	one = leaf("x")
	two = Cons({ a: Box.box(one), b: Box.box(leaf("y")), t: one, s: "z" })
	depth(two) == 4
}
