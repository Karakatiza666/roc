# A recursive type whose record holds the type itself and an explicit box of
# it. The layout commit boxes the recursive field, and that box and the
# explicit box have the same contents. They must be one layout, or two
# refcount helpers get the same symbol name.
RecursionBoxBesideExplicitBox := {}

T := [Nil, Cons({ t : T, bt : Box(T), s : Str })]

wrap : Str -> Box(T)
wrap = |s| Box.box(Cons({ t: Nil, bt: Box.box(Nil), s }))

depth : Box(T) -> I64
depth = |b| match Box.unbox(b) {
	Nil => 0
	Cons(r) => 1 + depth(r.bt) + depth(Box.box(r.t))
}

expect {
	one = wrap("x")
	two = Box.box(Cons({ t: Box.unbox(one), bt: one, s: "y" }))
	depth(two) == 3
}
