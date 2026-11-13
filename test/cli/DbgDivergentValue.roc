# A `dbg` of a value that never resolves, in an `expect`. `grow` takes one
# argument and the helper passes two, so the dispatch in `helper` is rejected
# and `size` has no receiver type. Checking reports the error, and `dbg` of
# the divergent value lowers for its effect: it has no value to render.
Q := { n : U64 }.{
	grow : Q, U64 -> Q
	grow = |Q.(q), k| Q.({ n: q.n + k })

	size : Q -> U64
	size = |Q.(q)| q.n
}

helper = |q| q.grow(1, 2)

expect {
	dbg helper(Q.({ n: 0 })).size()
	Bool.True
}
