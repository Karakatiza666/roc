# A lambda passed to a method that takes a `Code`, in a helper whose receiver
# has no annotation. The receiver's type is not known when the lambda is
# checked, so the lambda is a plain function, and the report says to annotate
# the receiver. The `dbg` of the value that never resolves lowers for its
# effect.
Q := { n : U64 }.{
	keep : Q, Code(U64 -> Bool) -> Q
	keep = |Q.(q), code| Q.({ n: q.n + Code.graph(code).root_row().params.len() })

	size : Q -> U64
	size = |Q.(q)| q.n
}

helper = |q| q.keep(|x| x > 1)

expect {
	dbg helper(Q.({ n: 0 })).size()
	Bool.True
}
