Q := { n : U64 }.{
	filter : Q, Code({ name : Str } -> Bool) -> Q
	filter = |q, _c| { n: q.n + 1 }
}
