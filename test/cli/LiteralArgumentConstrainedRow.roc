# A local generic function with a numeric literal, called with a value whose
# type names a constrained row variable of the enclosing function. The
# literal's own type is closed, so it has a literal argument root, and the
# root never enters `make`, so no scope binds `new` (issue 13085).
LiteralArgumentConstrainedRow := [].{
	make : { id : Str, ..new } -> U64 where [new.describe : new -> Str]
	make = |whole| {
		built = |x| { count: 1, got: x }
		built(whole).count
	}
}
