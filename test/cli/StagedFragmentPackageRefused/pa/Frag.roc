# A fragment whose site reads a function that builds an opaque record. The
# package has no description of the site, so the refusal comes at the use
# that fixes the fragment's types.
import Db

Stamp :: { n : I64 }.{
	n_of : Stamp -> I64
	n_of = |s| s.n
}

Frag := {}.{
	shifted : I64 -> I64
	shifted = |n| Stamp.n_of(Stamp.{ n }) + 1

	recent : Db.Q({ age : I64, ..r }) -> Db.Q({ age : I64, ..r })
	recent = |q| q.filter(|x| Frag.shifted(x.age) > 3)
}
