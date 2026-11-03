# Query fragments of the package, and constants that hold them with no
# annotation. Nothing in the package fixes the constants' types: each use
# in the app fixes them, and describes the sites at the types it fixes.
import Db

Frag := {}.{
	named_only : Db.Q({ name : Str, ..r }) -> Db.Q({ name : Str, ..r })
	named_only = |q| q.filter(|x| x.name != "")

	adults : Db.Q({ age : U8, ..r }) -> Db.Q({ age : U8, ..r })
	adults = |q| q.filter(|x| x.age > 17)

	pair = (Frag.named_only, Frag.adults)

	both = { named: Frag.named_only, grown: Frag.adults }

	nested = { inner: Frag.pair, more: Frag.both.grown }
}
