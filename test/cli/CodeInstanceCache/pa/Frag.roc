# Fragments with instance sites, and a helper a description reads.
import Db

Frag := {}.{
	named_only : Db.Q({ name : Str, ..r }) -> Db.Q({ name : Str, ..r })
	named_only = |q| q.filter(|x| x.name != "frag-one")

	kept : Db.Q(a) -> Db.Q(a) where [a.keep : a -> Bool]
	kept = |q| q.filter(|x| x.keep())

	check : Str -> Bool
	check = |s| s != "check-one"
}
