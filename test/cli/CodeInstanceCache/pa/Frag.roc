# Fragments with instance sites, and a helper a description reads.
import Db

Frag := {}.{
	named_only : Db.Q({ name : Str, ..r }) -> Db.Q({ name : Str, ..r })
	named_only = |q| q.filter(|x| x.name != "frag-one")

	kept : Db.Q(a) -> Db.Q(a) where [a.keep : a -> Bool]
	kept = |q| q.filter(|x| x.keep())

	check : Str -> Bool
	check = |s| s != "check-one"

	## A method the compiler calls for inspection, with a site at its own
	## variable (Q17): each type occurrence of `Rows` describes it.
	Rows(r) := { q : Db.Q({ name : Str, ..r }) }.{
		to_inspect : Rows(r) -> Str
		to_inspect = |rows| rows.q.filter(|x| x.name != "rows-one").show()
	}
}
