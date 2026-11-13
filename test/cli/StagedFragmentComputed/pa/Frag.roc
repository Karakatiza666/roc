# Top-level values of the package that compute a query fragment, with no
# annotation. Such a value does not generalize, but nothing in the package
# fixes its row, so each use in another module fixes it, and the value's
# entry wrapper describes the sites at the types that use fixes.
import Db

Frag := {}.{
	named_only : Db.Q({ name : Str, ..r }) -> Db.Q({ name : Str, ..r })
	named_only = |q| q.filter(|x| x.name != "")

	adults : Db.Q({ age : U8, ..r }) -> Db.Q({ age : U8, ..r })
	adults = |q| q.filter(|x| x.age > 17)

	pick = if Bool.True Frag.named_only else Frag.named_only

	# A value computed from another such value of this module: its use of
	# `pick` is at its own row too.
	pick_again = if Bool.True Frag.pick else Frag.pick
}
