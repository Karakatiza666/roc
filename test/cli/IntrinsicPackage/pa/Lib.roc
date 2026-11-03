# Helpers that reach the intrinsics. Each is reify-only: it can be described
# in a clause, and it is an error where it runs.
import Db
import Hit
import Text

Lib := {}.{
	hot = |s| Text.is_email(s)

	ranked : Hit -> U64
	ranked = |hit| hit.score() + 1

	inner = |x| x.now()

	outer = |t| Lib.inner(t)

	named_only = |q| Db.Q.filter(q, |x| Text.is_email(x.e))
}
