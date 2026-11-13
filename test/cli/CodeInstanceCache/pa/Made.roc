# Calls a stored function of Pick: this module has no table of its own.
import Db
import Pick

Made := {}.{
	run : Db.Q(Pick.Tag) -> Db.Q(Pick.Tag)
	run = |q| Pick.made(q)
}
