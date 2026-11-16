import Db

Other :: {}.{
	## A Code site at this function's own variable `a`: each written use
	## that fixes `a` gets its own description.
	render : a -> Str
	render = |x| Db.of(x).filter(|_y| Bool.True).show()
}
