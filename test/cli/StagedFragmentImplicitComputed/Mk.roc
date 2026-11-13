import Db

Mk :: {}.{
	## A closure that holds a Code site at this function's own variable `a`.
	make : {} -> (a -> Str)
	make = |{}| |x| Db.of(x).filter(|_y| Bool.True).show()
}
