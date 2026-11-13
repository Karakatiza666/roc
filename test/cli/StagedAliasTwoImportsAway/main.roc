# A use of an exact alias that another module exports, of a function of a
# module this module does not import, whose Code site is at the function's
# own variable. This module has no site, and its only import holds no
# inventory, so only the import's own import holds the inventory the use
# closes.
import B

main! = |_args| {
	q = B.start("pet")
	echo!("${B.only_named(q).show()}\n")
	Ok({})
}
