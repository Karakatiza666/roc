# The module IntrinsicRunsBitImport/Main.roc imports. Its generic
# definitions' `runs` bits must reach the importing module with their
# schemes.
Frag :: {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, _code| q
	}

	# Used only inside a lambda written at a `Code` place.
	frag = |q| Q.filter(q, |x| x.t.now())

	# Used at run time.
	run = |x| x.now()
}
