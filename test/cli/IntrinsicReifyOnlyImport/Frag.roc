# The module IntrinsicReifyOnlyImport/Main.roc imports. Its reify-only
# definitions reach the importing module through the checked module, and
# through the module cache.
Frag :: {}.{
	# An intrinsic.
	hot : Str -> Bool

	# Calls the intrinsic at run time.
	uses_hot = |s| Frag.hot(s)

	# Not reify-only.
	plain = |s| s.is_empty()

	Clock := { n : U64 }.{
		# An intrinsic method.
		now : Clock -> Bool
	}

	Meter := { name : Str }.{
		# A method whose body calls the intrinsic.
		now : Meter -> Bool
		now = |m| Frag.hot(m.name)
	}
}
