# The staged function and the template both live here, and the application
# beside this file stages them. Reaching a definition in another module is the
# published view's job: it carries checked bodies and solved types, and the
# export table says which body a name leads to.

Maker := {}.{
	## An ordinary function, staged by name from another module.
	double : F32 -> F32
	double = |x| x * 2.0

	## A template, called from another module with the factor fixed there.
	scaled : F32 -> Code(F32 -> F32)
	scaled = |factor| |x| x * factor

	## A template whose argument is a function, which the calling module
	## writes and whose row the calling module's walk describes.
	twice : (F32 -> F32) -> Code(F32 -> F32)
	twice = |g| |x| g(g(x))

	## A generic function, staged by name from another module. Its scheme is
	## written here and the type fixing it is written there, so the root is
	## walked under a substitution that crosses the boundary.
	twin : a -> (a, a)
	twin = |v| (v, v)
}
