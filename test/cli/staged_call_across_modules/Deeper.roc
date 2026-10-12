# The third module: reached only by a call inside `Helper`'s description, so
# nothing the application wrote names it.

Deeper := {}.{
	inner : F32 -> F32
	inner = |x| x + 1.0
}
