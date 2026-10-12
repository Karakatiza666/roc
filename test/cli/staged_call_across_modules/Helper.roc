# The module the application's staged body calls into. Its own callee lives in
# a third module, which the application never imports.

import Deeper

Helper := {}.{
	twice : F32 -> F32
	twice = |x| Deeper.inner(x) * 2.0
}
