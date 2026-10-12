# The module the application's staged body calls into. Both definitions are
# generic, so each row the application's table carries is one instantiation.

Shader := {}.{
	id : a -> a
	id = |v| v

	pick : a, b -> a
	pick = |p, _q| p
}
