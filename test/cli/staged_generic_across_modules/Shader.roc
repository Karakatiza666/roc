# The module the application's staged body calls into. The definition is
# generic, so each row the application's table carries is one instantiation.

Shader := {}.{
	single : a -> List(a)
	single = |v| [v]
}
