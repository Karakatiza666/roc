# A type whose method is bound to a computed callable of another module.
# Checking a use in another module copies the binding's type, so the
# binding keeps its free variable.
import Mk

Par(r) := { row : r }.{
	label = Mk.make({})
}
