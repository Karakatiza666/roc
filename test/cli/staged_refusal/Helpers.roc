# A helper that a translated function in another module calls.
Helpers := {}.{
	step : U16 -> U16
	step = |x| x * 3

	# Reaches `step` through a call in this module (see nested.roc).
	bumped : U16 -> U16
	bumped = |x| step(x) + 1
}
