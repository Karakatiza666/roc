# A generic function of the package whose `Code.Bound` call has the
# function's open row in its type. The package has no instance of it: each
# use that fixes the row binds the call's input.
import Q

F := {}.{
	fetch : U16 -> Code.Bound(Try(Str, [NotFound, ..e]))
	fetch = |least| Q.from("meds").filter(|m| m > least).ready()
}
