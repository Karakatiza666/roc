# A codec method bound to a function of another module that holds a Code
# site is refused at the method (Q17). A call of a format function that
# selects the method by type through `where` evidence is refused too, and
# both lowerings read the refused method as a rejected declaration, so the
# call crashes.
import Db
import Other

There(r) := { row : r }.{
	encoder_for = Other.encode
}

main! = |_args| {
	t : There(Str)
	t = There.({ row: "x" })
	echo!("t: ${Json.to_str(t)}\n")
	Ok({})
}
