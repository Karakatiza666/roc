# A query translator of the package.
import Prepared

Q := [Q(Str)].{
	from : Str -> Q
	from = |name| Q(name)

	filter : Q, Code(U16 -> Bool) -> Q
	filter = |Q(text), code| Q("${text} slots ${Code.graph(code).slots().len().to_str()}")

	ready : Q -> Prepared(Str)
	ready = |Q(text)| Prepared.of(text)
}
