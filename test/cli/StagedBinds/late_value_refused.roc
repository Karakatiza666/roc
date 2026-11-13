# A value at a `Code.Binds(Code(a), fmt)` position whose type holds an opaque
# type is one input slot when its type is known where it is written (R12).
# Here the translator's `a` is a type variable at the value's place, and only
# a later argument fixes it to `Time`. The checker decides what the value is
# where it is written, so no call binds it, and a `Time` has no literal. The
# report says to write the type at the value.
app [main!] { pt: "pt/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pt.Time

# The translator's format: it writes each number as its decimal digits.
Fmt := [Default].{
	default : () -> Fmt
	default = || Default

	encode_i128 : I128, List(U8) -> Try(List(U8), [])
	encode_i128 = |n, out| Ok(out.concat(n.to_str().to_utf8()))
}

Stage := {}.{
	pair : Code.Binds(Code(a), Fmt), a -> Code.Bound(Str)
	pair = |code, _other| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")
}

numeral : {} -> Str
numeral = |{}| Stage.pair(41, Time.from_nanos(1)).value()

# Generic in what it returns: the place decides the type.
zero_of : {} -> a where [a.zero : () -> a]
zero_of = |{}| {
	A : a
	A.zero()
}

generic : {} -> Str
generic = |{}| Stage.pair(zero_of({}), Time.from_nanos(1)).value()

# Written with its type, the same value is one encoded input slot.
typed : {} -> Str
typed = |{}| Stage.pair(41.Time, Time.from_nanos(1)).value()

main! = || {
	Stdout.line!("typed: ${typed({})}")
	Stdout.line!("numeral: ${numeral({})}")
	Stdout.line!("generic: ${generic({})}")
}
