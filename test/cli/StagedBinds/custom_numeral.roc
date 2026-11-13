# A number literal of an opaque type with its own `from_numeral`, written as
# a whole value at a `Code.Binds` position (R12). Its type holds an opaque
# type, so it is one input slot: the program converts the literal where the
# call stands and writes it with the type's `encoder_for`. The node of the
# literal holds the `Code`, so the conversion is read at the value's type.
#
# The `a` of `Code.Binds(Code(Time), Fmt)` is known where the value is
# written, so a value whose own type is still a variable there is decided
# at once too: a literal with no suffix, and a call of a function that is
# generic in what it returns.
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
	since : Code.Binds(Code(Time), Fmt) -> Code.Bound(Str)
	since = |code| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")

	show : Code.Value -> Str
	show = |value| match value {
		Encoded(bytes) => "Encoded(${Str.from_utf8_lossy(bytes)})"
		_ => "other"
	}
}

shown : Code.Bound(Str) -> Str
shown = |bound| "${bound.value()}: ${Str.join_with(bound.inputs().map(Stage.show), ", ")}"

suffixed : {} -> Str
suffixed = |{}| shown(Stage.since(41.Time))

unsuffixed : {} -> Str
unsuffixed = |{}| shown(Stage.since(42))

# Generic in what it returns: the place decides the type.
zero_of : {} -> a where [a.zero : () -> a]
zero_of = |{}| {
	A : a
	A.zero()
}

generic : {} -> Str
generic = |{}| shown(Stage.since(zero_of({})))

main! = || {
	Stdout.line!("suffixed: ${suffixed({})}")
	Stdout.line!("unsuffixed: ${unsuffixed({})}")
	Stdout.line!("generic: ${generic({})}")
}
