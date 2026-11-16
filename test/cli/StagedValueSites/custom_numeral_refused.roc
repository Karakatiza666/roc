# A number literal of a type with its own `from_numeral`, written as a whole
# value at a plain `Code(a)` position (R12). It is a fixed value, so the walk
# computes it into a literal. Its conversion reaches the builtin
# `I128.from_numeral`, a primitive the walk does not compute, so the value
# is refused, with or without the type written at the literal.
app [main!] { st: "st/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import st.Stage

# A count whose backing is visible, with a number literal conversion.
Count := { n : I128 }.{
	from_numeral : Numeral -> Try(Count, [InvalidNumeral(Str)])
	from_numeral = |numeral| {
		Inner : I128
		match Inner.from_numeral(numeral) {
			Ok(n) => Ok(Count.({ n: n }))
			Err(err) => Err(err)
		}
	}
}

show_count : Code(Count) -> Str
show_count = |code| Stage.describe(code)

typed : {} -> Str
typed = |{}| show_count(41.Count)

untyped : {} -> Str
untyped = |{}| show_count(42)

main! = || {
	Stdout.line!("typed: ${typed({})}")
	Stdout.line!("untyped: ${untyped({})}")
}
