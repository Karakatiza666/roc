# A module of the app that declares its own `Bool`, with the name of a
# builtin type and of the builtin's method `not`.
Bool :: { n : I64 }.{
	not : Bool -> Bool
	not = |Bool.(b)| Bool.{ n: 1 - b.n }

	level : Bool -> I64
	level = |Bool.(b)| b.n
}
