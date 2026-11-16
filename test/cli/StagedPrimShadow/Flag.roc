# A module of the app whose type has a method with the name of the builtin's
# method `Bool.not`.
Flag :: { n : I64 }.{
	not : Flag -> Flag
	not = |Flag.(b)| Flag.{ n: 1 - b.n }

	level : Flag -> I64
	level = |Flag.(b)| b.n
}
