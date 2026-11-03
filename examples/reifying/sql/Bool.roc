# A module of the application that declares its own `Bool`, for
# `extensions.roc`. A name can repeat a builtin's, and an id cannot: this
# `not` is not the builtin `Bool.not`, so the translator does not read it as
# `NOT`.
Bool :: { n : I64 }.{
	not : Bool -> Bool
	not = |Bool.(b)| Bool.{ n: 1 - b.n }

	level : Bool -> I64
	level = |Bool.(b)| b.n
}
