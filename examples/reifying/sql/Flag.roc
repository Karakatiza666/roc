# A module of the application with a method `not`, for `extensions.roc`. A
# method name can repeat a builtin's, and an id cannot: this `not` is not the
# builtin `Bool.not`, so the translator does not read it as `NOT`.
Flag :: { n : I64 }.{
	not : Flag -> Flag
	not = |Flag.(b)| Flag.{ n: 1 - b.n }

	level : Flag -> I64
	level = |Flag.(b)| b.n
}
