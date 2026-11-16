# roc-lang/roc#12720: the app module `Bool` has the name of a builtin type,
# which is a reserved module name. Checking reports it, and the qualified
# values, tags and patterns that start with `Bool` do not crash the compiler.
import Bool

pick : Bool -> Str
pick = |b| match b {
	Bool.Yes => "pick yes"
	Bool.No => "pick no"
}

main! = |_args| {
	echo!(Bool.not("a"))
	echo!(Bool.level("b"))
	echo!(Bool.show(Bool.Yes))
	echo!(pick(Bool.No))
	Ok({})
}
