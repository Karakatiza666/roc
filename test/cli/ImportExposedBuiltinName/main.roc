# A type that an import exposes under the name of a builtin type
# (`import Foo exposing [Bool]`) is the type that a qualified tag, pattern
# or value with that name reads, not the builtin type (the rule of
# roc-lang/roc#12720 for an import that binds the name).
import Foo exposing [Bool, Encoding]

pick : Bool -> Str
pick = |b| match b {
	Bool.Yes => "pick yes"
	Bool.No => "pick no"
	Bool.True => "pick true"
}

main! = |_args| {
	echo!(Bool.show(Bool.Yes))
	echo!(Bool.show(Bool.True))
	echo!(pick(Bool.No))
	echo!(Encoding.name(Encoding.Fancy))
	Ok({})
}
