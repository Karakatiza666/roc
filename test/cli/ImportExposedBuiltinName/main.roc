# An import that exposes a type under the name of a builtin type
# (`import Foo exposing [Bool]`) gets a warning that it shadows the builtin
# type. A qualified tag, pattern or value with that name still reads the
# builtin type, so the uses of `Foo`'s members are errors. Checking reports
# them and does not panic.
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
