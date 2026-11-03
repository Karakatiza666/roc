# roc-lang/roc#12720: `import Bool` with no alias names the app's own `Bool`
# module. Qualified values, tags and patterns that start with `Bool` resolve in
# that module, not in the builtin `Bool`.
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
