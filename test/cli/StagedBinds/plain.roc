# A `Code.Binds` translator whose format encodes nothing (rule "Bound Capture
# Encoding"): a captured value whose type holds no opaque type needs no
# encoder, since the translator receives it as its value. The format still
# needs `default`.
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout

# A format with no encoder at all.
Bare := [Default].{
	default : () -> Bare
	default = || Default
}

Celsius := F32

Event : { id : U64, name : Str }

Stage := {}.{
	render : Code.Binds(Code(Event -> Bool), Bare) -> Code.Bound(Str)
	render = |code| Code.bound(code, "slots ${Code.graph(code).slots().len().to_str()}")
}

show : Code.Bound(Str) -> Str
show = |bound| "${bound.value()}: ${Str.inspect(bound.inputs())}"

text : Str -> Str
text = |name| show(Stage.render(|e| e.name == name))

number : U64 -> Str
number = |least| show(Stage.render(|e| e.id > least))

record : Event -> Str
record = |want| show(Stage.render(|e| e == want))

list : List(U64) -> Str
list = |ids| show(Stage.render(|e| ids.contains(e.id)))

float : F32 -> Str
float = |limit| show(Stage.render(|e| e.id.to_f32() < limit))

# A nominal type whose backing a stage reads is no opaque type.
celsius : Celsius -> Str
celsius = |limit| show(Stage.render(|e| {
	Celsius.(c) = limit
	e.id.to_f32() < c
}))

# A record that holds a function, and no opaque type.
holds : { check : U64 -> Bool } -> Str
holds = |h| show(Stage.render(|e| {
	_ = h
	e.id > 0
}))

# The type of `seen` is final only after the lambda: `append` fixes its item
# type to `U64` at the end of the function.
late : U64 -> Str
late = |seed| {
	seen = []
	bound = show(Stage.render(|e| seen.len() < e.id))
	_ = seen.append(seed)
	bound
}

main! = || {
	Stdout.line!("text: ${text("Oslo")}")
	Stdout.line!("number: ${number(7)}")
	Stdout.line!("record: ${record({ id: 3, name: "Lyon" })}")
	Stdout.line!("list: ${list([1, 2])}")
	Stdout.line!("float: ${float(1.5)}")
	Stdout.line!("celsius: ${celsius(Celsius.(2.5))}")
	Stdout.line!("holds: ${holds({ check: |n| n > 0 })}")
	Stdout.line!("late: ${late(4)}")
}
