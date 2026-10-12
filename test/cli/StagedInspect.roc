# What `Str.inspect` describes as: the subject's own `to_inspect` when that
# method is the inspect override, and the compiler's default rendering
# otherwise.
#
# The default rendering stays one `Derived` node, because it is Roc's debugging
# format and a translator targets its own. The override belongs to the subject
# alone, so a container inside a record stays inside the record's `Derived`.
Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| Stage.node(Code.ir(code))

	node : Code.Ir -> Str
	node = |ir| match ir {
		Lambda(_, body, _) => "fn(${Stage.node(body)})"
		Param(name, _) => name
		Call(name, args, _) => "${name}(${Str.join_with(args.map(Stage.node), ", ")})"
		Derived(method, _, args, _) => "derived ${method}(${Str.join_with(args.map(Stage.node), ", ")})"
		MakeRecord(fields, _) => "{${Str.join_with(fields.map(Stage.field), ", ")}}"
		_ => "other"
	}

	field : { name : Str, value : Code.Ir } -> Str
	field = |f| "${f.name}: ${Stage.node(f.value)}"
}

# A nominal whose `to_inspect` is an inspect override: `Meters -> Str`.
Meters := { m : F32 }.{
	to_inspect : Meters -> Str
	to_inspect = |_| "meters"
}

# A builtin container writes its own override.
dict_inspect : Dict(Str, U64) -> Str
dict_inspect = |d| Str.inspect(d)

# A record's rendering is the default form, container and all.
record_inspect : Dict(Str, U64) -> Str
record_inspect = |d| Str.inspect({ d: d })

meters_inspect : Meters -> Str
meters_inspect = |m| Str.inspect(m)

main! = |_args| {
	echo!("${Stage.describe(dict_inspect)}\n")
	echo!("${Stage.describe(record_inspect)}\n")
	echo!("${Stage.describe(meters_inspect)}\n")
	Ok({})
}
