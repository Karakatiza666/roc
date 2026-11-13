# Record extension through type aliases only, as a parameter, a local and a
# top-level constant, inspected. Both lowerings run it; Boxy once crashed
# here ("hidden descriptor mapping saw mismatched child roles").
Ext(r) : { z : I64, ..r }
Mid(r) : { m : Str, ..r }
Base : { id : Str, name : Str }

show : Ext(Mid(Base)) -> Str
show = |o| "${o.m} ${o.name} ${o.id} ${o.z.to_str()}"

k : Ext(Base)
k = { z: 4, id: "e", name: "Eve" }

main! = |_args| {
	v : Ext(Mid(Base))
	v = { z: 1, m: "m", id: "i", name: "n" }
	echo!("${show(v)} ${Str.inspect(v)} ${Str.inspect(k)}\n")
	Ok({})
}
