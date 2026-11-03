# A nominal row whose defaults its own module declares: a literal, a list,
# a tag of a nominal union, a constant of the module, and a call.
base_stock : I32
base_stock = 7

made : {} -> Str
made = |_| "made"

Med := { id : Str, stock : I32 ?? 0, tags : List(Str) ?? [], kind : Med.Kind ?? Tablet, again : I32 ?? base_stock, label : Str ?? made({}), note ?: Str }.{
	Kind := [Tablet, Syrup]
}
