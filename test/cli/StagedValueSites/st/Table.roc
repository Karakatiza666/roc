# An opaque type whose operation computes a value of a type that is not
# opaque, as a keyed query names a row (R12).
import Id

Table :: { name : Str }.{
	named : Str -> Table
	named = |name| Table.({ name: name })

	id : Table, Str -> Id
	id = |Table.(t), key| Id.({ table: t.name, key })
}
