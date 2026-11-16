# A constant whose value holds a nominal or opaque type backed by a record,
# restored by a Monotype program: its stored type keeps the declaration's
# field order, as the type the program reads it at does.

Id := { bits : Str }

Key :: { n : U128 }

empty : List(Id)
empty = []

ids : List(Id)
ids = [{ bits: "a" }]

keys : List(Key)
keys = [{ n: 1 }]

add : List({ ids : List(Id) }) -> List({ ids : List(Id) })
add = |defs| defs.prepend({ ids: [] })

expect empty.len() == 0
expect ids.len() == 1
expect keys.len() == 1
expect add([]).len() == 1
