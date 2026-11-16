# The description of a nominal type is one constant: both lowerings print the
# same `Code.Ty`. `Code.Ty` is a recursive tag union (`Named(Str, List(Ty), Ty)`), so a
# lowering that stores its recursion point in a box must not render that box
# as a source `Box`.
import Probe
import Shapes

Pet : { id : Str, name : Str }

## A nominal over a record.
Rows(r) := { row : r }

## A nominal over a tag union.
Color := [Red, Green]

## A nominal over a nominal.
Outer := { inner : Rows(Pet) }

## A recursive nominal.
Tree := [Leaf, Node(Tree, I64, Tree)]

## A nominal whose type argument its backing does not hold. The `Named`
## carries the argument, and a captured value holds only the backing.
Key(row) := { key : Str }

Owner : { id : Str, nick ?: Str, tags : Set(Str) }

Bind := {}.{
	slots : Code(Str -> Key(r)) -> Code.Bound(Str)
	slots = |code| Code.bound(code, Str.inspect(code.graph().slots()))
}

record : Code(Rows(Pet) -> Bool) -> Str
record = |code| Str.inspect(code.graph().root_row().params)

union : Code(Color -> Bool) -> Str
union = |code| Str.inspect(code.graph().root_row().params)

nested : Code(Outer -> Bool) -> Str
nested = |code| Str.inspect(code.graph().root_row().params)

recursive : Code(Tree -> Bool) -> Str
recursive = |code| Str.inspect(code.graph().root_row().params)

imported : Code(Shapes.Point -> Bool) -> Str
imported = |code| Str.inspect(code.graph().root_row().params)

function : Code((I64 -> Rows(Pet)) -> Bool) -> Str
function = |code| Str.inspect(code.graph().root_row().params)

phantom : Code(Key(Owner) -> Bool) -> Str
phantom = |code| {
	params = code.graph().root_row().params
	"${Str.inspect(params)} ${Str.join_with(params.map(|p| p.name()), ", ")}"
}

captured : Key(Owner) -> Str
captured = |k| {
	bound = Bind.slots(|_s| k)
	"${bound.value()} ${Str.inspect(bound.inputs())}"
}

## A site at this function's own type variable.
generic : a -> Str
generic = |x| Probe.of(x).filter(|_y| Bool.True).show()

main! = |_args| {
	echo!("record: ${record(|_x| Bool.True)}\n")
	echo!("union: ${union(|_x| Bool.True)}\n")
	echo!("nested: ${nested(|_x| Bool.True)}\n")
	echo!("recursive: ${recursive(|_x| Bool.True)}\n")
	echo!("imported: ${imported(|_x| Bool.True)}\n")
	echo!("function: ${function(|_x| Bool.True)}\n")
	echo!("phantom: ${phantom(|_x| Bool.True)}\n")
	echo!("captured: ${captured(Key.({ key: "k1" }))}\n")
	rows : Rows(Pet)
	rows = Rows.({ row: { id: "1", name: "rex" } })
	echo!("generic: ${generic(rows)}\n")
	Ok({})
}
