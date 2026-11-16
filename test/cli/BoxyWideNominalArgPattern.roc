# A lambda argument pattern `Wide.(w)` reads the nominal's backing, which is a
# representation conversion over a wide type. The conversion emits one
# statement per field, so its size follows the type, not the two pattern nodes
# the match-tree size lint counts.
Wide(a) := { a : a, b : List(a), c : Str, d : I64, e : List(Str), f : (a, a), g : [Some(a), None], h : Bool, i : U8, j : { k : a, l : List(a) } }

pick : Wide(a), I64 -> a
pick = |Wide.(w), n| if n == 0 w.a else w.j.k

expect pick(Wide.({ a: "x", b: [], c: "c", d: 1, e: [], f: ("p", "q"), g: None, h: True, i: 1, j: { k: "y", l: [] } }), 1) == "y"
expect pick(Wide.({ a: "x", b: [], c: "c", d: 1, e: [], f: ("p", "q"), g: None, h: True, i: 1, j: { k: "y", l: [] } }), 0) == "x"
