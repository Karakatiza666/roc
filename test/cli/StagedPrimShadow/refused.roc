# `Point.is_eq` is a derived equality of a type that is no builtin. A call of
# it is the comparison of its backing, which no `Prim` names, so `Code.prim`
# of it is refused at the argument.
import Point

p : Code.PrimId
p = Code.prim(Point.is_eq)

main! = |_args| Ok({})
