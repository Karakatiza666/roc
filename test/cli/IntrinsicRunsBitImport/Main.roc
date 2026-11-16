# A use of an imported generic definition copies its requirements with their
# `runs` bits, ANDed with the use's own bit.
import Frag

uses_frag = |q| Frag.frag(q)

uses_run = |x| Frag.run(x)

main! = |_args| Ok({})
