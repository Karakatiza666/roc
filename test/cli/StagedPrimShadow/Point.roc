# A type of another module that derives its `is_eq`.
Point :: { x : I64 }.{
	is_eq : _

	make : I64 -> Point
	make = |x| Point.{ x }
}
