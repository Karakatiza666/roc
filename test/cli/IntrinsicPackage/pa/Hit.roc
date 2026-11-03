# A type whose `is_eq` and `score` are intrinsics.
Hit := { s : U64 }.{
	is_eq : Hit, Hit -> Bool
	score : Hit -> U64
}
