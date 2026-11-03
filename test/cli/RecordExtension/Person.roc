Person := { age : I64, name : Str }.{
	mk : Str -> Person
	mk = |n| { age: 1, name: n }
}
