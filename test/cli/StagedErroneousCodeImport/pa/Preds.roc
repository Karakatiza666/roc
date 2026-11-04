Preds := {}.{
	adult : { name : Str, age : U8 } -> Bool
	adult = |p| p.age >= 18
}
