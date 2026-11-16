# A generic definition reaches an intrinsic only at a use that fixes its type
# to one whose method is an intrinsic. Inside a `Code` lambda the use is
# described. At run time it is an error with the chain to the intrinsic.
Ops := {}.{
	count : Code(T -> Bool) -> Str
	count = |code| code.graph().rows().len().to_str()
}

T := { n : U64 }.{
	now : T -> Bool
}

M := { n : U64 }.{
	now : M -> Bool
	now = |m| m.n > 0
}

inner = |x| x.now()

outer = |t| inner(t)

main! = |args| {
	echo!("described: ${Ops.count(|t| outer(t))}\n")
	m : M
	m = { n: 1 }
	echo!("body: ${Str.inspect(outer(m))}\n")
	if args.len() > 100 {
		t : T
		t = { n: 1 }
		echo!("intrinsic: ${Str.inspect(outer(t))}\n")
	}
	Ok({})
}
