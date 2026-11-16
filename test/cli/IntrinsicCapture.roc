# Inside a `Code` lambda an intrinsic is described, and a captured value is
# an input that the program computes at run time. A capture that calls an
# intrinsic runs.
Event : { at : U64, n : U64, ok : Bool }

Db := {}.{
	select_where : Code(Event -> Bool) -> Code.Bound(Str)
	select_where = |code| Code.bound(code, code.graph().rows().len().to_str())

	run : Code.Bound(Str) -> Str
	run = |bound| "${bound.value()} inputs ${bound.inputs().len().to_str()}"
}

Time :: {}.{
	now : {} -> U64
}

Text :: {}.{
	is_email : Str -> Bool
}

before : U64 -> Str
before = |c| Db.run(Db.select_where(|e| e.at < Time.now({}) and e.n > c))

flagged : Str -> Str
flagged = |x| {
	limit = Text.is_email(x)
	Db.run(Db.select_where(|e| e.ok == limit))
}

main! = |args| {
	echo!("before: ${before(3)}\n")
	if args.len() > 100 {
		echo!("flagged: ${flagged("a")}\n")
	}
	Ok({})
}
