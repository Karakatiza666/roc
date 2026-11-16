# A `from_quote` that rejects its literal is a compile error in a function that
# only a `Code` site reaches.

Stage := {}.{
	render : Code(f) -> Str
	render = |code| "rows ${Code.graph(code).rows().len().to_str()}"
}

Method := [Get, Post].{
	from_quote : Str -> Try(Method, [BadQuotedBytes(Str)])
	from_quote = |raw| match raw {
		"GET" => Ok(Get)
		_ => Err(BadQuotedBytes("not a method"))
	}

	is_get : Method, F64 -> F64
	is_get = |m, f| match m {
		Get => f
		Post => 0.0
	}
}

pick : F64 -> F64
pick = |x| "FETCH".Method.is_get(x)

main! = |_args| {
	echo!("${Stage.render(pick)}\n")
	Ok({})
}
