# Code sites in the codec methods (Q17 of roc-reify-structural-proposal.md,
# design.md "Code Instance Tables"). The compiler calls `encoder_for` and
# `parser_for` with no written use: through the `where` requirement of a
# format function, and from the encoder or parser it derives for a
# structure that holds the type. Each such call is an evidence edge, which
# fixes the format and the state types the owner type does not fix, so the
# method is described at the edge: in the method's own body, in a function
# of another module the method is bound to, and in a computed callable.
import Db
import Other

## A closure that holds a Code site at this function's own variable.
make = |{}| |encoding| |value, state| Json.encode_str(encoding, Db.of(value).filter(|_y| Bool.True).show(), state)

Here(r) := { q : Db.Q(r) }.{
	encoder_for = |encoding| |Here.(here), state| Json.encode_str(encoding, here.q.filter(|_x| Bool.True).show(), state)
	parser_for = |encoding| |state| {
		parsed = Json.parse_str(encoding, state)?
		Ok({ value: Here.({ q: Db.empty({}).filter(|_x| Bool.True) }), rest: parsed.rest })
	}
}

There(r) := { row : r }.{
	encoder_for = Other.encode
}

Made(r) := { row : r }.{
	encoder_for = make({})
}

## Parses a `Here(Str)` through `parser_for`.
parse_here : Str -> Str
parse_here = |text| {
	parsed : Try(Here(Str), _)
	parsed = Json.parse(text)
	match parsed {
		Ok(Here.(p)) => p.q.show()
		Err(_) => "bad"
	}
}

main! = |_args| {
	here : Here(Str)
	here = Here.({ q: Db.of("x") })
	count : Here(U64)
	count = Here.({ q: Db.of(1) })
	echo!("here: ${Json.to_str(here)}\n")
	echo!("count: ${Json.to_str(count)}\n")
	echo!("record: ${Json.to_str({ h: here, c: count })}\n")
	echo!("list: ${Json.to_str([here])}\n")
	there : There(Str)
	there = There.({ row: "x" })
	echo!("there: ${Json.to_str(there)}\n")
	made : Made(Str)
	made = Made.({ row: "x" })
	echo!("made: ${Json.to_str(made)}\n")
	echo!("parsed: ${parse_here("\"x\"")}\n")
	Ok({})
}
