CodecErrorRowLiteral :: [].{}

# A codec method whose result has a literal in its error row
# (`Err(Oops(5))`). Its contract call has a literal argument. A holder
# whose error row is its own variable (`go`, `go_inferred`) gives the
# relation to each of its uses, so each use derives the codec at closed
# types and the literal is converted there.

Format := [Default].{
	rename_field : Format, Str -> Str
	rename_field = |_, name| name

	parse_str : Format, State -> Try({ value : Str, rest : State }, [FormatError])
	parse_str = |_, state|
		match state {
			Present(value) => Ok({ value, rest: Done })
			Done => Err(FormatError)
		}

	parse_record_start : Format, State -> Try([Counted({ len : U64, rest : State }), Uncounted(State)], [FormatError])
	parse_record_start = |_, state| Ok(Uncounted(state))

	parse_record_field : Format,
	Encoding.FieldName.FieldNames(_shape),
	State -> Try(
		[
			Field({ field : Encoding.FieldName(_shape), rest : State }),
			TryField({ name : Str, rest : State }),
			TryFieldCaseless({ name : Str, rest : State }),
			Continue(State),
			Done(State),
		],
		[FormatError],
	)
	parse_record_field = |_, _, state|
		match state {
			Present(_) => Ok(TryField({ name: "token", rest: state }))
			Done => Ok(Done(state))
		}

	parse_record_after_field : Format, State -> Try([Continue(State), Done(State)], [FormatError])
	parse_record_after_field = |_, state| Ok(Continue(state))

	skip_record_field : Format, State -> Try(State, [FormatError])
	skip_record_field = |_, _| Ok(Done)
}

State := [Present(Str), Done]

Token := { raw ?: Str }.{
	parser_for = |format| |state|
		match state {
			Present("bad") => Err(Oops(5))
			_ => {
				parsed = Format.parse_str(format, state)?
				Ok({ value: { raw: "custom-token" }, rest: parsed.rest })
			}
		}

	count_utf8_bytes : Token -> U64
	count_utf8_bytes = |token|
		match token.?raw {
			Ok(raw) => Str.count_utf8_bytes(raw)
			Err(MissingField) => 0
		}
}

parse : State -> Try(a, [FormatError, ..errs])
	where [
		a.parser_for : Format -> (State -> Try({ value : a, rest : State }, [FormatError, ..errs])),
	]
parse = |input| {
	Shape : a
	parse_shape = Shape.parser_for(Format.Default)
	parsed = parse_shape(input)?
	Ok(parsed.value)
}

# The error row holds a variable of the holder's own annotation.
go : State -> Try({ token : Token }, [FormatError, MissingRequiredField(Str), Oops(n)])
	where [n.from_numeral : Numeral -> Try(n, [InvalidNumeral(Str)])]
go = |input| parse(input)

# The same holder with an inferred error row.
go_inferred = |input| {
	result : Try({ token : Token }, _)
	result = parse(input)
	result
}

expect {
	match go(State.Present("bad")) {
		Err(Oops(k)) => k == 5.U64
		_ => False
	}
}

expect {
	match go(State.Present("wire-token")) {
		Ok(decoded) => Token.count_utf8_bytes(decoded.token) == 12
		_ => False
	}
}

expect {
	match go(State.Present("bad")) {
		Err(Oops(k)) => k == 5.I64
		_ => False
	}
}

expect {
	match go_inferred(State.Present("bad")) {
		Err(Oops(k)) => k == 5.U64
		_ => False
	}
}

expect {
	match go_inferred(State.Present("wire-token")) {
		Ok(decoded) => Token.count_utf8_bytes(decoded.token) == 12
		_ => False
	}
}
