# Codec methods described at the evidence edges that select them (design.md
# "Code Instance Tables"). A generic function that encodes its own type
# holds the edge at its variables, so each closing use describes the
# method at the types it fixes. A user format's method is selected by a
# derived encoder's contract call, which fixes the format's state type. A
# generic `Code.Bound` call in an encoder and in a format method binds its
# inputs at the edge that selects the method (design.md "Bound Instance
# Roots").
import Db

Here(r) := { q : Db.Q(r) }.{
	encoder_for = |encoding| |Here.(here), state| Json.encode_str(encoding, here.q.filter(|_x| Bool.True).show(), state)
}

## The edge that selects `Here.encoder_for` is at this function's `r`.
enc : r -> Str
enc = |row| Json.to_str(Here.({ q: Db.of(row) }))

## A format whose state is a query: `encode_str` filters it with a Code
## site at the state's row type.
Fmt := [Default].{
	rename_field : Fmt, Str -> Str
	rename_field = |_, name| name

	encode_record : Db.Q(r), U64, (Db.Q(r), (Db.Q(r), Str, (Db.Q(r) -> Try(Db.Q(r), [])) -> Try(Db.Q(r), [])) -> Try(Db.Q(r), [])) -> Try(Db.Q(r), [])
	encode_record = |state, _, write_fields| write_fields(state, |field_state, _name, write_value| write_value(field_state))

	encode_str : Str, Db.Q(r) -> Try(Db.Q(r), [])
	encode_str = |_value, state| Ok(state.filter(|_x| Bool.True))

	## A generic bound call at the state's row type.
	encode_u16 : U16, Db.Q(r) -> Try(Db.Q(r), [])
	encode_u16 = |least, state| {
		bound = bound_at(state, least)
		Ok(state.note("format inputs ${bound.inputs().len().to_str()}"))
	}
}

## The bound call of `fetch` at the row type of `state`.
bound_at : Db.Q(r), U16 -> Code.Bound(Try(Str, [NotFound, Gone(Db.Q(r))]))
bound_at = |_state, least| fetch(least)

## A source whose `ready` binds the inputs of the sites before it.
Src := [Src(Str)].{
	from : Str -> Src
	from = |name| Src(name)

	filter : Src, Code(U16 -> Bool) -> Src
	filter = |Src(text), code| Src("${text} slots ${Code.graph(code).slots().len().to_str()}")

	ready : Src -> Code.Bound(Try(Str, [NotFound, ..e]))
	ready = |Src(text)| Code.Bound.of(Ok(text))
}

## A generic bound call: generic in the error row `e`.
fetch : U16 -> Code.Bound(Try(Str, [NotFound, ..e]))
fetch = |least| Src.from("meds").filter(|m| m > least).ready()

## An encoder with a generic bound call at the type's own variable `e`.
Count(e) := { least : U16, last : Try(Str, [NotFound, ..e]) }.{
	encoder_for : Fmt -> (Count(e), Db.Q(r) -> Try(Db.Q(r), []))
	encoder_for = |_format| |Count.(c), state| {
		bound : Code.Bound(Try(Str, [NotFound, ..e]))
		bound = fetch(c.least)
		Ok(state.note("encoder inputs ${bound.inputs().len().to_str()}"))
	}
}

## Encodes `value` with `Fmt`, starting from the query `start`.
encode_q : value, Db.Q(r) -> Db.Q(r)
	where [value.encoder_for : Fmt -> (value, Db.Q(r) -> Try(Db.Q(r), []))]
encode_q = |value, start| {
	Shape : value
	encode_value = Shape.encoder_for(Fmt.Default)
	encode_value(value, start) ?? start
}

Owner : { id : Str, name : Str }

Pet : { name : Str }

main! = |_args| {
	echo!("enc: ${enc("x")}\n")
	echo!("enc: ${enc(1.U64)}\n")
	owners : Db.Q(Owner)
	owners = Db.of({ id: "1", name: "ann" })
	pets : Db.Q(Pet)
	pets = Db.of({ name: "rex" })
	echo!("format: ${encode_q({ name: "x" }, owners).show()}\n")
	echo!("format: ${encode_q({ name: "y" }, pets).show()}\n")
	first : Count([First])
	first = Count.({ least: 3, last: Err(NotFound) })
	second : Count([Second])
	second = Count.({ least: 4, last: Err(NotFound) })
	echo!("bound: ${encode_q(first, owners).show()}\n")
	echo!("bound: ${encode_q(second, pets).show()}\n")
	echo!("bound: ${encode_q({ n: 5.U16 }, owners).show()}\n")
	echo!("bound: ${encode_q({ n: 6.U16 }, pets).show()}\n")
	Ok({})
}
