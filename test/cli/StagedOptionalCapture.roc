# A captured record with an optional field binds as an input slot.
#
# The `Code.Value` of an optional field is the value of the field when the
# record holds it, and `Absent` when it does not. The program decides which
# when it runs, so each call gives its own answer. The field can be inside a
# nested record, a nominal value, an item of a list, a tag payload, or the
# value of another optional field.
Inner : { tag : Str, note ?: U8 }
Row : { id : Str, zip ?: Str, count ?: I64, inner ?: Inner }
Named := { row : Row, label ?: Str }
Shape : [One(Row), Two(Row, Inner), Empty]

Stage := {}.{
	render : Code(Str -> Bool) -> Code.Bound(Str)
	render = |code| Code.bound(code, "slots ${code.graph().slots().len().to_str()}")

	show : Code.Value -> Str
	show = |value| match value {
		Str(s) => "\"${s}\""
		Int(i) => i.to_str()
		Record(items) => "{${Str.join_with(items.map(Stage.show), ", ")}}"
		List(items) => "[${Str.join_with(items.map(Stage.show), ", ")}]"
		Tag(name, payloads) => "${name}(${Str.join_with(payloads.map(Stage.show), ", ")})"
		Wrap(inner) => "Wrap(${Stage.show(inner)})"
		Absent => "Absent"
		_ => "other"
	}

	run : Code.Bound(Str) -> Str
	run = |bound| "${bound.value()} ${Str.join_with(bound.inputs().map(Stage.show), "; ")}"
}

# `.?` reads the whole record, so the slot is the record itself and not a
# field of it.
has_zip : Row, Str -> Bool
has_zip = |r, k| r.?zip == Ok(k)

of_row : Row -> Str
of_row = |row| Stage.run(Stage.render(|k| has_zip(row, k)))

of_nested : { outer : Row, n ?: U8 } -> Str
of_nested = |pair| Stage.run(Stage.render(|k| pair.?n == Ok(1) and k == ""))

of_named : List(Named) -> Str
of_named = |many| Stage.run(Stage.render(|k| many.any(|named| named.?label == Ok(k))))

of_list : List(Row) -> Str
of_list = |rows| Stage.run(Stage.render(|k| rows.any(|r| has_zip(r, k))))

of_tag : Shape -> Str
of_tag = |shape| Stage.run(Stage.render(|k| match shape {
	One(r) => has_zip(r, k)
	Two(r, _) => has_zip(r, k)
	Empty => Bool.False
}))

main! = |args| {
	n = args.len().to_str()
	present : Row
	present = { id: n, zip: "z${n}", count: 7, inner: { tag: "t", note: 3 } }
	absent : Row
	absent = { id: n }
	half : Row
	half = { id: n, inner: { tag: "h" } }
	echo!("present: ${of_row(present)}\n")
	echo!("absent: ${of_row(absent)}\n")
	echo!("half: ${of_row(half)}\n")
	echo!("nested: ${of_nested({ outer: absent, n: 1 })}\n")
	echo!("named: ${of_named([Named.({ row: half, label: "l" }), Named.({ row: present })])}\n")
	echo!("list: ${of_list([present, absent])}\n")
	echo!("tag: ${of_tag(Two(absent, { tag: "i", note: 9 }))}\n")
	echo!("tag one: ${of_tag(One(present))}\n")
	Ok({})
}
