import Ql

# The format the compiler's derived `encoder_for` is run against, so a Roc
# row or a parameter record becomes a `Ql.Value`.
#
# The state is a stack. Every encoder pushes exactly one value. A container
# remembers the stack height, lets its members push, then folds everything
# above that height into one value.
Encode :: {}.{

	## What the derived encoder threads through: the values built so far.
	State : List(Ql.Value)

	## Anything the derived encoder can write as SurrealQL values. Nested
	## signatures spell the constraint out, as `Sql.Bindable` does.
	a.Writable : where [a.encoder_for : Encode.Format -> (a, Encode.State -> Try(Encode.State, []))]

	## The format the encoder is derived against. `U64`, `I128` and `U128`
	## have no method here on purpose: a row that holds one does not type-check
	## where it is written, because SurrealDB's `int` is 64-bit signed.
	Format := [Surreal].{
		rename_field : Format, Str -> Str
		rename_field = |_, name| name

		encode_str : Str, Encode.State -> Try(Encode.State, [])
		encode_str = |s, state| Ok(state.append(Ql.Value.Str(s)))

		encode_bool : Bool, Encode.State -> Try(Encode.State, [])
		encode_bool = |b, state| Ok(state.append(Ql.Value.Bool(b)))

		encode_i8 : I8, Encode.State -> Try(Encode.State, [])
		encode_i8 = |n, state| Ok(state.append(Ql.Value.Int(n.to_i64())))

		encode_i16 : I16, Encode.State -> Try(Encode.State, [])
		encode_i16 = |n, state| Ok(state.append(Ql.Value.Int(n.to_i64())))

		encode_i32 : I32, Encode.State -> Try(Encode.State, [])
		encode_i32 = |n, state| Ok(state.append(Ql.Value.Int(n.to_i64())))

		encode_i64 : I64, Encode.State -> Try(Encode.State, [])
		encode_i64 = |n, state| Ok(state.append(Ql.Value.Int(n)))

		encode_u8 : U8, Encode.State -> Try(Encode.State, [])
		encode_u8 = |n, state| Ok(state.append(Ql.Value.Int(n.to_i64())))

		encode_u16 : U16, Encode.State -> Try(Encode.State, [])
		encode_u16 = |n, state| Ok(state.append(Ql.Value.Int(n.to_i64())))

		encode_u32 : U32, Encode.State -> Try(Encode.State, [])
		encode_u32 = |n, state| Ok(state.append(Ql.Value.Int(n.to_i64())))

		encode_dec : Dec, Encode.State -> Try(Encode.State, [])
		encode_dec = |d, state| Ok(state.append(Ql.Value.Decimal(d)))

		encode_f32 : F32, Encode.State -> Try(Encode.State, [])
		encode_f32 = |f, state| Ok(state.append(Ql.Value.Float(f.to_f64())))

		encode_f64 : F64, Encode.State -> Try(Encode.State, [])
		encode_f64 = |f, state| Ok(state.append(Ql.Value.Float(f)))

		## A record id, written by the hand-written encoders of `Surreal.Id`
		## and `Surreal.Link`.
		encode_id : Str, Str, Encode.State -> Try(Encode.State, [])
		encode_id = |table, key, state| Ok(state.append(Ql.Value.Record({ table: table, key: key })))

		## A datetime, written by the encoder of `Surreal.Datetime`.
		encode_datetime : Str, Encode.State -> Try(Encode.State, [])
		encode_datetime = |iso, state| Ok(state.append(Ql.Value.Datetime(iso)))

		## Each field pushes its name, then its value. A field that is absent
		## pushes nothing, so the key is left out.
		encode_record : Encode.State, U64, (Encode.State, (Encode.State, Str, (Encode.State -> Try(Encode.State, [])) -> Try(Encode.State, [])) -> Try(Encode.State, [])) -> Try(Encode.State, [])
		encode_record = |state, _, write_fields| {
			base = state.len()
			written = write_fields(state, |acc, name, write_value| write_value(acc.append(Ql.Value.Str(name))))?
			Ok(Encode.fold_above(written, base, |items| Ql.Value.Object(Encode.pair_up(items, []))))
		}

		encode_list : Encode.State, U64, (Encode.State, (Encode.State, (Encode.State -> Try(Encode.State, [])) -> Try(Encode.State, [])) -> Try(Encode.State, [])) -> Try(Encode.State, [])
		encode_list = |state, _, write_items| {
			base = state.len()
			written = write_items(state, |acc, write_item| write_item(acc))?
			Ok(Encode.fold_above(written, base, |items| Ql.Value.Array(items)))
		}

		## The union payload rule: no payload is the bare tag
		## name, a record payload is spread next to `kind`, one other payload
		## is `value`, several are `_0`, `_1`, ...
		encode_tag : Encode.State, Str, U64, (Encode.State, (Encode.State, (Encode.State -> Try(Encode.State, [])) -> Try(Encode.State, [])) -> Try(Encode.State, [])) -> Try(Encode.State, [])
		encode_tag = |state, tag, _, write_payloads| {
			base = state.len()
			written = write_payloads(state, |acc, write_item| write_item(acc))?
			Ok(Encode.fold_above(written, base, |items| Encode.tagged(tag, items)))
		}
	}

	## Encode a value the way a row is written.
	value_of : a -> Try(Ql.Value, Ql.Error) where [a.encoder_for : Encode.Format -> (a, Encode.State -> Try(Encode.State, []))]
	value_of = |value| {
		Shape : a
		encode = Shape.encoder_for(Encode.Format.Surreal)
		match encode(value, []) {
			Ok([one]) => Ok(one)
			Ok(_) => Err(BadSchema("an encoder wrote other than one value"))
		}
	}

	## The stack above `base` becomes one value on top of what was below.
	fold_above : Encode.State, U64, (List(Ql.Value) -> Ql.Value) -> Encode.State
	fold_above = |state, base, build| {
		below = state.take_first(base)
		below.append(build(state.drop_first(base)))
	}

	## Names and values alternate on the stack, as `encode_record` pushed them.
	pair_up : List(Ql.Value), List({ name : Str, value : Ql.Value }) -> List({ name : Str, value : Ql.Value })
	pair_up = |items, done| match items {
		[Ql.Value.Str(name), value, .. as rest] => Encode.pair_up(rest, done.append({ name: name, value: value }))
		_ => done
	}

	## One union value from its tag and the payloads the arm carried.
	tagged : Str, List(Ql.Value) -> Ql.Value
	tagged = |tag, payloads| {
		kind = { name: "kind", value: Ql.Value.Str(tag) }
		match payloads {
			[] => Ql.Value.Str(tag)
			[Ql.Value.Object(fields)] => Ql.Value.Object(fields.prepend(kind))
			[one] => Ql.Value.Object([kind, { name: "value", value: one }])
			many => Ql.Value.Object(many.map_with_index(|v, i| { name: "_${i.to_str()}", value: v }).prepend(kind))
		}
	}
}

Row : { id : Str, qty : I64, price : Dec, ratio : F64, ok : Bool, tags : List(Str), note ?: Str, pay : [Cash, Card({ last4 : Str }), Check(I64), Wire(Str, I64)] }

row_a : Row
row_a = { id: "o'neil", qty: 3, price: 1.5, ratio: 2.0, ok: Bool.True, tags: ["a", "b"], pay: Card({ last4: "4242" }) }

row_b : Row
row_b = { id: "x", qty: -1, price: 0, ratio: 0.5, ok: Bool.False, tags: [], note: "hi", pay: Cash }

small : { a : I8, b : U8, c : I16, d : U16, e : I32, f : U32, g : F32 }
small = { a: -1, b: 255, c: -300, d: 65535, e: -70000, f: 4000000000, g: 1.5 }

expect Encode.value_of(row_a).map_ok(Ql.literal) == Ok("{ id: 'o\\'neil', ok: true, pay: { kind: 'Card', last4: '4242' }, price: 1.5dec, qty: 3, ratio: 2f, tags: ['a', 'b'] }")
expect Encode.value_of(row_b).map_ok(Ql.literal) == Ok("{ id: 'x', note: 'hi', ok: false, pay: 'Cash', price: 0.0dec, qty: -1, ratio: 0.5f, tags: [] }")
expect Encode.value_of(small).map_ok(Ql.literal) == Ok("{ a: -1, b: 255, c: -300, d: 65535, e: -70000, f: 4000000000, g: 1.5f }")

pay_check : Row
pay_check = { ..row_b, pay: Check(7) }

pay_wire : Row
pay_wire = { ..row_b, pay: Wire("eu", 9) }

expect Encode.value_of(pay_check).map_ok(Ql.literal) == Ok("{ id: 'x', note: 'hi', ok: false, pay: { kind: 'Check', value: 7 }, price: 0.0dec, qty: -1, ratio: 0.5f, tags: [] }")
expect Encode.value_of(pay_wire).map_ok(Ql.literal) == Ok("{ id: 'x', note: 'hi', ok: false, pay: { kind: 'Wire', _0: 'eu', _1: 9 }, price: 0.0dec, qty: -1, ratio: 0.5f, tags: [] }")
