# SurrealQL text: the value type every module shares, and the quoting rules
# that turn a value, a name or a record id into source text.
Ql :: {}.{

	## Why a reified function is not SurrealQL, or a schema is not one
	## SurrealDB can create. Every rejection names the construct.
	Error := [Unsupported(Str), BadSchema(Str)].{
		is_eq : _
	}

	## One SurrealQL value, as a parameter, a seed or a default. `Float` and
	## `Decimal` stay apart because SurrealDB keeps them apart.
	Value := [
		None,
		Bool(Bool),
		Int(I64),
		Float(F64),
		Decimal(Dec),
		Str(Str),
		Datetime(Str),
		Record({ table : Str, key : Str }),
		Array(List(Value)),
		Object(List({ name : Str, value : Value })),
	]

	## The value as source text: `'it\'s'`, `20dec`, `customer:⟨ada⟩`, `{ a: 1 }`.
	literal : Value -> Str
	literal = |value| match value {
		None => "NONE"
		Bool(b) => if (b) "true" else "false"
		Int(n) => n.to_str()
		Float(f) => Ql.float(f)
		Decimal(d) => "${d.to_str()}dec"
		Str(s) => Ql.quote(s)
		Datetime(iso) => "d${Ql.quote(iso)}"
		Record(r) => Ql.record_id(r.table, r.key)
		Array(items) => "[${Str.join_with(items.map(Ql.literal), ", ")}]"
		Object([]) => "{}"
		Object(fields) => "{ ${Str.join_with(fields.map(|f| "${Ql.member(f.name)}: ${Ql.literal(f.value)}"), ", ")} }"
	}

	## A float with the `f` suffix, so a whole number stays a float. SurrealQL
	## spells the two non-finite values `NaN` and `Infinity`.
	float : F64 -> Str
	float = |f|
		if f.is_nan() {
			"NaN"
		} else if f.is_infinite() {
			if (f < 0) "-Infinity" else "Infinity"
		} else {
			"${f.to_str()}f"
		}

	## A string literal in single quotes.
	quote : Str -> Str
	quote = |text| "'${Ql.escape(text, Bool.False)}'"

	## A table or field name, bare when SurrealQL reads it as a name and in
	## angle brackets otherwise (`⟨x y⟩`, `⟨select⟩`).
	ident : Str -> Str
	ident = |name|
		if Ql.is_plain(name) and !Ql.keywords.contains(name) {
			name
		} else {
			"⟨${Ql.escape(name, Bool.True)}⟩"
		}

	## A name after a dot or an object key. Words such as `value` and `select`
	## are fine there (verified), so only a name that is not plain is bracketed.
	member : Str -> Str
	member = |name| if (Ql.is_plain(name)) name else "⟨${Ql.escape(name, Bool.True)}⟩"

	## A record id. The key is always bracketed, so any key is one token:
	## `customer:⟨o'neil⟩`, `customer:⟨x y⟩`.
	record_id : Str, Str -> Str
	record_id = |table, key| "${Ql.ident(table)}:⟨${Ql.escape(key, Bool.True)}⟩"

	## Names SurrealQL does not accept bare as a table or a field. Found by
	## running each candidate word against SurrealDB 3.3.4.
	keywords : List(Str)
	keywords = [
		"break",
		"continue",
		"create",
		"define",
		"delete",
		"explain",
		"false",
		"for",
		"from",
		"function",
		"if",
		"info",
		"insert",
		"let",
		"none",
		"null",
		"only",
		"rebuild",
		"relate",
		"remove",
		"return",
		"select",
		"sleep",
		"table",
		"throw",
		"true",
		"update",
		"upsert",
		"value",
	]

	## A name made of lower case letters, digits and `_`, not starting with a digit.
	is_plain : Str -> Bool
	is_plain = |name| {
		bytes = name.to_utf8()
		is_letter = |b| (b >= 97 and b <= 122) or (b >= 65 and b <= 90) or b == 95
		is_digit = |b| b >= 48 and b <= 57
		match bytes {
			[first, .. as rest] => is_letter(first) and rest.all(|b| is_letter(b) or is_digit(b))
			[] => Bool.False
		}
	}

	## Text as it goes between quotes: `\`, the quote, and control characters
	## are escaped. Inside angle brackets, `⟩` is escaped too.
	escape : Str, Bool -> Str
	escape = |text, in_brackets| {
		bytes = text.to_utf8().fold(
			[],
			|out, byte|
				if byte == 92 {
					out.concat([92, 92])
				} else if byte == 39 and !in_brackets {
					out.concat([92, 39])
				} else if byte == 10 {
					out.concat([92, 110])
				} else if byte == 13 {
					out.concat([92, 114])
				} else if byte == 9 {
					out.concat([92, 116])
				} else if byte < 32 {
					# \u{1f}: two hex digits.
					out.concat(Str.to_utf8("\\u{${Ql.hex(byte // 16)}${Ql.hex(byte % 16)}}"))
				} else {
					out.append(byte)
				},
		)
		escaped = match Str.from_utf8(bytes) {
			Ok(s) => s
			Err(_) => crash "escaping whole bytes of valid UTF-8 keeps it valid"
		}
		if (in_brackets) escaped.replace_each("⟩", "\\u{27E9}") else escaped
	}

	hex : U8 -> Str
	hex = |digit| match ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "a", "b", "c", "d", "e", "f"].get(digit.to_u64()) {
		Ok(c) => c
		Err(_) => crash "a hex digit is below 16"
	}
}

expect Ql.quote("plain") == "'plain'"
expect Ql.quote("o'neil") == "'o\\'neil'"
expect Ql.quote("a\\b") == "'a\\\\b'"
expect Ql.quote("two\nlines\ttab") == "'two\\nlines\\ttab'"
expect Ql.quote("\u(1)") == "'\\u{01}'"
expect Ql.quote("é☃") == "'é☃'"
expect Ql.ident("name") == "name"
expect Ql.ident("x y") == "⟨x y⟩"
expect Ql.ident("select") == "⟨select⟩"
expect Ql.ident("9lives") == "⟨9lives⟩"
expect Ql.ident("") == "⟨⟩"
expect Ql.record_id("customer", "ada") == "customer:⟨ada⟩"
expect Ql.record_id("customer", "o'neil") == "customer:⟨o'neil⟩"
expect Ql.record_id("customer", "x y") == "customer:⟨x y⟩"
expect Ql.record_id("order", "a⟩b\\c") == "order:⟨a\\u{27E9}b\\\\c⟩"
expect Ql.record_id("my table", "1") == "⟨my table⟩:⟨1⟩"
expect Ql.literal(Value.None) == "NONE"
expect Ql.literal(Value.Bool(Bool.True)) == "true"
expect Ql.literal(Value.Int(-5)) == "-5"
expect Ql.literal(Value.Float(2.0)) == "2f"
expect Ql.literal(Value.Float(F64.nan)) == "NaN"
expect Ql.literal(Value.Float(-F64.infinity)) == "-Infinity"
expect Ql.literal(Value.Decimal(20)) == "20.0dec"
expect Ql.literal(Value.Decimal(-1.5)) == "-1.5dec"
expect Ql.literal(Value.Datetime("2026-10-28T04:53:59Z")) == "d'2026-10-28T04:53:59Z'"
expect Ql.literal(Value.Record({ table: "customer", key: "o'neil" })) == "customer:⟨o'neil⟩"
expect Ql.literal(Value.Array([Value.Int(1), Value.Str("a")])) == "[1, 'a']"
expect Ql.literal(Value.Array([])) == "[]"
expect Ql.literal(Value.Object([])) == "{}"
expect Ql.literal(Value.Object([{ name: "kind", value: Value.Str("Card") }, { name: "x y", value: Value.None }])) == "{ kind: 'Card', ⟨x y⟩: NONE }"
expect Ql.literal(Value.Float(0.00001)) == "1e-5f"
expect Ql.member("value") == "value"
expect Ql.member("x y") == "⟨x y⟩"
expect Ql.literal(Value.Object([{ name: "value", value: Value.Int(1) }])) == "{ value: 1 }"
