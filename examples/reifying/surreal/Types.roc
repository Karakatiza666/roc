import Ql

# Roc types as SurrealDB types. Reads the `Code.Ty` that the table's identity
# lambda reified and gives:
#   - the SurrealDB `TYPE` of each field, with the generated constraints
#   - every place a `Link` or `Id` sits, for the delete policy
#   - the checks that make a row type a valid schema (`BadSchema`)
Types :: {}.{

	## One end of an edge table.
	Endpoint : { name : Str, row_ty : Code.Ty }

	## A normal table, or an edge table with the tables its ends point at.
	Kind := [Normal, Relation({ from : Types.Endpoint, to : Types.Endpoint })].{
		is_eq : _
	}

	## A table the schema lists. A link finds its target table here.
	Source : { name : Str, row_ty : Code.Ty, kind : Types.Kind }

	Registry : List(Types.Source)

	## One `DEFINE FIELD`. `path` is spelled for SurrealQL (`items[*].product`)
	## and `top` is its first part. `asserts` are conditions over `$value`,
	## each safe to join with `AND`.
	FieldDef : { path : Str, top : Str, ty : Str, asserts : List(Str) }

	## Where a link sits. `elements` is True when the site is a `List` of links.
	Shape : [Root, RootOptional, RootList, InObject, InList, InUnionArm({ tag : Str })]

	## A `Link` or an `Id` at any depth. `target` is the row type it points
	## at; `table_for` turns it into a table. `required` is True when no
	## optional field, list or union arm is on the way to it.
	LinkSite : { path : Str, top : Str, target : Code.Ty, is_id : Bool, required : Bool, shape : Types.Shape, elements : Bool }

	link_name : Str
	link_name = "Surreal.Link"

	id_name : Str
	id_name = "Surreal.Id"

	datetime_name : Str
	datetime_name = "Surreal.Datetime"

	# ---------------------------------------------------------------- shapes

	## A user nominal is read through to its backing. `Surreal.*` and
	## `Builtin.*` types are not.
	user_named : Str -> Bool
	user_named = |name| !name.starts_with("Surreal.") and !name.starts_with("Builtin.")

	unwrap : Code.Ty -> Code.Ty
	unwrap = |ty| match ty {
		Named(name, backing) => if (user_named(name)) Types.unwrap(backing) else ty
		_ => ty
	}

	record_fields : Code.Ty -> Try(List({ name : Str, ty : Code.Ty, presence : [Required, Optional] }), Ql.Error)
	record_fields = |ty| match Types.unwrap(ty) {
		Record(fields) => Ok(fields)
		other => Err(BadSchema("a row is a record, and this is `${other.name()}`"))
	}

	## The row type a `Link` or an `Id` points at, or `Err` for any other type.
	site_of : Code.Ty -> Try({ target : Code.Ty, is_id : Bool }, [NotASite])
	site_of = |ty| match Types.unwrap(ty) {
		Named("Surreal.Link", backing) => Ok({ target: Types.link_target(backing), is_id: Bool.False })
		Named("Surreal.Id", backing) => Ok({ target: Types.id_target(backing), is_id: Bool.True })
		_ => Err(NotASite)
	}

	## `Link(row)` holds its row in `fetched : [Fetched(row), NotFetched]`.
	link_target : Code.Ty -> Code.Ty
	link_target = |backing| match backing {
		Record(fields) => match fields.find_first(|f| f.name == "fetched") {
			Ok({ ty: TagUnion(variants), .. }) => match variants.find_first(|v| v.name == "Fetched") {
				Ok({ payloads: [row], .. }) => row
				_ => crash "Surreal.Link has a Fetched variant with one payload"
			}
			_ => crash "Surreal.Link has a fetched field"
		}
		_ => crash "Surreal.Link is a record"
	}

	## `Id(row)` holds its row type in `phantom : List(row)`.
	id_target : Code.Ty -> Code.Ty
	id_target = |backing| match backing {
		Record(fields) => match fields.find_first(|f| f.name == "phantom") {
			Ok({ ty: ListOf(row), .. }) => row
			_ => crash "Surreal.Id has a phantom field"
		}
		_ => crash "Surreal.Id is a record"
	}

	## A name for a row type that is equal for the same type however it was
	## reached. A nominal is its name: its body shows a link back to itself
	## differently from each side, so bodies are not compared.
	key : Code.Ty -> Str
	key = |ty| match ty {
		Named(name, backing) =>
			if name == Types.link_name {
				"Link<${Types.key(Types.link_target(backing))}>"
			} else if name == Types.id_name {
				"Id<${Types.key(Types.id_target(backing))}>"
			} else {
				"N:${name}"
			}
		Recursive(name) => "N:${name}"
		ListOf(item) => "List(${Types.key(item)})"
		Record(fields) => "{${Str.join_with(fields.map(|f| "${f.name}${if (f.presence == Optional) "?:" else ":"}${Types.key(f.ty)}"), ",")}}"
		Tuple(parts) => "(${Str.join_with(parts.map(Types.key), ",")})"
		TagUnion(variants) => "[${Str.join_with(variants.map(|v| "${v.name}(${Str.join_with(v.payloads.map(Types.key), ",")})"), ",")}]"
		Fn(params, result) => "Fn(${Str.join_with(params.map(Types.key), ",")}->${Types.key(result)})"
		Opaque(name, args) => "O:${name}(${Str.join_with(args.map(Types.key), ",")})"
		other => other.name()
	}

	## The table that holds rows of this type. Two tables with an equal row
	## type make a link to it ambiguous, so that is a `BadSchema`.
	table_for : Types.Registry, Code.Ty -> Try(Str, Ql.Error)
	table_for = |registry, target| match Types.lookup(registry, target) {
		Ok(name) => Ok(name)
		Err(message) => Err(BadSchema(message))
	}

	lookup : Types.Registry, Code.Ty -> Try(Str, Str)
	lookup = |registry, target| {
		wanted = Types.key(target)
		match registry.keep_if(|s| Types.key(s.row_ty) == wanted) {
			[one] => Ok(one.name)
			[] => Err("no table holds the row type `${target.name()}`; list its table in the schema")
			[first, second, ..] => Err("tables `${first.name}` and `${second.name}` have the same row type, so a link to it is ambiguous; make one of the rows a nominal type (`:=`)")
		}
	}

	## Tables must have different names and different row types.
	check_registry : Types.Registry -> Try({}, Ql.Error)
	check_registry = |registry| {
		clash = registry.map_with_index(
			|s, i| registry.drop_first(i + 1).find_first(|t| t.name == s.name or Types.key(t.row_ty) == Types.key(s.row_ty)).map_ok(|t| (s, t)),
		).keep_oks(|r| r)
		match clash {
			[(a, b), ..] =>
				if a.name == b.name {
					Err(BadSchema("two tables are named `${a.name}`"))
				} else {
					Err(BadSchema("tables `${a.name}` and `${b.name}` have the same row type, so a link to it is ambiguous; make one of the rows a nominal type (`:=`)"))
				}
			[] => Ok({})
		}
	}

	# ------------------------------------------------------------ the checks

	## The rules a table must meet, each a `BadSchema` that names the field:
	## `id : Str`, the two ends of an edge, no field named `kind` in a union
	## arm record, no integer wider than `I64`, and only types SurrealDB has.
	check_table : Types.Source, Types.Registry -> Try({}, Ql.Error)
	check_table = |source, registry| {
		fields = Types.record_fields(source.row_ty)?
		match fields.find_first(|f| f.name == "id") {
			Ok({ ty: Str, presence: Required, .. }) => {}
			_ => return Err(BadSchema("table `${source.name}` needs a required field `id : Str`; it is the record key"))
		}
		skip = match source.kind {
			Normal => ["id"]
			Relation(_) => ["id", "from", "to"]
		}
		Types.check_ends(source, fields)?
		_ = fields.keep_if(|f| !skip.contains(f.name)).map_try(|f| Types.scan(f.ty, Ql.ident(f.name), registry))?
		Ok({})
	}

	check_ends : Types.Source, List({ name : Str, ty : Code.Ty, presence : [Required, Optional] }) -> Try({}, Ql.Error)
	check_ends = |source, fields| match source.kind {
		Normal => Ok({})
		Relation({ from, to }) => {
			_ = Types.check_end(source.name, "from", from, fields)?
			Types.check_end(source.name, "to", to, fields)
		}
	}

	check_end : Str, Str, Types.Endpoint, List({ name : Str, ty : Code.Ty, presence : [Required, Optional] }) -> Try({}, Ql.Error)
	check_end = |table, end, endpoint, fields| {
		wrong = Err(BadSchema("edge table `${table}` needs a required field `${end}` that is a `Link` to a row of table `${endpoint.name}`"))
		match fields.find_first(|f| f.name == end) {
			Ok({ ty, presence: Required, .. }) => match Types.site_of(ty) {
				Ok({ target, is_id: Bool.False }) => if (Types.key(target) == Types.key(endpoint.row_ty)) Ok({}) else wrong
				_ => wrong
			}
			_ => wrong
		}
	}

	## One field type, and everything in it, against the rules.
	scan : Code.Ty, Str, Types.Registry -> Try({}, Ql.Error)
	scan = |ty, path, registry| {
		bad = |why| Err(BadSchema("field `${path}`: ${why}"))
		match Types.unwrap(ty) {
			U64 => bad("U64 does not fit SurrealDB's `int`, which is 64-bit signed")
			I128 => bad("I128 does not fit SurrealDB's `int`, which is 64-bit signed")
			U128 => bad("U128 does not fit SurrealDB's `int`, which is 64-bit signed")
			Named(name, backing) =>
				if name == Types.datetime_name {
					Ok({})
				} else if name == Types.link_name or name == Types.id_name {
					match Types.lookup(registry, Types.site_target(name, backing)) {
						Ok(_) => Ok({})
						Err(why) => bad(why)
					}
				} else {
					bad("`${name}` has no SurrealDB type")
				}
			Record(fields) => {
				_ = fields.map_try(|f| Types.scan(f.ty, Types.dot(path, f.name), registry))?
				Ok({})
			}
			ListOf(item) => Types.scan(item, "${path}[*]", registry)
			TagUnion([]) => bad("an empty union has no values")
			TagUnion(variants) => {
				_ = variants.map_try(
					|v| match v.payloads {
						[] => Ok({})
						[one] => match Types.unwrap(one) {
							Record(fields) =>
								if fields.any(|f| f.name == "kind") {
									bad("the arm `${v.name}` has a field named `kind`, which tells the arms apart")
								} else {
									Types.scan(one, path, registry)
								}
							_ => Types.scan(one, Types.dot(path, "value"), registry)
						}
						many => {
							_ = many.map_with_index(|p, i| Types.scan(p, Types.dot(path, "_${i.to_str()}"), registry)).map_try(|r| r)?
							Ok({})
						}
					},
				)?
				Ok({})
			}
			Recursive(name) => bad("`${name}` refers back to itself; only a `Link` or an `Id` may do that")
			Tuple(_) => bad("a tuple has no SurrealDB type")
			Fn(_, _) => bad("a function has no SurrealDB type")
			Opaque(name, _) => bad("`${name}` has no SurrealDB type")
			_ => Ok({})
		}
	}

	site_target : Str, Code.Ty -> Code.Ty
	site_target = |name, backing| if (name == Types.link_name) Types.link_target(backing) else Types.id_target(backing)

	## A path part after a dot.
	dot : Str, Str -> Str
	dot = |path, name| "${path}.${Ql.member(name)}"

	# ----------------------------------------------------------- type mapping

	## The range of a narrow Roc integer, which SurrealDB's `int` does not hold.
	int_range : Code.Ty -> Try({ lo : I64, hi : I64 }, [NotRanged])
	int_range = |ty| match ty {
		I8 => Ok({ lo: -128, hi: 127 })
		U8 => Ok({ lo: 0, hi: 255 })
		I16 => Ok({ lo: -32768, hi: 32767 })
		U16 => Ok({ lo: 0, hi: 65535 })
		I32 => Ok({ lo: -2147483648, hi: 2147483647 })
		U32 => Ok({ lo: 0, hi: 4294967295 })
		_ => Err(NotRanged)
	}

	## The `TYPE` of a field. A record is `object` and a list of records is
	## `array<object>`: their fields get their own definitions.
	surreal_type : Code.Ty, Types.Registry -> Try(Str, Ql.Error)
	surreal_type = |ty, registry| match Types.unwrap(ty) {
		Record(_) => Ok("object")
		ListOf(item) => match Types.unwrap(item) {
			Record(_) => Ok("array<object>")
			_ => Types.inline_type(ty, registry)
		}
		_ => Types.inline_type(ty, registry)
	}

	## A type written out in full, as inside a union arm or an array.
	inline_type : Code.Ty, Types.Registry -> Try(Str, Ql.Error)
	inline_type = |ty, registry| match Types.unwrap(ty) {
		Str => Ok("string")
		Bool => Ok("bool")
		I64 | I8 | I16 | I32 | U8 | U16 | U32 => Ok("int")
		F32 | F64 => Ok("float")
		Dec => Ok("decimal")
		Named(name, backing) =>
			if name == Types.datetime_name {
				Ok("datetime")
			} else if name == Types.link_name or name == Types.id_name {
				table = Types.table_for(registry, Types.site_target(name, backing))?
				Ok("record<${Ql.ident(table)}>")
			} else {
				Err(BadSchema("`${name}` has no SurrealDB type"))
			}
		Record(fields) => {
			parts = fields.map_try(|f| Types.member_type(f, registry))?
			Ok("{ ${Str.join_with(parts, ", ")} }")
		}
		ListOf(item) => Ok("array<${Types.inline_type(item, registry)?}>")
		TagUnion(variants) => Types.union_type(variants, registry)
		other => Err(BadSchema("`${other.name()}` has no SurrealDB type"))
	}

	member_type : { name : Str, ty : Code.Ty, presence : [Required, Optional] }, Types.Registry -> Try(Str, Ql.Error)
	member_type = |f, registry| {
		inner = Types.inline_type(f.ty, registry)?
		Ok("${Ql.member(f.name)}: ${if (f.presence == Optional) "option<${inner}>" else inner}")
	}

	## `"A" | { kind: "B", x: X } | { kind: "C", value: Y } | { kind: "D", _0: Y, _1: Z }`
	union_type : List({ name : Str, payloads : List(Code.Ty) }), Types.Registry -> Try(Str, Ql.Error)
	union_type = |variants, registry| {
		if variants.is_empty() {
			return Err(BadSchema("an empty union has no values"))
		}
		arms = variants.map_try(
			|v| {
				kind = "kind: \"${v.name}\""
				match v.payloads {
					[] => Ok("\"${v.name}\"")
					[one] => match Types.unwrap(one) {
						Record(fields) => {
							parts = fields.map_try(|f| Types.member_type(f, registry))?
							Ok("{ ${Str.join_with([kind].concat(parts), ", ")} }")
						}
						_ => Ok("{ ${kind}, value: ${Types.inline_type(one, registry)?} }")
					}
					many => {
						parts = many.map_with_index(|p, i| Types.inline_type(p, registry).map_ok(|t| "_${i.to_str()}: ${t}")).map_try(|r| r)?
						Ok("{ ${Str.join_with([kind].concat(parts), ", ")} }")
					}
				}
			},
		)?
		Ok(Str.join_with(arms, " | "))
	}

	# ------------------------------------------------------------ constraints

	## Conditions a value of this type must meet beyond its `TYPE`, over the
	## expression `subject`. `depth` numbers the closure variables of lists.
	## Each is safe to join with `AND`.
	constraints : Code.Ty, Str, U64 -> List(Str)
	constraints = |ty, subject, depth| match Types.unwrap(ty) {
		Named(name, _) => if (name == Types.link_name or name == Types.id_name) ["record::exists(${subject})"] else []
		Record(fields) => fields.join_map(
			|f| {
				member = "${subject}.${Ql.member(f.name)}"
				inner = Types.constraints(f.ty, member, depth)
				if (f.presence == Optional) inner.map(|c| "(${member} = NONE OR (${c}))") else inner
			},
		)
		ListOf(item) => {
			item_var = "$e${(depth + 1).to_str()}"
			match Types.constraints(item, item_var, depth + 1) {
				[] => []
				inner => ["${subject}.all(|${item_var}| ${Str.join_with(inner, " AND ")})"]
			}
		}
		TagUnion(variants) => variants.join_map(
			|v| {
				inner = match v.payloads {
					[] => []
					[one] => match Types.unwrap(one) {
						Record(_) => Types.constraints(one, subject, depth)
						_ => Types.constraints(one, "${subject}.value", depth)
					}
					many => many.map_with_index(|p, i| Types.constraints(p, "${subject}._${i.to_str()}", depth)).join()
				}
				match inner {
					[] => []
					_ => ["(IF ${subject}.kind = ${Ql.quote(v.name)} THEN ${Str.join_with(inner, " AND ")} ELSE true END)"]
				}
			},
		)
		other => match Types.int_range(other) {
			Ok({ lo, hi }) => ["${subject} >= ${lo.to_str()} AND ${subject} <= ${hi.to_str()}"]
			Err(_) => []
		}
	}

	## The `DEFINE FIELD` list of a table, parents before children, in name
	## order. `id` is the record key, and the `from` and `to` of an edge are
	## SurrealDB's `in` and `out`, so none of the three is defined.
	field_defs : Str, Code.Ty, Types.Registry -> Try(List(Types.FieldDef), Ql.Error)
	field_defs = |table, row_ty, registry| {
		source = match registry.find_first(|s| s.name == table) {
			Ok(s) => s
			Err(_) => return Err(BadSchema("table `${table}` is not in the schema list"))
		}
		Types.check_table({ ..source, row_ty: row_ty }, registry)?
		skip = match source.kind {
			Normal => ["id"]
			Relation(_) => ["id", "from", "to"]
		}
		fields = Types.record_fields(row_ty)?
		defs = fields.keep_if(|f| !skip.contains(f.name)).map_try(|f| Types.defs_of("", "", f, registry))?
		Ok(defs.join())
	}

	defs_of : Str, Str, { name : Str, ty : Code.Ty, presence : [Required, Optional] }, Types.Registry -> Try(List(Types.FieldDef), Ql.Error)
	defs_of = |prefix, top, f, registry| {
		path = if (prefix == "") Ql.ident(f.name) else Types.dot(prefix, f.name)
		first = if (top == "") path else top
		optional = f.presence == Optional
		wrap = |t| if (optional) "option<${t}>" else t
		guard = |cs| if (optional) cs.map(|c| "($value = NONE OR (${c}))") else cs
		children = |fields, under|
			fields.map_try(|c| Types.defs_of(under, first, c, registry)).map_ok(|lists| lists.join())
		match Types.unwrap(f.ty) {
			Record(fields) => {
				kids = children(fields, path)?
				Ok(kids.prepend({ path: path, top: first, ty: wrap("object"), asserts: [] }))
			}
			ListOf(item) => match Types.unwrap(item) {
				Record(fields) => {
					kids = children(fields, "${path}[*]")?
					check = Types.key_check(fields)
					Ok(kids.prepend({ path: path, top: first, ty: wrap("array<object>"), asserts: guard([check]) }))
				}
				_ => Types.leaf(path, first, f.ty, optional, registry)
			}
			_ => Types.leaf(path, first, f.ty, optional, registry)
		}
	}

	leaf : Str, Str, Code.Ty, Bool, Types.Registry -> Try(List(Types.FieldDef), Ql.Error)
	leaf = |path, top, ty, optional, registry| {
		type = Types.inline_type(ty, registry)?
		cs = Types.constraints(ty, "$value", 0)
		asserts = if (optional) cs.map(|c| "($value = NONE OR (${c}))") else cs
		Ok([{ path: path, top: top, ty: if (optional) "option<${type}>" else type, asserts: asserts }])
	}

	## Elements of an `array<object>` may carry extra keys, so the keys are
	## checked by a generated condition.
	key_check : List({ name : Str, ty : Code.Ty, presence : [Required, Optional] }) -> Str
	key_check = |fields| "$value.all(|$e| object::keys($e).all(|$k| $k IN [${Str.join_with(fields.map(|f| Ql.quote(f.name)), ", ")}]))"

	# ------------------------------------------------------------- link sites

	## Every `Link` and `Id` in a row type, at any depth, in name order. A
	## `Link` or `Id` is not entered: it is another table's row. The `from`
	## and `to` of an edge row are listed like any other link, though they
	## are SurrealDB's `in` and `out`.
	link_sites : Code.Ty -> List(Types.LinkSite)
	link_sites = |row_ty| match Types.unwrap(row_ty) {
		Record(fields) => fields.join_map(
			|f| {
				path = Ql.ident(f.name)
				Types.sites(f.ty, { path: path, top: path, optional: f.presence == Optional, nested: Bool.False, in_list: Bool.False, tag: "" })
			},
		)
		_ => []
	}

	Walk : { path : Str, top : Str, optional : Bool, nested : Bool, in_list : Bool, tag : Str }

	sites : Code.Ty, Types.Walk -> List(Types.LinkSite)
	sites = |ty, w| match Types.site_of(ty) {
		Ok({ target, is_id }) => [Types.site(w, target, is_id, Bool.False)]
		Err(NotASite) => match Types.unwrap(ty) {
			Record(fields) => fields.join_map(
				|f| Types.sites(
					f.ty,
					{ ..w, path: Types.dot(w.path, f.name), optional: w.optional or f.presence == Optional, nested: Bool.True },
				),
			)
			ListOf(item) => match Types.site_of(item) {
				Ok({ target, is_id }) => [Types.site(w, target, is_id, Bool.True)]
				Err(NotASite) => Types.sites(item, { ..w, path: "${w.path}[*]", nested: Bool.True, in_list: Bool.True })
			}
			TagUnion(variants) => variants.join_map(
				|v| {
					arm = { ..w, nested: Bool.True, tag: v.name }
					match v.payloads {
						[] => []
						[one] => match Types.unwrap(one) {
							Record(_) => Types.sites(one, arm)
							_ => Types.sites(one, { ..arm, path: Types.dot(w.path, "value") })
						}
						many => many.map_with_index(|p, i| Types.sites(p, { ..arm, path: Types.dot(w.path, "_${i.to_str()}") })).join()
					}
				},
			)
			_ => []
		}
	}

	site : Types.Walk, Code.Ty, Bool, Bool -> Types.LinkSite
	site = |w, target, is_id, elements| {
		shape =
			if w.tag != "" {
				InUnionArm({ tag: w.tag })
			} else if w.in_list {
				InList
			} else if w.nested {
				InObject
			} else if elements {
				RootList
			} else if w.optional {
				RootOptional
			} else {
				Root
			}
		{
			path: w.path,
			top: w.top,
			target: target,
			is_id: is_id,
			required: !w.optional and !w.in_list and w.tag == "" and !elements,
			shape: shape,
			elements: elements,
		}
	}
}

# Tests that need no table. The rest are in `TypesTest.roc`, where a row type
# comes from a reified table.

expect Types.int_range(U8) == Ok({ lo: 0, hi: 255 })
expect Types.int_range(I32) == Ok({ lo: -2147483648, hi: 2147483647 })
expect Types.int_range(I64) == Err(NotRanged)
expect Types.int_range(Str) == Err(NotRanged)
expect Types.user_named("Customer")
expect !Types.user_named("Surreal.Link")
expect !Types.user_named("Builtin.Try")
expect Types.unwrap(Named("Customer", Str)) == Str
expect Types.unwrap(Named("Surreal.Datetime", Str)) == Named("Surreal.Datetime", Str)
expect Types.key(ListOf(Str)) == "List(Str)"
expect Types.key(Record([{ name: "a", ty: I64, presence: Required }, { name: "b", ty: Str, presence: Optional }])) == "{a:I64,b?:Str}"
expect Types.key(Named("Customer", Str)) == "N:Customer"
expect Types.key(Recursive("Customer")) == "N:Customer"
expect Types.dot("items[*]", "qty") == "items[*].qty"
expect Types.dot("payment", "value") == "payment.value"
expect Types.dot("a", "x y") == "a.⟨x y⟩"
expect Types.constraints(U8, "$value", 0) == ["$value >= 0 AND $value <= 255"]
expect Types.constraints(Str, "$value", 0) == []
expect Types.constraints(ListOf(I8), "$value", 0) == ["$value.all(|$e1| $e1 >= -128 AND $e1 <= 127)"]
expect Types.constraints(ListOf(ListOf(U8)), "$value", 0) == ["$value.all(|$e1| $e1.all(|$e2| $e2 >= 0 AND $e2 <= 255))"]
expect Types.constraints(Record([{ name: "n", ty: U16, presence: Optional }]), "$value", 0) == ["($value.n = NONE OR ($value.n >= 0 AND $value.n <= 65535))"]
expect Types.constraints(TagUnion([{ name: "A", payloads: [] }, { name: "B", payloads: [U8] }]), "$value", 0) == ["(IF $value.kind = 'B' THEN $value.value >= 0 AND $value.value <= 255 ELSE true END)"]
expect Types.key_check([{ name: "a", ty: Str, presence: Required }, { name: "it's", ty: Str, presence: Optional }]) == "$value.all(|$e| object::keys($e).all(|$k| $k IN ['a', 'it\\'s']))"
expect Types.union_type([{ name: "A", payloads: [] }, { name: "B", payloads: [Str] }, { name: "C", payloads: [Str, I64] }], []) == Ok("\"A\" | { kind: \"B\", value: string } | { kind: \"C\", _0: string, _1: int }")
expect Types.union_type([], []) == Err(BadSchema("an empty union has no values"))
expect Types.inline_type(ListOf(Record([{ name: "n", ty: I64, presence: Optional }])), []) == Ok("array<{ n: option<int> }>")
expect Types.inline_type(U64, []).is_err()
expect Types.inline_type(Tuple([Str]), []).is_err()
expect Types.inline_type(Recursive("C"), []).is_err()
expect Types.surreal_type(Record([]), []) == Ok("object")
