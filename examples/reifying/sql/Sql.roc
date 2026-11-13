# A SQL translator and the typed builder around it: reified Roc functions in,
# SQL out.
#
# Rows are ordinary Roc records. A table is `Table(row)` over one of them, and
# every clause a query or a migration needs is a Roc function over that record:
# a filter is a `row -> Bool`, a projection a `row -> out`, a primary key a
# `row -> key`. Naming a function where a builder method expects a `Code(f)`
# reifies it, and the translator below reads the description.
Sql :: {}.{

	## Why a reified function is not SQL, or a schema is not one a database
	## can create. Every rejection names the construct.
	Error := [Unsupported(Str), BadSchema(Str)].{
		is_eq : _
	}

	## One SQL value, as a parameter or a literal. A `Blob` is the bytes
	## [Sql.Param] wrote for a captured value of an opaque type.
	Value := [Integer(I64), Numeric(Dec), Text(Str), Boolean(Bool), Blob(List(U8)), Null].{
		to_sql : Value -> Str
		to_sql = |value| match value {
			Integer(n) => n.to_str()
			Numeric(d) => d.to_str()
			Text(s) => Sql.quote(s)
			Boolean(b) => if (b) "TRUE" else "FALSE"
			Blob(bytes) => "X'${Sql.hex(bytes)}'"
			Null => "NULL"
		}
	}

	## What a package adds to the translator: the SQL form of operations and
	## column types the translator does not know. Each names its primitive or
	## its type by the identity the compiler gives it, `Code.prim(f)` or
	## `Code.type_id(proxy)`, so two packages that each declare a `Time` never
	## meet. `render` takes the SQL of each argument and the evidence of the
	## call, and returns the SQL of the call or why it has none.
	##
	## The builtins the translator knows are an extension too, [Sql.builtins],
	## and a call is looked up by its id in the same way. A name says nothing:
	## a module can declare its own `Bool` with a `not`, and that `not` is not
	## SQL's `NOT` unless an extension covers its id.
	Extension := {
		prims : List(Entry),
		types : List({ type : Code.TypeId, column : Str }),
	}

	extension : { prims : List({ prim : Code.PrimId, render : { args : List(Str), evidence : List(Code.Evidence) } -> Try(Str, Str) }), types : List({ type : Code.TypeId, column : Str }) } -> Extension
	extension = |entries| Extension.({ prims: entries.prims.map(|entry| { prim: entry.prim, form: Render(entry.render) }), types: entries.types })

	## The SQL form of one primitive.
	Entry : { prim : Code.PrimId, form : Form }

	## How a primitive's call is SQL: an extension's `render`, or one of the
	## forms the builtins take. `Operator` puts an SQL operator between two
	## operands, `Present` tests an optional field (`IS NULL` or
	## `IS NOT NULL`), `Count` counts a group's rows, `Sum` is
	## `map(..).sum()` over them, and `Refused` is a builtin the translator
	## knows and refuses, with the reason.
	Form : [
		Render({ args : List(Str), evidence : List(Code.Evidence) } -> Try(Str, Str)),
		Operator(Str),
		StartsWith,
		Present(Str),
		Count,
		Sum,
		Not,
		Negate,
		ToDec,
		Refused(Str),
	]

	## The builtins a query may call, by the ids of their definitions.
	builtins : Extension
	builtins = Extension.(
		{
			prims: List.join([
				Sql.integer({ plus: Code.prim(I8.plus), minus: Code.prim(I8.minus), times: Code.prim(I8.times), div_by: Code.prim(I8.div_by), div_trunc_by: Code.prim(I8.div_trunc_by), rem_by: Code.prim(I8.rem_by), is_lt: Code.prim(I8.is_lt), is_gt: Code.prim(I8.is_gt), is_lte: Code.prim(I8.is_lte), is_gte: Code.prim(I8.is_gte) }).concat([{ prim: Code.prim(I8.is_eq), form: Operator("=") }, { prim: Code.prim(I8.negate), form: Negate }, { prim: Code.prim(I8.to_dec), form: ToDec }]),
				Sql.integer({ plus: Code.prim(U8.plus), minus: Code.prim(U8.minus), times: Code.prim(U8.times), div_by: Code.prim(U8.div_by), div_trunc_by: Code.prim(U8.div_trunc_by), rem_by: Code.prim(U8.rem_by), is_lt: Code.prim(U8.is_lt), is_gt: Code.prim(U8.is_gt), is_lte: Code.prim(U8.is_lte), is_gte: Code.prim(U8.is_gte) }).concat([{ prim: Code.prim(U8.is_eq), form: Operator("=") }, { prim: Code.prim(U8.to_dec), form: ToDec }]),
				Sql.integer({ plus: Code.prim(I16.plus), minus: Code.prim(I16.minus), times: Code.prim(I16.times), div_by: Code.prim(I16.div_by), div_trunc_by: Code.prim(I16.div_trunc_by), rem_by: Code.prim(I16.rem_by), is_lt: Code.prim(I16.is_lt), is_gt: Code.prim(I16.is_gt), is_lte: Code.prim(I16.is_lte), is_gte: Code.prim(I16.is_gte) }).concat([{ prim: Code.prim(I16.is_eq), form: Operator("=") }, { prim: Code.prim(I16.negate), form: Negate }, { prim: Code.prim(I16.to_dec), form: ToDec }]),
				Sql.integer({ plus: Code.prim(U16.plus), minus: Code.prim(U16.minus), times: Code.prim(U16.times), div_by: Code.prim(U16.div_by), div_trunc_by: Code.prim(U16.div_trunc_by), rem_by: Code.prim(U16.rem_by), is_lt: Code.prim(U16.is_lt), is_gt: Code.prim(U16.is_gt), is_lte: Code.prim(U16.is_lte), is_gte: Code.prim(U16.is_gte) }).concat([{ prim: Code.prim(U16.is_eq), form: Operator("=") }, { prim: Code.prim(U16.to_dec), form: ToDec }]),
				Sql.integer({ plus: Code.prim(I32.plus), minus: Code.prim(I32.minus), times: Code.prim(I32.times), div_by: Code.prim(I32.div_by), div_trunc_by: Code.prim(I32.div_trunc_by), rem_by: Code.prim(I32.rem_by), is_lt: Code.prim(I32.is_lt), is_gt: Code.prim(I32.is_gt), is_lte: Code.prim(I32.is_lte), is_gte: Code.prim(I32.is_gte) }).concat([{ prim: Code.prim(I32.is_eq), form: Operator("=") }, { prim: Code.prim(I32.negate), form: Negate }, { prim: Code.prim(I32.to_dec), form: ToDec }]),
				Sql.integer({ plus: Code.prim(U32.plus), minus: Code.prim(U32.minus), times: Code.prim(U32.times), div_by: Code.prim(U32.div_by), div_trunc_by: Code.prim(U32.div_trunc_by), rem_by: Code.prim(U32.rem_by), is_lt: Code.prim(U32.is_lt), is_gt: Code.prim(U32.is_gt), is_lte: Code.prim(U32.is_lte), is_gte: Code.prim(U32.is_gte) }).concat([{ prim: Code.prim(U32.is_eq), form: Operator("=") }, { prim: Code.prim(U32.to_dec), form: ToDec }]),
				Sql.integer({ plus: Code.prim(I64.plus), minus: Code.prim(I64.minus), times: Code.prim(I64.times), div_by: Code.prim(I64.div_by), div_trunc_by: Code.prim(I64.div_trunc_by), rem_by: Code.prim(I64.rem_by), is_lt: Code.prim(I64.is_lt), is_gt: Code.prim(I64.is_gt), is_lte: Code.prim(I64.is_lte), is_gte: Code.prim(I64.is_gte) }).concat([{ prim: Code.prim(I64.is_eq), form: Operator("=") }, { prim: Code.prim(I64.negate), form: Negate }, { prim: Code.prim(I64.to_dec), form: ToDec }]),
				Sql.integer({ plus: Code.prim(U64.plus), minus: Code.prim(U64.minus), times: Code.prim(U64.times), div_by: Code.prim(U64.div_by), div_trunc_by: Code.prim(U64.div_trunc_by), rem_by: Code.prim(U64.rem_by), is_lt: Code.prim(U64.is_lt), is_gt: Code.prim(U64.is_gt), is_lte: Code.prim(U64.is_lte), is_gte: Code.prim(U64.is_gte) }).concat([{ prim: Code.prim(U64.is_eq), form: Operator("=") }, { prim: Code.prim(U64.to_dec), form: ToDec }]),
				Sql.integer({ plus: Code.prim(I128.plus), minus: Code.prim(I128.minus), times: Code.prim(I128.times), div_by: Code.prim(I128.div_by), div_trunc_by: Code.prim(I128.div_trunc_by), rem_by: Code.prim(I128.rem_by), is_lt: Code.prim(I128.is_lt), is_gt: Code.prim(I128.is_gt), is_lte: Code.prim(I128.is_lte), is_gte: Code.prim(I128.is_gte) }).concat([{ prim: Code.prim(I128.is_eq), form: Operator("=") }, { prim: Code.prim(I128.negate), form: Negate }]),
				Sql.integer({ plus: Code.prim(U128.plus), minus: Code.prim(U128.minus), times: Code.prim(U128.times), div_by: Code.prim(U128.div_by), div_trunc_by: Code.prim(U128.div_trunc_by), rem_by: Code.prim(U128.rem_by), is_lt: Code.prim(U128.is_lt), is_gt: Code.prim(U128.is_gt), is_lte: Code.prim(U128.is_lte), is_gte: Code.prim(U128.is_gte) }).concat([{ prim: Code.prim(U128.is_eq), form: Operator("=") }]),
				Sql.fraction({ plus: Code.prim(Dec.plus), minus: Code.prim(Dec.minus), times: Code.prim(Dec.times), div_by: Code.prim(Dec.div_by), div_trunc_by: Code.prim(Dec.div_trunc_by), rem_by: Code.prim(Dec.rem_by), is_lt: Code.prim(Dec.is_lt), is_gt: Code.prim(Dec.is_gt), is_lte: Code.prim(Dec.is_lte), is_gte: Code.prim(Dec.is_gte) }).concat([{ prim: Code.prim(Dec.is_eq), form: Operator("=") }, { prim: Code.prim(Dec.negate), form: Negate }, { prim: Code.prim(Dec.to_dec), form: ToDec }]),
				Sql.fraction({ plus: Code.prim(F32.plus), minus: Code.prim(F32.minus), times: Code.prim(F32.times), div_by: Code.prim(F32.div_by), div_trunc_by: Code.prim(F32.div_trunc_by), rem_by: Code.prim(F32.rem_by), is_lt: Code.prim(F32.is_lt), is_gt: Code.prim(F32.is_gt), is_lte: Code.prim(F32.is_lte), is_gte: Code.prim(F32.is_gte) }).concat([{ prim: Code.prim(F32.is_eq), form: Operator("=") }, { prim: Code.prim(F32.negate), form: Negate }]),
				Sql.fraction({ plus: Code.prim(F64.plus), minus: Code.prim(F64.minus), times: Code.prim(F64.times), div_by: Code.prim(F64.div_by), div_trunc_by: Code.prim(F64.div_trunc_by), rem_by: Code.prim(F64.rem_by), is_lt: Code.prim(F64.is_lt), is_gt: Code.prim(F64.is_gt), is_lte: Code.prim(F64.is_lte), is_gte: Code.prim(F64.is_gte) }).concat([{ prim: Code.prim(F64.is_eq), form: Operator("=") }, { prim: Code.prim(F64.negate), form: Negate }]),
				[
					{ prim: Code.prim(Str.concat), form: Operator("||") },
					{ prim: Code.prim(Str.starts_with), form: StartsWith },
					{ prim: Code.prim(Str.count_utf8_bytes), form: Refused("`count_utf8_bytes` counts bytes, and SQL's `length` counts characters; the two disagree on any non-ASCII text") },
					{ prim: Code.prim(Str.is_eq), form: Operator("=") },
					{ prim: Code.prim(Bool.not), form: Not },
					{ prim: Code.prim(Bool.is_eq), form: Operator("=") },
					{ prim: Code.prim(Try.is_ok), form: Present("IS NOT NULL") },
					{ prim: Code.prim(Try.is_err), form: Present("IS NULL") },
					{ prim: Code.prim(List.len), form: Count },
					{ prim: Code.prim(List.sum), form: Sum },
				],
			]),
			types: [],
		},
	)

	## The ids of the operators every numeric type has. `==` is listed per
	## type: `F32` and `F64` derive theirs (`is_eq : _`), and `Code.prim`
	## names it as it names a written one.
	Arithmetic : { plus : Code.PrimId, minus : Code.PrimId, times : Code.PrimId, div_by : Code.PrimId, div_trunc_by : Code.PrimId, rem_by : Code.PrimId, is_lt : Code.PrimId, is_gt : Code.PrimId, is_lte : Code.PrimId, is_gte : Code.PrimId }

	## An integer type's operators. Roc's `%` and SQL's agree: both follow
	## the sign of the dividend. Roc's `//` and SQL's `/` agree at an
	## integer, where both truncate.
	integer : Arithmetic -> List(Entry)
	integer = |ids| Sql.arithmetic(ids).concat([{ prim: ids.div_trunc_by, form: Operator("/") }, { prim: ids.rem_by, form: Operator("%") }])

	## A fraction type's operators.
	fraction : Arithmetic -> List(Entry)
	fraction = |ids| Sql.arithmetic(ids).concat([
		{ prim: ids.div_trunc_by, form: Refused("`//` truncates a fraction toward zero, and SQL has no portable spelling of that; divide with `/`") },
		{ prim: ids.rem_by, form: Refused("SQL's `%` takes integers") },
	])

	arithmetic : Arithmetic -> List(Entry)
	arithmetic = |ids| [
		{ prim: ids.plus, form: Operator("+") },
		{ prim: ids.minus, form: Operator("-") },
		{ prim: ids.times, form: Operator("*") },
		{ prim: ids.div_by, form: Operator("/") },
		{ prim: ids.is_lt, form: Operator("<") },
		{ prim: ids.is_gt, form: Operator(">") },
		{ prim: ids.is_lte, form: Operator("<=") },
		{ prim: ids.is_gte, form: Operator(">=") },
	]

	## The SQL form of the primitive `id`: a builtin's, or the one an
	## extension gives it.
	form : Code.PrimId, List(Extension) -> Try(Form, [NotFound])
	form = |id, extensions| match [Sql.builtins].concat(extensions).join_map(|e| e.prims).find_first(|entry| entry.prim == id) {
		Ok(entry) => Ok(entry.form)
		Err(_) => Err(NotFound)
	}

	## A table whose rows are `row`. It holds only its name: the columns are
	## the fields of `row`, and every clause reads them off the type of the
	## function it was given.
	Table(row) :: { name : Str }.{

		## Start a migration step that creates this table with the columns the
		## function returns. The record it builds is the column list, so a
		## migration names the columns that existed when it was written, not
		## the ones `row` has now.
		create : Table(row), Code(row -> cols) -> Step(row)
		create = |Table.(t), columns| Sql.step(t.name, Create, [], columns)

		## [Table.create], where a column of a type the translator does not
		## know takes its SQL type from the extensions.
		create_with : Table(row), List(Extension), Code(row -> cols) -> Step(row)
		create_with = |Table.(t), extensions, columns| Sql.step(t.name, Create, extensions, columns)

		## Start a migration step that adds columns to a table an earlier
		## migration created.
		add_columns : Table(row), Code(row -> cols) -> Step(row)
		add_columns = |Table.(t), columns| Sql.step(t.name, Alter, [], columns)

		## One `INSERT` per row, with the values the compiler's derived encoder
		## writes. An optional field that is absent is a column left out, which
		## the database fills with `NULL`.
		insert : Table(row), List(row) -> Try(Str, Error) where [row.encoder_for : Sql.RowEncoding -> (row, List(Sql.Token) -> Try(List(Sql.Token), []))]
		insert = |Table.(t), rows| {
			statements = rows.map_try(
				|row| {
					values = Sql.values_of(row)?
					names = Str.join_with(values.map(|v| v.name), ", ")
					literals = Str.join_with(values.map(|v| v.value.to_sql()), ", ")
					Ok("INSERT INTO ${t.name} (${names}) VALUES (${literals});")
				},
			)?
			Ok(Str.join_with(statements, "\n"))
		}

		## One `INSERT` of the record the function builds, each field a column.
		## The function reads the values from around itself, as a filter of
		## [Sql.select_where] does, so each is a numbered `?` and binds as
		## [Sql.bind_captured] binds it. A field of an opaque type is the bytes
		## its `encoder_for` writes in [Sql.Param], the same bytes a filter
		## that captures a value of that type binds, so `=` and `<` on the
		## column compare what Roc compares. The function can also return a
		## captured row, `|{}| row`. Then each field is a `?`, and an optional
		## field the row does not hold binds `NULL`. A row with no field of an
		## opaque type can use [Table.insert].
		insert_one : Table(row), Code.Binds(Code({} -> row), Param) -> Code.Bound(Try(Str, Error))
		insert_one = |Table.(t), build| Code.bound(build, Sql.insert_sql(t.name, Sql.evaluate(build, [Binding.Fields([])], Sql.placeholder)))
	}

	table : Str -> Table(row)
	table = |name| Table.({ name: name })

	# ---------------------------------------------------------------- queries

	## A query over rows of type `row`, taking parameters of type `p`.
	##
	## A join makes the row a pair, `(left, right)`, so a three-way join is a
	## `((a, b), c)`. That is the one shape that composes: every clause
	## reads a joined row with `.0` and `.1`, whichever join it came from.
	Query(p, row) :: {
		source : Source,
		aliases : List(Str),
		from : Str,
		joins : List(Clause),
		filters : List(Clause),
	}.{

		## An inner join with the table, on a condition over the row so far and
		## the row of the table being joined. The result's row is the pair of
		## the two.
		join : Query(p, a), Table(b), Code((a, b -> Bool)) -> Query(p, (a, b))
		join = |Query.(q), Table.(t), condition| {
			alias =
				if q.aliases.contains(t.name) {
					"${t.name}_${(q.aliases.len() + 1).to_str()}"
				} else {
					t.name
				}
			left = q.source
			right = Source.Leaf(alias)
			target = if (alias == t.name) t.name else "${t.name} AS ${alias}"
			clause = |param| {
				cond = Sql.render(condition, [Binding.Row(left), Binding.Row(right)], param)?
				Ok("JOIN ${target} ON ${cond}")
			}
			Query.(
				{
					source: Source.Pair(left, right),
					aliases: q.aliases.append(alias),
					from: q.from,
					joins: q.joins.append(clause),
					filters: q.filters,
				},
			)
		}

		filter : Query(p, row), Code(row -> Bool) -> Query(p, row)
		filter = |Query.(q), predicate| {
			source = q.source
			clause = |param| Sql.render(predicate, [Binding.Row(source)], param)
			Query.({ ..q, filters: q.filters.append(clause) })
		}

		## A filter that reads the query's parameters: the first argument is
		## the parameter record, and each field it reads becomes a `:name`
		## placeholder.
		filter_by : Query(p, row), Code((p, row -> Bool)) -> Query(p, row)
		filter_by = |Query.(q), predicate| {
			source = q.source
			clause = |param| Sql.render(predicate, [Binding.Params, Binding.Row(source)], param)
			Query.({ ..q, filters: q.filters.append(clause) })
		}

		## The columns of the result. The function returns a record, and its
		## fields name the result columns, in name order.
		select : Query(p, row), Code(row -> out) -> Selected(p, out)
		select = |Query.(q), projection| {
			source = q.source
			columns = |param| Sql.columns(projection, [Binding.Row(source)], param)
			Sql.selected(q, columns, [])
		}

		## Group the rows by what the function returns, a column or a record
		## of them.
		group_by : Query(p, row), Code(row -> k) -> Grouped(p, row, k)
		group_by = |Query.(q), key| Grouped.({ query: Query.(q), key: key })
	}

	## Rows grouped by a key, waiting for what to compute per group.
	Grouped(p, row, k) :: { query : Query(p, row), key : Code(row -> k) }.{

		## One result row per group. The function takes the key and the group's
		## rows as a `List(row)`, so it is ordinary Roc over a list: `rows.len()`
		## is `COUNT(*)`, and `rows.map(f).sum()` is `SUM` of `f`.
		aggregate : Grouped(p, row, k), Code((k, List(row) -> out)) -> Selected(p, out)
		aggregate = |Grouped.(g), per_group| {
			Query.(q) = g.query
			source = q.source
			key = g.key
			keys = |param| {
				parts = Sql.expr_list(Sql.evaluate(key, [Binding.Row(source)], param)?)?
				Ok(Str.join_with(parts, ", "))
			}
			columns = |param| {
				group_key = Sql.evaluate(key, [Binding.Row(source)], param)?
				Sql.columns(per_group, [group_key, Binding.Group(source)], param)
			}
			Sql.selected(q, columns, [keys])
		}
	}

	## A query with its result columns fixed.
	Selected(p, out) :: {
		from : Str,
		joins : List(Clause),
		filters : List(Clause),
		groups : List(Clause),
		columns : Clause,
		order : List(Clause),
		limit : [Unlimited, Limit(U64)],
	}.{

		## Order by what the function reads off a result row. It reads the
		## result, so it names result columns, and an aggregate orders by what
		## it computed.
		order_by : Selected(p, out), Code(out -> k), [Asc, Desc] -> Selected(p, out)
		order_by = |Selected.(s), key, direction| {
			clause = |param| {
				results = match Code.graph(key).root_row().params {
					[result] => Sql.result_columns(result)
					_ => return Err(Error.Unsupported("an ordering reads one result row"))
				}
				keys = Sql.expr_list(Sql.evaluate(key, [results], param)?)?
				suffix = match direction {
					Asc => ""
					Desc => " DESC"
				}
				Ok(Str.join_with(keys.map(|k| "${k}${suffix}"), ", "))
			}
			Selected.({ ..s, order: s.order.append(clause) })
		}

		limit : Selected(p, out), U64 -> Selected(p, out)
		limit = |Selected.(s), count| Selected.({ ..s, limit: Limit(count) })

		## The statement, with a `:name` placeholder per parameter it reads.
		to_sql : Selected(p, out) -> Try(Str, Error)
		to_sql = |selected| Selected.render(selected, Sql.placeholder)

		## The statement and the parameter values that go with it. The values
		## come from the compiler's derived encoder for `p`, which is the same
		## record type the filter reads, so a parameter the filter reads is a
		## parameter the record has.
		bind : Selected(p, out), p -> Try(Statement, Error) where [p.encoder_for : Sql.RowEncoding -> (p, List(Sql.Token) -> Try(List(Sql.Token), []))]
		bind = |selected, params| {
			values = Sql.values_of(params)?
			sql = Selected.render(selected, Sql.placeholder)?
			inlined = Selected.render(
				selected,
				|name| match values.find_first(|v| v.name == name) {
					Ok(v) => v.value.to_sql()
					Err(_) => Sql.placeholder(name)
				},
			)?
			Ok(Statement.({ sql: sql, inlined: inlined, params: values }))
		}

		render : Selected(p, out), (Str -> Str) -> Try(Str, Error)
		render = |Selected.(s), param| {
			run = |clause| clause(param)
			columns = run(s.columns)?
			joins = s.joins.map_try(run)?
			filters = s.filters.map_try(run)?
			groups = s.groups.map_try(run)?
			order = s.order.map_try(run)?
			lines = List.concat(["SELECT ${columns}", "FROM ${s.from}"], joins)
				.concat(Sql.clause("WHERE", if (filters.len() > 1) filters.map(|f| "(${f})") else filters, " AND "))
				.concat(Sql.clause("GROUP BY", groups, ", "))
				.concat(Sql.clause("ORDER BY", order, ", "))
				.concat(
					match s.limit {
						Unlimited => []
						Limit(n) => ["LIMIT ${n.to_str()}"]
					},
				)
			Ok(Str.join_with(lines, "\n"))
		}
	}

	## A statement ready for a driver: the SQL with placeholders, the values
	## that fill them, and the same statement with the values written in, for
	## a script.
	Statement := { sql : Str, inlined : Str, params : List({ name : Str, value : Value }) }

	## Every column of the rows of `table` that the filter keeps, where the
	## filter reads values from around the lambda which exist only when the
	## program runs, such as a parameter of the function the query is written
	## in. The translator runs while the compiler runs, so it writes a
	## numbered `?` for each value, and the program receives the values in the
	## result's `inputs`, one per placeholder, in order. A captured value of
	## an opaque type arrives as the bytes its `encoder_for` writes in
	## [Sql.Param], and an operation the translator does not know is one an
	## extension covers.
	select_where : Table(row), List(Extension), Code.Binds(Code(row -> Bool), Param) -> Code.Bound(Try(Str, Error))
	select_where = |Table.(t), extensions, predicate| {
		rendered = Sql.render_with(predicate, extensions, [Binding.Row(Source.Leaf(t.name))], Sql.placeholder)
		Code.bound(predicate, rendered.map_ok(|condition| "SELECT *\nFROM ${t.name}\nWHERE ${condition}"))
	}

	insert_sql : Str, Try(Binding, Error) -> Try(Str, Error)
	insert_sql = |table_name, built| match built? {
		Fields(fields) => {
			values = fields.map_try(|f| Sql.expr_of(f.binding).map_ok(Sql.bare))?
			Ok("INSERT INTO ${table_name} (${Str.join_with(fields.map(|f| f.name), ", ")}) VALUES (${Str.join_with(values, ", ")})")
		}
		_ => Err(Unsupported("a row to insert is a record, one field per column"))
	}

	## The bytes [Sql.Param] writes for a value: what a captured value of an
	## opaque type binds as.
	param_bytes : a -> List(U8) where [a.encoder_for : Sql.Param -> (a, List(U8) -> Try(List(U8), []))]
	param_bytes = |value| {
		Shape : a
		encode = Shape.encoder_for(Param.default())
		Ok(bytes) = encode(value, [])
		bytes
	}

	## The statement [Sql.select_where] or [Table.insert_one] built, and the
	## captured values that fill its placeholders.
	bind_captured : Code.Bound(Try(Str, Error)) -> Try(Statement, Error)
	bind_captured = |bound| {
		sql = bound.value()?
		# A captured record fills one placeholder per field, as `Input` spells them.
		columns = bound.inputs().join_map(
			|input| match input {
				Record(fields) => fields
				_ => [input]
			},
		)
		values = columns.map_with_index(|input, k| (k, input)).map_try(|(k, input)| Ok({ name: Sql.input_name(k), value: Sql.captured_value(input)? }))?
		# The last placeholder first, so `?1` never matches the start of `?10`.
		inlined = values.fold_rev(sql, |v, text| text.replace_each(v.name, v.value.to_sql()))
		Ok(Statement.({ sql: sql, inlined: inlined, params: values }))
	}

	## A named parameter is `:name`. A captured value is numbered, `?1`
	## first, and its name is the placeholder itself.
	placeholder : Str -> Str
	placeholder = |name| if (name.starts_with("?")) name else ":${name}"

	input_name : U64 -> Str
	input_name = |k| "?${(k + 1).to_str()}"

	## The SQL value of one captured value. A column holds one scalar, so a
	## record, a tag or a list is refused. A nominal value is its backing's,
	## and an optional field that a captured row does not hold is `NULL`.
	captured_value : Code.Value -> Try(Value, Error)
	captured_value = |input| match input {
		Int(n) => match n.to_i64_try() {
			Ok(i) => Ok(Value.Integer(i))
			Err(_) => Err(Unsupported("a captured integer outside the range of an SQL INTEGER"))
		}
		Dec(d) => Ok(Value.Numeric(d))
		Str(text) => Ok(Value.Text(text))
		Bool(b) => Ok(Value.Boolean(b))
		Wrap(inner) => Sql.captured_value(inner)
		U128(_) | Frac(_) => Err(Unsupported("a captured U128 or float has no exact SQL value"))
		Record(_) | Tuple(_) | List(_) | Tag(_, _) => Err(Unsupported("a captured value that is not a scalar has no SQL value; read one of its fields"))
		Encoded(bytes) => Ok(Value.Blob(bytes))
		Absent => Ok(Value.Null)
	}

	## The number of placeholders a captured value of type `ty` fills: one
	## per field of a record, and one for any other value.
	input_width : Code.Ty -> U64
	input_width = |ty| match ty {
		Record(fields) => fields.len()
		_ => 1
	}

	selected : { source : Source, aliases : List(Str), from : Str, joins : List(Clause), filters : List(Clause) }, Clause, List(Clause) -> Selected(p, out)
	selected = |q, columns, groups| Selected.(
		{
			from: q.from,
			joins: q.joins,
			filters: q.filters,
			groups: groups,
			columns: columns,
			order: [],
			limit: Unlimited,
		},
	)

	clause : Str, List(Str), Str -> List(Str)
	clause = |keyword, parts, separator|
		if parts.is_empty() {
			[]
		} else {
			["${keyword} ${Str.join_with(parts, separator)}"]
		}

	from : Table(row) -> Query(p, row)
	from = |Table.(t)| Query.(
		{
			source: Source.Leaf(t.name),
			aliases: [t.name],
			from: t.name,
			joins: [],
			filters: [],
		},
	)

	## A clause is rendered when the statement is, with the spelling of a
	## parameter chosen then: a placeholder for a driver, a literal for a
	## script.
	Clause : (Str -> Str) -> Try(Str, Error)

	# ------------------------------------------------------------- migrations

	## One column of a `CREATE TABLE` or an `ALTER TABLE .. ADD COLUMN`.
	Column : { name : Str, sql_type : Str, nullable : Bool }

	## A migration step being built: a table created, or columns added to one.
	##
	## `row_fields` is every field of `row` as the type has it now. Only the
	## steps know which of them some migration created, so this is what lets
	## [Sql.schema_gaps] say which ones none did.
	Step(row) :: {
		table : Str,
		kind : [Create, Alter],
		row_fields : List(Str),
		columns : List(Column),
		constraints : List(Str),
		problems : List(Error),
	}.{

		primary_key : Step(row), Code(row -> k) -> Step(row)
		primary_key = |step, key| Step.constrain(step, key, |names| "PRIMARY KEY (${Str.join_with(names, ", ")})")

		unique : Step(row), Code(row -> k) -> Step(row)
		unique = |step, key| Step.constrain(step, key, |names| "UNIQUE (${Str.join_with(names, ", ")})")

		## A foreign key to another table's primary key. The target is named by
		## its `Table`, so a renamed table is one definition to change.
		references : Step(row), Code(row -> k), Table(t) -> Step(row)
		references = |step, key, Table.(target)|
			Step.constrain(step, key, |names| "FOREIGN KEY (${Str.join_with(names, ", ")}) REFERENCES ${target.name}")

		## A `CHECK` constraint, written as the Roc predicate it is.
		check : Step(row), Code(row -> Bool) -> Step(row)
		check = |Step.(s), predicate| {
			if s.kind == Alter {
				return Step.({ ..s, problems: s.problems.append(BadSchema("a constraint is declared where the table is created, not where a column is added")) })
			}
			match Sql.render(predicate, [Binding.Row(Source.Leaf(""))], Sql.placeholder) {
				Ok(sql) => Step.({ ..s, constraints: s.constraints.append("CHECK (${sql})") })
				Err(e) => Step.({ ..s, problems: s.problems.append(e) })
			}
		}

		## `NUMERIC(precision, scale)` for a `Dec` column. A `Dec` alone is
		## `NUMERIC`, which the database stores at whatever precision it likes.
		numeric : Step(row), Code(row -> Dec), U8, U8 -> Step(row)
		numeric = |step, column, precision, scale| Step.retype(step, column, "NUMERIC(${precision.to_str()}, ${scale.to_str()})")

		## `VARCHAR(n)` for a `Str` column.
		varchar : Step(row), Code(row -> Str), U16 -> Step(row)
		varchar = |step, column, length| Step.retype(step, column, "VARCHAR(${length.to_str()})")

		## The step, ready for a migration.
		done : Step(row) -> Ddl
		done = |Step.(s)| {
			statements = match s.problems {
				[first, ..] => Err(first)
				[] => Ok(Sql.ddl_statements(s.table, s.kind, s.columns, s.constraints))
			}
			Ddl.({ table: s.table, row_fields: s.row_fields, columns: s.columns.map(|c| c.name), statements: statements })
		}

		constrain : Step(row), Code(row -> k), (List(Str) -> Str) -> Step(row)
		constrain = |Step.(s), key, spell| {
			if s.kind == Alter {
				return Step.({ ..s, problems: s.problems.append(BadSchema("a constraint is declared where the table is created, not where a column is added")) })
			}
			match Sql.column_names(key) {
				Ok(names) => Step.({ ..s, constraints: s.constraints.append(spell(names)) })
				Err(e) => Step.({ ..s, problems: s.problems.append(e) })
			}
		}

		retype : Step(row), Code(row -> k), Str -> Step(row)
		retype = |Step.(s), column, sql_type| match Sql.column_names(column) {
			Ok([name]) =>
				if s.columns.any(|c| c.name == name) {
					Step.({ ..s, columns: s.columns.map(|c| if (c.name == name) { ..c, sql_type: sql_type } else c) })
				} else {
					Step.({ ..s, problems: s.problems.append(BadSchema("`${name}` is not a column this step creates")) })
				}
			Ok(_) => Step.({ ..s, problems: s.problems.append(BadSchema("a column type applies to one column")) })
			Err(e) => Step.({ ..s, problems: s.problems.append(e) })
		}
	}

	## A finished migration step.
	Ddl := { table : Str, row_fields : List(Str), columns : List(Str), statements : Try(List(Str), Error) }

	## A named, ordered group of steps.
	Migration := { id : Str, steps : List(Ddl) }

	migration : Str, List(Ddl) -> Migration
	migration = |id, steps| Migration.({ id: id, steps: steps })

	## Every migration in order, each recorded in `schema_migrations` once its
	## steps have run. A runner that skips the applied ones reads that table;
	## this writes the script it would run on an empty database.
	migrate : List(Migration) -> Try(Str, Error)
	migrate = |migrations| {
		rendered = migrations.map_try(
			|m| {
				statements = m.steps.map_try(|step| step.statements)?
				Ok(
					Str.join_with(
						List.concat(["-- migration ${m.id}"], statements.join_map(|s| s))
							.append("INSERT INTO schema_migrations (id) VALUES (${Sql.quote(m.id)});"),
						"\n",
					),
				)
			},
		)?
		Ok(Str.join_with(List.concat(["CREATE TABLE IF NOT EXISTS schema_migrations (id TEXT PRIMARY KEY);"], rendered), "\n\n"))
	}

	## Each `table.column` the row type has and no migration creates, and each
	## one two migrations create. The row type is the schema the application
	## reads, so either is a database that disagrees with the code.
	schema_gaps : List(Migration) -> List(Str)
	schema_gaps = |migrations| {
		steps = migrations.join_map(|m| m.steps)
		tables = steps.fold([], |seen, step| if (seen.contains(step.table)) seen else seen.append(step.table))
		tables.join_map(
			|name| {
				of_table = steps.keep_if(|step| step.table == name)
				created = of_table.join_map(|step| step.columns)
				fields = of_table.join_map(|step| step.row_fields).fold([], |seen, f| if (seen.contains(f)) seen else seen.append(f))
				missing = fields.keep_if(|f| !created.contains(f)).map(|f| "${name}.${f} is never created")
				twice = fields.keep_if(|f| created.keep_if(|c| c == f).len() > 1).map(|f| "${name}.${f} is created twice")
				missing.concat(twice)
			},
		)
	}

	step : Str, [Create, Alter], List(Extension), Code(row -> cols) -> Step(row)
	step = |table_name, kind, extensions, columns| {
		empty = { table: table_name, kind: kind, row_fields: [], columns: [], constraints: [], problems: [] }
		match Sql.columns_of(columns, extensions) {
			Ok(found) => Step.({ ..empty, row_fields: found.row_fields, columns: found.columns })
			Err(e) => Step.({ ..empty, problems: [e] })
		}
	}

	ddl_statements : Str, [Create, Alter], List(Column), List(Str) -> List(Str)
	ddl_statements = |table_name, kind, columns, constraints| {
		spell = |c| "${c.name} ${c.sql_type}${if (c.nullable) "" else " NOT NULL"}"
		match kind {
			Create => {
				lines = columns.map(spell).concat(constraints).map(|line| "\t${line}")
				["CREATE TABLE ${table_name} (\n${Str.join_with(lines, ",\n")}\n);"]
			}
			Alter => columns.map(|c| "ALTER TABLE ${table_name} ADD COLUMN ${spell(c)};")
		}
	}

	## The columns a step's function lists. Its body is a record whose every
	## field reads the row's field of the same name, so the record is the
	## column list and nothing else. A record's fields arrive in name order,
	## so the columns do too.
	columns_of : Code(row -> cols), List(Extension) -> Try({ row_fields : List(Str), columns : List(Column) }, Error)
	columns_of = |code, extensions| {
		graph = Code.graph(code)
		root = graph.root_row()
		row = match root.params {
			[only] => only
			_ => return Err(Unsupported("a column list reads one row"))
		}
		fields = Sql.record_fields(row)?
		entries = match Sql.body(graph.to_tree(root.id)) {
			Op({ op: Record(names), args, .. }) => List.map2(names, args, |name, value| { name, value })
			_ => return Err(Unsupported("a column list is a record, one field per column"))
		}
		columns = entries.map_try(
			|entry| {
				read = match Sql.row_read(entry.value) {
					Ok(name) => name
					Err(_) => return Err(Error.Unsupported("`${entry.name}` must read the row's field of that name"))
				}
				if read != entry.name {
					return Err(Error.Unsupported("`${entry.name}` reads `${read}`; a column keeps its field's name"))
				}
				field = match fields.find_first(|f| f.name == read) {
					Ok(f) => f
					Err(_) => return Err(Error.Unsupported("the row has no field `${read}`"))
				}
				sql_type = Sql.column_type(field.ty, extensions)?
				Ok({ name: read, sql_type: sql_type, nullable: field.presence == Optional })
			},
		)?
		Ok({ row_fields: fields.map(|f| f.name), columns: columns })
	}

	## The columns a key function reads: one field, or a tuple of them.
	column_names : Code(row -> k) -> Try(List(Str), Error)
	column_names = |code| {
		graph = Code.graph(code)
		one : Code.Tree -> Try(Str, Error)
		one = |node| match Sql.row_read(node) {
			Ok(name) => Ok(name)
			Err(_) => Err(Unsupported("a key reads a column of the row"))
		}
		match Sql.body(graph.to_tree(graph.root_row().id)) {
			Op({ op: Tuple, args, .. }) => args.map_try(one)
			single => Ok([one(single)?])
		}
	}

	## The field a tree reads straight off the row parameter.
	row_read : Code.Tree -> Try(Str, [NotARead])
	row_read = |tree| match tree {
		Op({ op: Field(name), args: [Param(_)], .. }) => Ok(name)
		Op({ op: OptField(name), args: [Param(_)], .. }) => Ok(name)
		_ => Err(NotARead)
	}

	## A row's tree without the block around it, where the block holds one
	## value and no definitions.
	body : Code.Tree -> Code.Tree
	body = |tree| match tree {
		Block({ defs: [], end: Value([one]) }) => one
		other => other
	}

	record_fields : Code.Ty -> Try(List({ name : Str, ty : Code.Ty, presence : [Required, Optional, Default(Code.Value), DefaultComputed] }), Error)
	record_fields = |ty| match ty {
		Record(fields) => Ok(fields)
		Named(_, _, backing) => Sql.record_fields(backing)
		_ => Err(Unsupported("a row is a record, and this is `${ty.name()}`"))
	}

	## The SQL type a Roc field type maps to when a step does not say. An
	## opaque type's is the one an extension gives its identity.
	column_type : Code.Ty, List(Extension) -> Try(Str, Error)
	column_type = |ty, extensions| match ty {
		I64 => Ok("BIGINT")
		I32 => Ok("INTEGER")
		I16 => Ok("SMALLINT")
		Str => Ok("TEXT")
		Bool => Ok("BOOLEAN")
		Dec => Ok("NUMERIC")
		F64 => Ok("DOUBLE PRECISION")
		Named(_, _, backing) => Sql.column_type(backing, extensions)
		Opaque(name, id, _) => match extensions.join_map(|e| e.types).find_first(|entry| entry.type == id) {
			Ok(entry) => Ok(entry.column)
			Err(_) => Err(BadSchema("`${name}` has no column type; pass an extension that covers it"))
		}
		U64 => Err(BadSchema("SQL has no unsigned 64-bit integer; U64 goes past BIGINT's range"))
		_ => Err(BadSchema("`${ty.name()}` has no column type; a column holds one scalar"))
	}

	# ------------------------------------------------------------- translator

	## What a value in a reified function stands for.
	##
	## A row is not an SQL value: it is where columns come from, so it binds
	## to the tables it came from, and a field read off it is the column. A
	## joined row is a pair of those, which is what `.0` and `.1` take apart.
	## A read of an optional field is `Maybe`: the column, which can be `NULL`.
	Binding := [
		Row(Source),
		Params,
		Group(Source),
		Expr(Str),
		Maybe(Str),
		Fields(List({ name : Str, binding : Binding })),
	]

	## The tables a row is read from, as the joins nested them.
	Source := [Leaf(Str), Pair(Source, Source)]

	## What the translation of one row's tree reads: the graph its calls name,
	## what the row's parameters and its kept nodes stand for, and how a
	## parameter of the query is spelled.
	Env : {
		graph : Code.Graph,
		extensions : List(Extension),
		params : List(Binding),
		nodes : List({ id : U32, binding : Binding }),
		param : Str -> Str,
		depth : U64,
	}

	## A reified function applied to what its parameters stand for.
	evaluate : Code(f), List(Binding), (Str -> Str) -> Try(Binding, Error)
	evaluate = |code, bindings, param| Sql.evaluate_with(code, [], bindings, param)

	## [Sql.evaluate], with the operations the extensions cover.
	evaluate_with : Code(f), List(Extension), List(Binding), (Str -> Str) -> Try(Binding, Error)
	evaluate_with = |code, extensions, bindings, param| {
		graph = Code.graph(code)
		root = graph.root_row()
		if root.params.len() != bindings.len() {
			return Err(Unsupported("this clause takes ${bindings.len().to_str()} argument(s)"))
		}
		Sql.eval(graph.to_tree(root.id), { graph: graph, extensions: extensions, params: bindings, nodes: [], param: param, depth: 0 })
	}

	render : Code(f), List(Binding), (Str -> Str) -> Try(Str, Error)
	render = |code, bindings, param| Sql.render_with(code, [], bindings, param)

	render_with : Code(f), List(Extension), List(Binding), (Str -> Str) -> Try(Str, Error)
	render_with = |code, extensions, bindings, param| {
		value = Sql.evaluate_with(code, extensions, bindings, param)?
		Ok(Sql.bare(Sql.expr_of(value)?))
	}

	## The select list: a record whose fields are the result columns, in the
	## name order a record's fields arrive in.
	columns : Code(f), List(Binding), (Str -> Str) -> Try(Str, Error)
	columns = |code, bindings, param| match Sql.evaluate(code, bindings, param)? {
		Fields(fields) => {
			spelled = fields.map_try(|f| Ok("${Sql.bare(Sql.expr_of(f.binding)?)} AS ${f.name}"))?
			Ok(Str.join_with(spelled, ", "))
		}
		_ => Err(Unsupported("a result row is a record, so each column has a name"))
	}

	## A result row, as a later clause reads it: each field is the result
	## column of that name.
	result_columns : Code.Ty -> Binding
	result_columns = |ty| match ty {
		Record(fields) => Binding.Fields(fields.map(|f| { name: f.name, binding: Binding.Expr(f.name) }))
		Named(_, _, backing) => Sql.result_columns(backing)
		_ => Binding.Fields([])
	}

	expr_list : Binding -> Try(List(Str), Error)
	expr_list = |binding| match binding {
		Fields(fields) => fields.map_try(|f| Sql.expr_of(f.binding).map_ok(Sql.bare))
		other => Ok([Sql.bare(Sql.expr_of(other)?)])
	}

	expr_of : Binding -> Try(Str, Error)
	expr_of = |binding| match binding {
		Expr(sql) => Ok(sql)
		Maybe(sql) => Ok(sql)
		Row(_) => Err(Unsupported("a whole row has no SQL value; read one of its columns"))
		Params => Err(Unsupported("the parameter record has no SQL value; read one of its fields"))
		Group(_) => Err(Unsupported("a group's rows have no SQL value; aggregate them with `len` or `map(..).sum()`"))
		Fields(_) => Err(Unsupported("a record has no SQL value here; this clause takes one column"))
	}

	expr : Code.Tree, Env -> Try(Str, Error)
	expr = |tree, env| Sql.expr_of(Sql.eval(tree, env)?)

	## What one tree stands for. A kept node is computed once, where its block
	## defines it, and each read of it is what it stands for.
	eval : Code.Tree, Env -> Try(Binding, Error)
	eval = |tree, env| match tree {
		Param(k) => match env.params.get(k.to_u64()) {
			Ok(binding) => Ok(binding)
			Err(_) => Err(Unsupported("this clause reads a parameter it does not take"))
		}
		Def(n) => match env.nodes.find_last(|entry| entry.id == n) {
			Ok(entry) => Ok(entry.binding)
			Err(_) => Err(Unsupported("a value is read before its block computes it"))
		}
		# A captured record is its fields, each a placeholder of its own, so a
		# row the program builds can be inserted. The placeholders of the
		# slots before it come first.
		Input(k) => {
			spell = env.param
			slots = env.graph.slots()
			first = slots.take_first(k.to_u64()).fold(0, |n, ty| n + Sql.input_width(ty))
			match slots.get(k.to_u64()) {
				Ok(Record(fields)) => Ok(Binding.Fields(fields.map_with_index(|f, i| { name: f.name, binding: Binding.Expr(spell(Sql.input_name(first + i))) })))
				_ => Ok(Binding.Expr(spell(Sql.input_name(first))))
			}
		}
		Arg(_) => Err(Sql.no_loop)
		Out(_) => Err(Unsupported("a branch that delivers several values has no SQL form"))
		Block(block) => {
			inner = block.defs.fold_try(
				env,
				|acc, def| {
					value = Sql.eval(def.value, acc)?
					Ok({ ..acc, nodes: acc.nodes.append({ id: def.id, binding: value }) })
				},
			)?
			match block.end {
				Value([one]) => Sql.eval(one, inner)
				Value(_) => Err(Unsupported("a branch that delivers several values has no SQL form"))
				Return(_) | Jump(_) | Branch(_) => Err(Unsupported("a query cannot leave early; every branch delivers its value"))
				Continue(_) | Break(_) => Err(Sql.no_loop)
			}
		}
		Op(node) => Sql.op(node.op, node.args, env)
	}

	no_loop : Error
	no_loop = Unsupported("SQL has no loop; a query computes over rows, not by stepping through them")

	## One operation, over the trees of its arguments and regions.
	op : Code.Op, List(Code.Tree), Env -> Try(Binding, Error)
	op = |operation, args, env| {
		first = |_| match args.first() {
			Ok(tree) => Sql.eval(tree, env)
			Err(_) => Err(Unsupported("an operation with no operand"))
		}
		match operation {
			Lit(literal) => Ok(Binding.Expr(Sql.literal(literal)?))
			Prim(prim) => Sql.prim(prim, args, env)
			Call(row) => Sql.expand(row, args.map_try(|arg| Sql.eval(arg, env))?, env)
			Closure(_) => Err(Unsupported("a function inside a query means something only as the argument of `map` over a group's rows"))
			Record(names) => {
				fields = List.map2(names, args, |name, value| { name, value }).map_try(|f| Ok({ name: f.name, binding: Sql.eval(f.value, env)? }))?
				Ok(Binding.Fields(fields))
			}
			Tuple => Err(Unsupported("a tuple has no SQL value; a key of several columns is a record"))
			List | Item => Err(Unsupported("SQL has no list value"))
			Tag(name) => Err(Unsupported("SQL has no tag unions, so `${name}` has no SQL form"))
			# A nominal is its backing to SQL.
			Wrap(_) | Unwrap => first({})
			Field(name) => Sql.field(first({})?, name, env)
			OptField(name) => match Sql.field(first({})?, name, env)? {
				Expr(column) => Ok(Binding.Maybe(column))
				other => Ok(other)
			}
			Index(position) => match first({})? {
				Row(Pair(left, right)) => if (position == 0) Ok(Binding.Row(left)) else Ok(Binding.Row(right))
				_ => Err(Unsupported("only a joined row has positions: `.0` is the rows joined so far, `.1` the table joined to them"))
			}
			Payload(tag, _) => match first({})? {
				Maybe(column) if tag == "Ok" => Ok(Binding.Expr(column))
				_ => Err(Unsupported("SQL has no tag unions, so `${tag}` has no SQL form"))
			}
			Switch(sw) => Sql.switch(sw.arms.map(|arm| arm.key), sw.joins.len(), sw.outputs.len(), args, env)
			And(_) => Sql.connective("AND", args, env)
			Or(_) => Sql.connective("OR", args, env)
			ForRange(_) | ForList(_) | Loop(_) => Err(Sql.no_loop)
			Lambda(_) => Err(Unsupported("a function inside a query means something only as the argument of `map` over a group's rows"))
			Crash => Err(Unsupported("a query cannot crash"))
			Derived(method, _) => Err(Unsupported("`${method}` is derived by the compiler and has no SQL form"))
		}
	}

	## `and` and `or` keep every operand; SQL's `AND` and `OR` do not promise
	## an order, which is the same answer here: a query body has no effects.
	connective : Str, List(Code.Tree), Env -> Try(Binding, Error)
	connective = |word, args, env| {
		parts = args.map_try(|arg| Sql.expr(arg, env))?
		Ok(Binding.Expr("(${Str.join_with(parts, " ${word} ")})"))
	}

	## A branch: a test of an optional field, which reads the column or says
	## what stands in for `NULL`, or a `Bool` test, which is a `CASE`.
	switch : List(Code.Key), U64, U64, List(Code.Tree), Env -> Try(Binding, Error)
	switch = |keys, joins, outputs, args, env| {
		if joins != 0 or outputs != 1 {
			return Err(Unsupported("a query cannot leave early; every branch delivers its value"))
		}
		scrutinee = match args.first() {
			Ok(tree) => tree
			Err(_) => return Err(Unsupported("a branch with nothing to test"))
		}
		arms = List.map2(keys, args.drop_first(1), |key, tree| { key, tree })
		arm = |name| match arms.find_first(|a| Sql.key_is(a.key, name)) {
			Ok(found) => Sql.expr(found.tree, env)
			Err(_) => Err(Unsupported("a branch in a query has a `${name}` arm"))
		}
		match Sql.presence_equality(keys, args, env) {
			Ok(shape) => {
				left = Sql.expr(shape.left, env)?
				right = Sql.expr(shape.right, env)?
				Ok(Binding.Expr(if (shape.negated) "(${left} IS NOT ${right})" else "(${left} IS ${right})"))
			}
			Err(_) => Sql.branch(scrutinee, arm, env)
		}
	}

	## The branch itself, when it is not an equality of two optional fields.
	branch : Code.Tree, (Str -> Try(Str, Error)), Env -> Try(Binding, Error)
	branch = |scrutinee, arm, env| {
		match Sql.eval(scrutinee, env)? {
			Maybe(column) => {
				present = arm("Ok")?
				absent = arm("Err")?
				if present == column {
					Ok(Binding.Expr("COALESCE(${column}, ${absent})"))
				} else {
					Ok(Binding.Expr("CASE WHEN ${column} IS NOT NULL THEN ${present} ELSE ${absent} END"))
				}
			}
			Expr(test) => Ok(Binding.Expr("CASE WHEN ${test} THEN ${arm("True")?} ELSE ${arm("False")?} END"))
			_ => Err(Unsupported("SQL has no tag unions; a branch in a query tests a condition or an optional field"))
		}
	}

	## The shape the reifier gives `==` on two optional fields: a presence
	## switch on the first value, and in each arm a presence switch on the
	## second. Both absent is `True`, one absent is `False`, and both present
	## compare the two payloads. `!=` has the arms inverted, with `not` around
	## the comparison. SQLite spells both `IS` and `IS NOT`, which treat `NULL`
	## as a value. Any other switch is not this shape.
	presence_equality : List(Code.Key), List(Code.Tree), Env -> Try({ left : Code.Tree, right : Code.Tree, negated : Bool }, [NotPresenceEquality])
	presence_equality = |keys, args, env| {
		outer = Sql.presence_parts(keys, args)?
		when_absent = Sql.presence_of(outer.absent)?
		when_present = Sql.presence_of(outer.present)?
		if when_absent.node != when_present.node {
			return Err(NotPresenceEquality)
		}
		both_absent = Sql.bool_of(when_absent.absent)?
		only_second = Sql.bool_of(when_absent.present)?
		only_first = Sql.bool_of(when_present.absent)?
		payload_of = |tree, node| match Sql.single(tree) {
			Op({ op: Payload("Ok", _), args: [Def(read)], .. }) => read == node
			_ => Bool.False
		}
		match Sql.single(when_present.present) {
			Op({ op: Prim(call), args: [x, y], .. }) if Sql.is_equality(call.id, env) and payload_of(x, outer.node) and payload_of(y, when_absent.node) and both_absent and !only_second and !only_first =>
				Ok({ left: Def(outer.node), right: Def(when_absent.node), negated: Bool.False })
			Op({ op: Prim(call), args: [Op({ op: Prim(inner), args: [x, y], .. })], .. }) if Sql.is_not(call.id, env) and Sql.is_equality(inner.id, env) and payload_of(x, outer.node) and payload_of(y, when_absent.node) and !both_absent and only_second and only_first =>
				Ok({ left: Def(outer.node), right: Def(when_absent.node), negated: Bool.True })
			_ => Err(NotPresenceEquality)
		}
	}

	## A presence switch on a kept node, as the node and its two arms.
	presence_of : Code.Tree -> Try({ node : U32, absent : Code.Tree, present : Code.Tree }, [NotPresenceEquality])
	presence_of = |tree| match Sql.single(tree) {
		Op({ op: Switch(sw), args, .. }) => Sql.presence_parts(sw.arms.map(|arm| arm.key), args)
		_ => Err(NotPresenceEquality)
	}

	presence_parts : List(Code.Key), List(Code.Tree) -> Try({ node : U32, absent : Code.Tree, present : Code.Tree }, [NotPresenceEquality])
	presence_parts = |keys, args| match args {
		[Def(node), first, second] if keys.len() == 2 => {
			arms = List.map2(keys, [first, second], |key, tree| { key, tree })
			match (arms.find_first(|a| Sql.key_is(a.key, "Err")), arms.find_first(|a| Sql.key_is(a.key, "Ok"))) {
				(Ok(absent), Ok(present)) => Ok({ node, absent: absent.tree, present: present.tree })
				_ => Err(NotPresenceEquality)
			}
		}
		_ => Err(NotPresenceEquality)
	}

	bool_of : Code.Tree -> Try(Bool, [NotPresenceEquality])
	bool_of = |tree| match Sql.single(tree) {
		Op({ op: Lit(Bool(flag)), .. }) => Ok(flag)
		_ => Err(NotPresenceEquality)
	}

	## A region that only delivers one value is that value.
	single : Code.Tree -> Code.Tree
	single = |tree| match tree {
		Block({ defs: [], end: Value([one]) }) => one
		_ => tree
	}

	## Whether the primitive `id` is a builtin's `not`.
	is_not : Code.PrimId, Env -> Bool
	is_not = |id, env| match Sql.form(id, env.extensions) {
		Ok(Not) => Bool.True
		_ => Bool.False
	}

	key_is : Code.Key, Str -> Bool
	key_is = |key, name| match key {
		Tag(tag) => tag == name
		Lit(Bool(flag)) => (if (flag) "True" else "False") == name
		Lit(_) | Len(_) | AtLeast(_) | Default => Bool.False
	}

	field : Binding, Str, Env -> Try(Binding, Error)
	field = |holder, name, env| match holder {
		Row(Leaf(alias)) =>
			if alias.is_empty() {
				Ok(Binding.Expr(name))
			} else {
				Ok(Binding.Expr("${alias}.${name}"))
			}
		Row(Pair(_, _)) => Err(Unsupported("a joined row is a pair; take `.0` or `.1` before reading `${name}`"))
		Params => {
			spell = env.param
			Ok(Binding.Expr(spell(name)))
		}
		Fields(fields) => match fields.find_first(|f| f.name == name) {
			Ok(f) => Ok(f.binding)
			Err(_) => Err(Unsupported("this record has no `${name}`"))
		}
		Group(_) => Err(Unsupported("a group's rows have no single `${name}`; aggregate them with `len` or `map(..).sum()`"))
		Expr(_) | Maybe(_) => Err(Unsupported("`${name}` is read from a value that is not a row"))
	}

	## A call of a primitive, in the form its id has in [Sql.builtins] or in
	## an extension. The owner and the method name the call in a refusal only:
	## a package type's operation is never matched by its name, so
	## `Time.is_lt` is not `<` unless an extension says it is.
	prim : { owner : Str, method : Str, id : Code.PrimId, evidence : List(Code.Evidence) }, List(Code.Tree), Env -> Try(Binding, Error)
	prim = |call, args, env| {
		name = "${call.owner}.${call.method}"
		sql = |node| Sql.expr(node, env)
		found = match Sql.form(call.id, env.extensions) {
			Ok(entry) => entry
			Err(_) => return Err(Unsupported("`${name}` has no SQL form; pass an extension that covers it"))
		}
		match (found, args) {
			(Render(spell), _) => {
				operands = args.map_try(sql)?
				match spell({ args: operands, evidence: call.evidence }) {
					Ok(text) => Ok(Binding.Expr(text))
					Err(message) => Err(Unsupported(message))
				}
			}
			(Operator(symbol), [lhs, rhs]) => Sql.binary(symbol, lhs, rhs, env)
			(StartsWith, [s, prefix]) => {
				p = sql(prefix)?
				Ok(Binding.Expr("(substr(${sql(s)?}, 1, length(${p})) = ${p})"))
			}
			(Present(test), [opt]) => Sql.null_test(opt, test, env)
			(Count, [rows]) => match Sql.eval(rows, env)? {
				Group(_) => Ok(Binding.Expr("COUNT(*)"))
				_ => Err(Unsupported("`len` counts a group's rows, and this is not one"))
			}
			(Sum, [mapped]) => Sql.sum(mapped, env)
			(Not, [operand]) => match operand {
				Op({ op: Prim(inner), args: [lhs, rhs], .. }) if Sql.is_equality(inner.id, env) => Ok(Binding.Expr("(${sql(lhs)?} <> ${sql(rhs)?})"))
				_ => Ok(Binding.Expr("(NOT ${sql(operand)?})"))
			}
			(Negate, [n]) => Ok(Binding.Expr("(-${sql(n)?})"))
			(ToDec, [n]) => Ok(Binding.Expr("CAST(${sql(n)?} AS NUMERIC)"))
			(Refused(reason), _) => Err(Unsupported(reason))
			_ => Err(Unsupported("`${name}` takes ${args.len().to_str()} operand(s) here, which its SQL form does not"))
		}
	}

	## Whether the primitive `id` is a builtin's `==`, which `!=` negates as
	## `<>`.
	is_equality : Code.PrimId, Env -> Bool
	is_equality = |id, env| match Sql.form(id, env.extensions) {
		Ok(Operator("=")) => Bool.True
		_ => Bool.False
	}

	## `rows.map(f).sum()` over a group's rows is `SUM` of `f`, with `f`'s
	## row read as the group's row.
	sum : Code.Tree, Env -> Try(Binding, Error)
	sum = |mapped, env| match mapped {
		Op({ op: Prim(map), args: [rows, Op({ op: Closure(row), args: captured, .. })], .. }) if map.id == Code.prim(List.map) =>
			match Sql.eval(rows, env)? {
				Group(source) => {
					values = captured.map_try(|c| Sql.eval(c, env))?
					inner = Sql.expr_of(Sql.expand(row, values.append(Binding.Row(source)), env)?)?
					Ok(Binding.Expr("SUM(${Sql.bare(inner)})"))
				}
				_ => Err(Unsupported("`map(..).sum()` sums over a group's rows, and this is not one"))
			}
		_ => Err(Unsupported("`sum` adds up a group's rows through `map`"))
	}

	null_test : Code.Tree, Str, Env -> Try(Binding, Error)
	null_test = |tree, test, env| match Sql.eval(tree, env)? {
		Maybe(column) => Ok(Binding.Expr("(${column} ${test})"))
		_ => Err(Unsupported("a query tests presence only on an optional field"))
	}

	## A call to one of the application's own functions, expanded with its
	## parameters bound to what the arguments stand for. A row passes through
	## as a row, so a helper over `Order` reads the order's columns.
	expand : U32, List(Binding), Env -> Try(Binding, Error)
	expand = |row, values, env| {
		if env.depth > 32 or env.graph.row(row).recursive {
			return Err(Unsupported("a function that calls itself has no SQL form; SQL has no recursion to spell it with"))
		}
		Sql.eval(env.graph.to_tree(row), { ..env, params: values, nodes: [], depth: env.depth + 1 })
	}

	literal : Code.Lit -> Try(Str, Error)
	literal = |value| match value {
		Int(n, _) => Ok(n.to_str())
		Frac(f, _) => Ok(f.to_str())
		Fixed(d) => Ok(d.to_str())
		Bool(b) => Ok(if (b) "TRUE" else "FALSE")
		Str(s) => Ok(Sql.quote(s))
		Bytes(_) => Err(Unsupported("a byte literal has no portable SQL form"))
		Numeral(n) => Ok(Sql.numeral_text(n))
	}

	## The exact decimal text of a numeral, which SQL reads as an exact
	## numeric literal: the sign, the digits before the point, and the
	## digits after it, as many as the source wrote.
	numeral_text : Numeral -> Str
	numeral_text = |n| {
		sign = if (n.is_negative()) "-" else ""
		after_count = n.digits_after_pt_count()
		after_point =
			if after_count == 0 {
				""
			} else {
				digits = Sql.decimal_digits(n.digits_after_pt())
				".${"0".repeat(after_count - digits.count_utf8_bytes())}${digits}"
			}
		"${sign}${Sql.decimal_digits(n.digits_before_pt())}${after_point}"
	}

	## The decimal digits of a number given in base-256 digits, most
	## significant first.
	decimal_digits : List(U8) -> Str
	decimal_digits = |base256| {
		# Decimal digits, least significant first: each base-256 digit
		# multiplies what is there by 256 and adds itself.
		reversed = base256.fold(
			[0.U8],
			|digits, byte| {
				var $carry = byte.to_u32()
				var $out = []
				for digit in digits {
					value = digit.to_u32() * 256 + $carry
					$out = $out.append((value % 10).to_u8_wrap())
					$carry = value // 10
				}
				while $carry > 0 {
					$out = $out.append(($carry % 10).to_u8_wrap())
					$carry = $carry // 10
				}
				$out
			},
		)
		Str.from_utf8(reversed.rev().map(|digit| digit + 48)) ?? "0"
	}

	## Two operands with an SQL operator between them.
	##
	## The normal form puts an integer literal first in a comparison, as
	## `10 <= quantity`. SQL reads as a column test, so a comparison whose
	## left operand is the only literal is written the other way round, with
	## the mirrored operator: the same comparison.
	binary : Str, Code.Tree, Code.Tree, Env -> Try(Binding, Error)
	binary = |symbol, lhs, rhs, env| {
		mirrored = Sql.mirror(symbol)
		flip = Sql.is_literal(lhs) and !Sql.is_literal(rhs) and !mirrored.is_empty()
		left = Sql.expr(if (flip) rhs else lhs, env)?
		right = Sql.expr(if (flip) lhs else rhs, env)?
		operator = if (flip) mirrored else symbol
		Ok(Binding.Expr("(${left} ${operator} ${right})"))
	}

	mirror : Str -> Str
	mirror = |symbol| match symbol {
		"<" => ">"
		">" => "<"
		"<=" => ">="
		">=" => "<="
		"=" => "="
		_ => ""
	}

	is_literal : Code.Tree -> Bool
	is_literal = |tree| match tree {
		Op({ op: Lit(_), .. }) => Bool.True
		_ => Bool.False
	}

	## An expression without the parentheses around the whole of it, for a
	## clause that stands on its own. Every operator renders parenthesised so
	## that nesting never depends on SQL's precedence table.
	bare : Str -> Str
	bare = |sql| {
		bytes = sql.to_utf8()
		last = bytes.len() - 1
		walk = bytes.fold_with_index(
			{ depth: 0.I64, quoted: Bool.False, early: Bool.False },
			|state, byte, i|
				if state.quoted {
					{ ..state, quoted: byte != 39 }
				} else if byte == 39 {
					{ ..state, quoted: Bool.True }
				} else if byte == 40 {
					{ ..state, depth: state.depth + 1 }
				} else if byte == 41 {
					{ ..state, depth: state.depth - 1, early: state.early or (state.depth == 1 and i < last) }
				} else {
					state
				},
		)
		if bytes.first() == Ok(40) and !walk.early {
			sql.drop_prefix("(").drop_suffix(")")
		} else {
			sql
		}
	}

	## Two hex digits per byte, as an SQL blob literal spells them.
	hex : List(U8) -> Str
	hex = |bytes| {
		digit = |n| if (n < 10) 48 + n else 55 + n
		Str.from_utf8_lossy(bytes.join_map(|b| [digit(b // 16), digit(b % 16)]))
	}

	quote : Str -> Str
	quote = |text| "'${text.replace_each("'", "''")}'"

	# --------------------------------------------------------------- encoding

	## The requirement that a record can become SQL values: the compiler
	## derives its encoder against [Sql.RowEncoding].
	a.Bindable : where [a.encoder_for : Sql.RowEncoding -> (a, List(Sql.Token) -> Try(List(Sql.Token), []))]

	## What the derived encoder writes: a column's name, then its value.
	Token := [Name(Str), Val(Value)]

	## The format the compiler derives a record's encoder against. A column
	## holds one scalar, so these are the scalars and the one record around
	## them.
	RowEncoding := [Row].{
		rename_field : RowEncoding, Str -> Str
		rename_field = |_, name| name

		encode_record : List(Token), U64, (List(Token), (List(Token), Str, (List(Token) -> Try(List(Token), [])) -> Try(List(Token), [])) -> Try(List(Token), [])) -> Try(List(Token), [])
		encode_record = |state, _, write_fields| write_fields(state, |fields, name, write_value| write_value(fields.append(Token.Name(name))))

		encode_i64 : I64, List(Token) -> Try(List(Token), [])
		encode_i64 = |n, state| Ok(state.append(Token.Val(Value.Integer(n))))

		encode_dec : Dec, List(Token) -> Try(List(Token), [])
		encode_dec = |d, state| Ok(state.append(Token.Val(Value.Numeric(d))))

		encode_str : Str, List(Token) -> Try(List(Token), [])
		encode_str = |s, state| Ok(state.append(Token.Val(Value.Text(s))))

		encode_bool : Bool, List(Token) -> Try(List(Token), [])
		encode_bool = |b, state| Ok(state.append(Token.Val(Value.Boolean(b))))
	}

	## The format [Sql.select_where] binds a captured value in. It writes the
	## value as bytes that sort as the value does: a database compares two
	## blobs byte by byte, so a comparison an extension renders as `<` on
	## the column agrees with Roc's. An integer is its big-endian bytes with
	## the sign bit flipped, a `Dec` is its count of attos written the same
	## way, a `Str` is its bytes with each zero byte doubled as `0, 255` and
	## a `0, 0` after them, and a record is its fields' bytes in name order.
	Param := [Default].{
		default : () -> Param
		default = || Default

		rename_field : Param, Str -> Str
		rename_field = |_, name| name

		encode_record : List(U8), U64, (List(U8), (List(U8), Str, (List(U8) -> Try(List(U8), [])) -> Try(List(U8), [])) -> Try(List(U8), [])) -> Try(List(U8), [])
		encode_record = |state, _, write_fields| write_fields(state, |fields, _, write_value| write_value(fields))

		encode_i64 : I64, List(U8) -> Try(List(U8), [])
		encode_i64 = |n, out| Ok(Param.big_endian(n.to_i128().to_u128_wrap().bitwise_xor(9223372036854775808), 8, out))

		encode_i128 : I128, List(U8) -> Try(List(U8), [])
		encode_i128 = |n, out| Ok(Param.big_endian(n.to_u128_wrap().bitwise_xor(170141183460469231731687303715884105728), 16, out))

		encode_dec : Dec, List(U8) -> Try(List(U8), [])
		encode_dec = |d, out| Param.encode_i128(d.to_attos(), out)

		encode_bool : Bool, List(U8) -> Try(List(U8), [])
		encode_bool = |b, out| Ok(out.append(if (b) 1 else 0))

		encode_str : Str, List(U8) -> Try(List(U8), [])
		encode_str = |s, out| Ok(out.concat(s.to_utf8().join_map(|b| if (b == 0) [0, 255] else [b])).concat([0, 0]))

		## The low `width` bytes of `bits`, the most significant first.
		big_endian : U128, U8, List(U8) -> List(U8)
		big_endian = |bits, width, out|
			if width == 0 {
				out
			} else {
				Param.big_endian(bits, width - 1, out.append(bits.shr_zf_wrap((width - 1) * 8).to_u8_wrap()))
			}
	}

	values_of : a -> Try(List({ name : Str, value : Value }), Error) where [a.Bindable]
	values_of = |record| {
		Shape : a
		encode = Shape.encoder_for(RowEncoding.Row)
		Ok(tokens) = encode(record, [])
		Sql.pair_up(tokens, [])
	}

	pair_up : List(Token), List({ name : Str, value : Value }) -> Try(List({ name : Str, value : Value }), Error)
	pair_up = |tokens, done| match tokens {
		[] => Ok(done)
		[Name(name), Val(value), .. as rest] => Sql.pair_up(rest, done.append({ name: name, value: value }))
		_ => Err(BadSchema("a row is a flat record of scalars, one per column"))
	}
}
