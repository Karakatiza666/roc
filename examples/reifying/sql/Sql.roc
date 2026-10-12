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
	## can create. Every rejection names the construct, and where there is one,
	## the line it was written on.
	Error := [Unsupported(Str), BadSchema(Str)].{
		is_eq : _
	}

	## One SQL value, as a parameter or a literal.
	Value := [Integer(I64), Numeric(Dec), Text(Str), Boolean(Bool), Null].{
		to_sql : Value -> Str
		to_sql = |value| match value {
			Integer(n) => n.to_str()
			Numeric(d) => d.to_str()
			Text(s) => Sql.quote(s)
			Boolean(b) => if b "TRUE" else "FALSE"
			Null => "NULL"
		}
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
		create = |Table.(t), columns| Sql.step(t.name, Create, columns)

		## Start a migration step that adds columns to a table an earlier
		## migration created.
		add_columns : Table(row), Code(row -> cols) -> Step(row)
		add_columns = |Table.(t), columns| Sql.step(t.name, Alter, columns)

		## One `INSERT` per row, with the values the compiler's derived encoder
		## writes. An optional field that is absent is a column left out, which
		## the database fills with `NULL`.
		insert : Table(row), List(row) -> Try(Str, Error) where [row.encoder_for : Sql.Encoding -> (row, List(Sql.Token) -> Try(List(Sql.Token), []))]
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
			target = if alias == t.name t.name else "${t.name} AS ${alias}"
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
		## fields name the result columns in the order they were written.
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
				parts = Sql.expr_list(Sql.evaluate(key, [Binding.Row(source)], param)?, Sql.body_meta(key))?
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
				lam = Sql.lambda_of(key)?
				results = match lam.params {
					[result] => Sql.result_columns(result.ty)
					_ => return Err(Sql.at_error(lam.meta, "an ordering reads one result row"))
				}
				env = Sql.env_for(key, lam.params, [results], param)
				keys = Sql.expr_list(Sql.eval(lam.body, env)?, lam.body.node_meta())?
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
		bind : Selected(p, out), p -> Try(Statement, Error) where [p.encoder_for : Sql.Encoding -> (p, List(Sql.Token) -> Try(List(Sql.Token), []))]
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
				.concat(Sql.clause("WHERE", if filters.len() > 1 filters.map(|f| "(${f})") else filters, " AND "))
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

	placeholder : Str -> Str
	placeholder = |name| ":${name}"

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
					Step.({ ..s, columns: s.columns.map(|c| if c.name == name { ..c, sql_type: sql_type } else c) })
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
		tables = steps.fold([], |seen, step| if seen.contains(step.table) seen else seen.append(step.table))
		tables.join_map(
			|name| {
				of_table = steps.keep_if(|step| step.table == name)
				created = of_table.join_map(|step| step.columns)
				fields = of_table.join_map(|step| step.row_fields).fold([], |seen, f| if seen.contains(f) seen else seen.append(f))
				missing = fields.keep_if(|f| !created.contains(f)).map(|f| "${name}.${f} is never created")
				twice = fields.keep_if(|f| created.keep_if(|c| c == f).len() > 1).map(|f| "${name}.${f} is created twice")
				missing.concat(twice)
			},
		)
	}

	step : Str, [Create, Alter], Code(row -> cols) -> Step(row)
	step = |table_name, kind, columns| {
		empty = { table: table_name, kind: kind, row_fields: [], columns: [], constraints: [], problems: [] }
		match Sql.columns_of(columns) {
			Ok(found) => Step.({ ..empty, row_fields: found.row_fields, columns: found.columns })
			Err(e) => Step.({ ..empty, problems: [e] })
		}
	}

	ddl_statements : Str, [Create, Alter], List(Column), List(Str) -> List(Str)
	ddl_statements = |table_name, kind, columns, constraints| {
		spell = |c| "${c.name} ${c.sql_type}${if c.nullable "" else " NOT NULL"}"
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
	## column list and nothing else.
	columns_of : Code(row -> cols) -> Try({ row_fields : List(Str), columns : List(Column) }, Error)
	columns_of = |code| {
		lam = Sql.lambda_of(code)?
		row = match lam.params {
			[only] => only
			_ => return Err(Sql.at_error(lam.meta, "a column list reads one row"))
		}
		fields = Sql.record_fields(row.ty, lam.meta)?
		entries = match lam.body {
			MakeRecord(written, _) => written
			other => return Err(Sql.at_error(other.node_meta(), "a column list is a record, one field per column"))
		}
		columns = entries.map_try(
			|entry| {
				read = match entry.value {
					Field(Param(_, _), name, _) => name
					OptField(Param(_, _), name, _) => name
					other => return Err(Sql.at_error(other.node_meta(), "`${entry.name}` must read the row's field of that name"))
				}
				if read != entry.name {
					return Err(Sql.at_error(entry.value.node_meta(), "`${entry.name}` reads `${read}`; a column keeps its field's name"))
				}
				field = match fields.find_first(|f| f.name == read) {
					Ok(f) => f
					Err(_) => return Err(Sql.at_error(entry.value.node_meta(), "the row has no field `${read}`"))
				}
				sql_type = Sql.located(Sql.column_type(field.ty), entry.value.node_meta())?
				Ok({ name: read, sql_type: sql_type, nullable: field.presence == Optional })
			},
		)?
		Ok({ row_fields: fields.map(|f| f.name), columns: columns })
	}

	## The columns a key function reads: one field, or a tuple of them.
	column_names : Code(row -> k) -> Try(List(Str), Error)
	column_names = |code| {
		lam = Sql.lambda_of(code)?
		one : Code.Ir -> Try(Str, Error)
		one = |node| match node {
			Field(Param(_, _), name, _) => Ok(name)
			other => Err(Sql.at_error(other.node_meta(), "a key reads a column of the row"))
		}
		match lam.body {
			MakeTuple(parts, _) => parts.map_try(one)
			single => Ok([one(single)?])
		}
	}

	record_fields : Code.Ty, Code.Meta -> Try(List({ name : Str, ty : Code.Ty, presence : [Required, Optional] }), Error)
	record_fields = |ty, meta| match ty {
		Record(fields) => Ok(fields)
		Named(_, backing) => Sql.record_fields(backing, meta)
		_ => Err(Sql.at_error(meta, "a row is a record, and this is `${ty.name()}`"))
	}

	## The SQL type a Roc field type maps to when a step does not say.
	column_type : Code.Ty -> Try(Str, Error)
	column_type = |ty| match ty {
		I64 => Ok("BIGINT")
		I32 => Ok("INTEGER")
		I16 => Ok("SMALLINT")
		Str => Ok("TEXT")
		Bool => Ok("BOOLEAN")
		Dec => Ok("NUMERIC")
		F64 => Ok("DOUBLE PRECISION")
		Named(_, backing) => Sql.column_type(backing)
		U64 => Err(BadSchema("SQL has no unsigned 64-bit integer; U64 goes past BIGINT's range"))
		_ => Err(BadSchema("`${ty.name()}` has no column type; a column holds one scalar"))
	}

	# ------------------------------------------------------------- translator

	## What a name in a reified function stands for.
	##
	## A row is not an SQL value: it is where columns come from, so it binds
	## to the tables it came from, and a field read off it is the column. A
	## joined row is a pair of those, which is what `.0` and `.1` take apart.
	Binding := [
		Row(Source),
		Params,
		Group(Source),
		Expr(Str),
		Fields(List({ name : Str, binding : Binding })),
	]

	## The tables a row is read from, as the joins nested them.
	Source := [Leaf(Str), Pair(Source, Source)]

	Env : {
		scope : List({ name : Str, binding : Binding }),
		param : Str -> Str,
		defs : List(Code.Def),
		depth : U64,
	}

	lambda_of : Code(f) -> Try({ params : List({ name : Str, ty : Code.Ty }), body : Code.Ir, meta : Code.Meta }, Error)
	lambda_of = |code| match Code.ir(code) {
		Lambda(params, body, meta) => Ok({ params: params, body: body, meta: meta })
		other => Err(Sql.at_error(other.node_meta(), "a clause is a function"))
	}

	body_meta : Code(f) -> Code.Meta
	body_meta = |code| match Code.ir(code) {
		Lambda(_, body, _) => body.node_meta()
		other => other.node_meta()
	}

	env_for : Code(f), List({ name : Str, ty : Code.Ty }), List(Binding), (Str -> Str) -> Env
	env_for = |code, params, bindings, param| {
		scope = params.map_with_index(
			|p, i| {
				binding = match bindings.get(i) {
					Ok(b) => b
					Err(_) => Binding.Expr("NULL")
				}
				{ name: p.name, binding: binding }
			},
		)
		{ scope: scope, param: param, defs: Code.definitions(code), depth: 0 }
	}

	## A reified function applied to what its parameters stand for.
	evaluate : Code(f), List(Binding), (Str -> Str) -> Try(Binding, Error)
	evaluate = |code, bindings, param| {
		lam = Sql.lambda_of(code)?
		if lam.params.len() != bindings.len() {
			return Err(Sql.at_error(lam.meta, "this clause takes ${bindings.len().to_str()} argument(s)"))
		}
		Sql.eval(lam.body, Sql.env_for(code, lam.params, bindings, param))
	}

	render : Code(f), List(Binding), (Str -> Str) -> Try(Str, Error)
	render = |code, bindings, param| {
		value = Sql.evaluate(code, bindings, param)?
		Ok(Sql.bare(Sql.expr_of(value, Sql.body_meta(code))?))
	}

	## The select list: a record whose fields are the result columns.
	columns : Code(f), List(Binding), (Str -> Str) -> Try(Str, Error)
	columns = |code, bindings, param| {
		meta = Sql.body_meta(code)
		match Sql.evaluate(code, bindings, param)? {
			Fields(fields) => {
				spelled = fields.map_try(|f| Ok("${Sql.bare(Sql.expr_of(f.binding, meta)?)} AS ${f.name}"))?
				Ok(Str.join_with(spelled, ", "))
			}
			_ => Err(Sql.at_error(meta, "a result row is a record, so each column has a name"))
		}
	}

	## A result row, as a later clause reads it: each field is the result
	## column of that name.
	result_columns : Code.Ty -> Binding
	result_columns = |ty| match ty {
		Record(fields) => Binding.Fields(fields.map(|f| { name: f.name, binding: Binding.Expr(f.name) }))
		Named(_, backing) => Sql.result_columns(backing)
		_ => Binding.Fields([])
	}

	expr_list : Binding, Code.Meta -> Try(List(Str), Error)
	expr_list = |binding, meta| match binding {
		Fields(fields) => fields.map_try(|f| Sql.expr_of(f.binding, meta).map_ok(Sql.bare))
		other => Ok([Sql.bare(Sql.expr_of(other, meta)?)])
	}

	expr_of : Binding, Code.Meta -> Try(Str, Error)
	expr_of = |binding, meta| match binding {
		Expr(sql) => Ok(sql)
		Row(_) => Err(Sql.at_error(meta, "a whole row has no SQL value; read one of its columns"))
		Params => Err(Sql.at_error(meta, "the parameter record has no SQL value; read one of its fields"))
		Group(_) => Err(Sql.at_error(meta, "a group's rows have no SQL value; aggregate them with `len` or `map(..).sum()`"))
		Fields(_) => Err(Sql.at_error(meta, "a record has no SQL value here; this clause takes one column"))
	}

	expr : Code.Ir, Env -> Try(Str, Error)
	expr = |node, env| Sql.expr_of(Sql.eval(node, env)?, node.node_meta())

	eval : Code.Ir, Env -> Try(Binding, Error)
	eval = |node, env| match node {
		Param(name, meta) => Sql.lookup(env, name, meta)
		Local(name, meta) => Sql.lookup(env, name, meta)

		Let(name, bound, rest, _) => {
			value = Sql.eval(bound, env)?
			Sql.eval(rest, { ..env, scope: env.scope.append({ name: name, binding: value }) })
		}

		Lit(literal, meta) => Ok(Binding.Expr(Sql.located(Sql.literal(literal), meta)?))

		Field(receiver, name, meta) => Sql.field(Sql.eval(receiver, env)?, name, env, meta)
		OptField(receiver, name, meta) => Sql.field(Sql.eval(receiver, env)?, name, env, meta)

		Index(receiver, position, meta) => match Sql.eval(receiver, env)? {
			Row(Pair(left, right)) =>
				if position == 0 {
					Ok(Binding.Row(left))
				} else {
					Ok(Binding.Row(right))
				}
			_ => Err(Sql.at_error(meta, "only a joined row has positions: `.0` is the rows joined so far, `.1` the table joined to them"))
		}

		Binop(op, lhs, rhs, meta) => {
			symbol = Sql.located(Sql.operator(op, lhs.node_ty()), meta)?
			left = Sql.expr(lhs, env)?
			right = Sql.expr(rhs, env)?
			Ok(Binding.Expr("(${left} ${symbol} ${right})"))
		}

		Unary(op, operand, meta) =>
			if op == "not" {
				match operand {
					Binop("is_eq", lhs, rhs, _) => {
						left = Sql.expr(lhs, env)?
						right = Sql.expr(rhs, env)?
						Ok(Binding.Expr("(${left} <> ${right})"))
					}
					_ => Ok(Binding.Expr("(NOT ${Sql.expr(operand, env)?})"))
				}
			} else if op == "neg" {
				Ok(Binding.Expr("(-${Sql.expr(operand, env)?})"))
			} else {
				Err(Sql.at_error(meta, "`${op}` has no SQL form"))
			}

		# A written `and` or `or` short-circuits, so it arrives as the `if` it
		# stands for. SQL's `AND` and `OR` do not promise an order, which is
		# the same answer here: a query body has no effects to order.
		If(condition, yes, no, _) => {
			test = Sql.expr(condition, env)?
			if Sql.is_bool(no, Bool.False) {
				Ok(Binding.Expr("(${test} AND ${Sql.expr(yes, env)?})"))
			} else if Sql.is_bool(yes, Bool.True) {
				Ok(Binding.Expr("(${test} OR ${Sql.expr(no, env)?})"))
			} else {
				Ok(Binding.Expr("CASE WHEN ${test} THEN ${Sql.expr(yes, env)?} ELSE ${Sql.expr(no, env)?} END"))
			}
		}

		Call(callee, args, meta) => Sql.call(callee, args, env, meta)

		Match(subject, branches, meta) => match subject {
			OptField(_, _, _) => Sql.optional(Sql.expr(subject, env)?, branches, env, meta)
			_ => Err(Sql.at_error(meta, "SQL has no tag unions; a `match` in a query reads an optional field"))
		}

		MakeRecord(entries, _) => {
			fields = entries.map_try(|entry| Ok({ name: entry.name, binding: Sql.eval(entry.value, env)? }))?
			Ok(Binding.Fields(fields))
		}

		MakeTuple(_, meta) => Err(Sql.at_error(meta, "a tuple has no SQL value; a key of several columns is a record"))
		MakeList(_, meta) => Err(Sql.at_error(meta, "SQL has no list value"))
		MakeTag(name, _, meta) => Err(Sql.at_error(meta, "SQL has no tag unions, so `${name}` has no SQL form"))
		Lambda(_, _, meta) => Err(Sql.at_error(meta, "a function inside a query means something only as the argument of `map` over a group's rows"))
		Crash(_, meta) => Err(Sql.at_error(meta, "a query cannot crash"))
		Derived(method, _, _, meta) => Err(Sql.at_error(meta, "`${method}` is derived by the compiler and has no SQL form"))
		Widen(_, meta) => Err(Sql.at_error(meta, "SQL has no tag unions, so a widening between two has no SQL form"))
		Range(_, _, _, meta) => Err(Sql.at_error(meta, "a range has no SQL form"))
		For(_, meta) => Err(Sql.at_error(meta, "SQL has no loop; a query computes over rows, not by stepping through them"))
		While(_, meta) => Err(Sql.at_error(meta, "SQL has no loop; a query computes over rows, not by stepping through them"))
		Break(_, meta) => Err(Sql.at_error(meta, "SQL has no loop to leave"))
		Return(_, meta) => Err(Sql.at_error(meta, "SQL has no loop to leave"))
	}

	lookup : Env, Str, Code.Meta -> Try(Binding, Error)
	lookup = |env, name, meta| match env.scope.find_last(|entry| entry.name == name) {
		Ok(entry) => Ok(entry.binding)
		Err(_) => Err(Sql.at_error(meta, "`${name}` is not bound here"))
	}

	field : Binding, Str, Env, Code.Meta -> Try(Binding, Error)
	field = |holder, name, env, meta| match holder {
		Row(Leaf(alias)) =>
			if alias.is_empty() {
				Ok(Binding.Expr(name))
			} else {
				Ok(Binding.Expr("${alias}.${name}"))
			}
		Row(Pair(_, _)) => Err(Sql.at_error(meta, "a joined row is a pair; take `.0` or `.1` before reading `${name}`"))
		Params => {
			spell = env.param
			Ok(Binding.Expr(spell(name)))
		}
		Fields(fields) => match fields.find_first(|f| f.name == name) {
			Ok(f) => Ok(f.binding)
			Err(_) => Err(Sql.at_error(meta, "this record has no `${name}`"))
		}
		Group(_) => Err(Sql.at_error(meta, "a group's rows have no single `${name}`; aggregate them with `len` or `map(..).sum()`"))
		Expr(_) => Err(Sql.at_error(meta, "`${name}` is read from a value that is not a row"))
	}

	## `x ?? d`, and a `match` that tests whether an optional field is there,
	## are the two ways Roc reads one. Both say what happens when it is absent,
	## which is exactly what SQL's `NULL` leaves unsaid.
	optional : Str, List(Code.Branch), Env, Code.Meta -> Try(Binding, Error)
	optional = |column, branches, env, meta| {
		present = branches.find_first(|b| Sql.branch_is(b, "Ok"))
		absent = branches.find_first(|b| Sql.branch_is(b, "Err"))
		match (present, absent) {
			(Ok(yes), Ok(no)) => {
				bound = match yes.patterns {
					[Variant(_, [Bind(name, _)], _)] => name
					_ => return Err(Sql.at_error(meta, "a present optional field is read by binding it: `Ok(value) =>`"))
				}
				otherwise = Sql.expr(no.value, env)?
				match yes.value {
					Local(name, _) if name == bound => Ok(Binding.Expr("COALESCE(${column}, ${otherwise})"))
					_ => {
						inner = Sql.expr(yes.value, { ..env, scope: env.scope.append({ name: bound, binding: Binding.Expr(column) }) })?
						Ok(Binding.Expr("CASE WHEN ${column} IS NOT NULL THEN ${inner} ELSE ${otherwise} END"))
					}
				}
			}
			_ => Err(Sql.at_error(meta, "a `match` on an optional field has an `Ok` branch and an `Err` branch"))
		}
	}

	branch_is : Code.Branch, Str -> Bool
	branch_is = |branch, tag| match branch.patterns {
		[Variant(name, _, _)] => name == tag and branch.guard == NoGuard
		_ => Bool.False
	}

	is_bool : Code.Ir, Bool -> Bool
	is_bool = |node, wanted| match node {
		Lit(Bool(b), _) => b == wanted
		_ => Bool.False
	}

	## The calls a query may make, each under the whole name a `Call` carries.
	##
	## A call to a definition of the application's own is expanded in place,
	## so a predicate or a computation written once in Roc is reused in any
	## query that calls it.
	call : Str, List(Code.Ir), Env, Code.Meta -> Try(Binding, Error)
	call = |callee, args, env, meta| {
		sql = |node| Sql.expr(node, env)
		match (callee, args) {
			("Builtin.Str.concat", [a, b]) => Ok(Binding.Expr("(${sql(a)?} || ${sql(b)?})"))
			("Builtin.Str.starts_with", [s, prefix]) => {
				p = sql(prefix)?
				Ok(Binding.Expr("(substr(${sql(s)?}, 1, length(${p})) = ${p})"))
			}
			("Builtin.Str.count_utf8_bytes", _) =>
				Err(Sql.at_error(meta, "`count_utf8_bytes` counts bytes, and SQL's `length` counts characters; the two disagree on any non-ASCII text"))
			("Builtin.Try.is_ok", [opt]) => Sql.null_test(opt, "IS NOT NULL", env, meta)
			("Builtin.Try.is_err", [opt]) => Sql.null_test(opt, "IS NULL", env, meta)
			("Builtin.List.len", [rows]) => match Sql.eval(rows, env)? {
				Group(_) => Ok(Binding.Expr("COUNT(*)"))
				_ => Err(Sql.at_error(meta, "`len` counts a group's rows, and this is not one"))
			}
			("Builtin.List.sum", [Call("Builtin.List.map", [rows, Lambda([row], body, _)], _)]) =>
				match Sql.eval(rows, env)? {
					Group(source) => {
						inner = Sql.expr(body, { ..env, scope: env.scope.append({ name: row.name, binding: Binding.Row(source) }) })?
						Ok(Binding.Expr("SUM(${Sql.bare(inner)})"))
					}
					_ => Err(Sql.at_error(meta, "`map(..).sum()` sums over a group's rows, and this is not one"))
				}
			_ =>
				if callee.starts_with("Builtin.Num.") and callee.ends_with(".to_dec") {
					match args {
						[n] => Ok(Binding.Expr("CAST(${sql(n)?} AS NUMERIC)"))
						_ => Err(Sql.at_error(meta, "`to_dec` takes one number"))
					}
				} else {
					Sql.expand(callee, args, env, meta)
				}
		}
	}

	null_test : Code.Ir, Str, Env, Code.Meta -> Try(Binding, Error)
	null_test = |node, test, env, meta| match node {
		OptField(_, _, _) => Ok(Binding.Expr("(${Sql.expr(node, env)?} ${test})"))
		_ => Err(Sql.at_error(meta, "a query tests presence only on an optional field"))
	}

	## A call to one of the application's own definitions, expanded with its
	## arguments bound to what they stand for. A row passes through as a row,
	## so a helper over `Order` reads the order's columns.
	expand : Str, List(Code.Ir), Env, Code.Meta -> Try(Binding, Error)
	expand = |callee, args, env, meta| {
		if env.depth > 32 {
			return Err(Sql.at_error(meta, "`${callee}` calls itself, and SQL has no recursion to spell it with"))
		}
		match env.defs.find_first(|def| def.name == callee) {
			Ok(def) => match def.ir {
				Lambda(params, body, _) => {
					values = args.map_try(|arg| Sql.eval(arg, env))?
					scope = params.map_with_index(
						|p, i| {
							binding = match values.get(i) {
								Ok(v) => v
								Err(_) => Binding.Expr("NULL")
							}
							{ name: p.name, binding: binding }
						},
					)
					Sql.eval(body, { ..env, scope: scope, depth: env.depth + 1 })
				}
				_ => Err(Sql.at_error(meta, "`${callee}` is not a function"))
			}
			Err(_) => Err(Sql.at_error(meta, "`${callee}` has no SQL form"))
		}
	}

	literal : Code.Lit -> Try(Str, Error)
	literal = |value| match value {
		Int(n, _) => Ok(n.to_str())
		Frac(f, _) => Ok(f.to_str())
		Fixed(d) => Ok(d.to_str())
		Bool(b) => Ok(if b "TRUE" else "FALSE")
		Str(s) => Ok(Sql.quote(s))
		Bytes(_) => Err(Unsupported("a byte literal has no portable SQL form"))
	}

	## A `Binop` names the Roc method the operator dispatched to.
	##
	## Roc's `%` and SQL's agree: both follow the sign of the dividend. Roc's
	## `//` and SQL's `/` agree only at an integer, where both truncate.
	operator : Str, Code.Ty -> Try(Str, Error)
	operator = |method, operand| {
		whole = match operand.numeric() {
			Ok(number) => number.kind == Int
			Err(_) => Bool.False
		}
		match method {
			"plus" => Ok("+")
			"minus" => Ok("-")
			"times" => Ok("*")
			"div_by" => Ok("/")
			"div_trunc_by" =>
				if whole {
					Ok("/")
				} else {
					Err(Unsupported("`//` truncates a fraction toward zero, and SQL has no portable spelling of that; divide with `/`"))
				}
			"rem_by" =>
				if whole {
					Ok("%")
				} else {
					Err(Unsupported("SQL's `%` takes integers"))
				}
			"is_lt" => Ok("<")
			"is_gt" => Ok(">")
			"is_lte" => Ok("<=")
			"is_gte" => Ok(">=")
			"is_eq" => Ok("=")
			"and" => Ok("AND")
			_ => Err(Unsupported("`${method}` has no SQL operator"))
		}
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

	quote : Str -> Str
	quote = |text| "'${text.replace_each("'", "''")}'"

	## Where a node was written, as a prefix an error message can lead with.
	at : Code.Meta -> Str
	at = |meta| {
		region = meta.region
		"${region.module_name}:${region.start_line.to_str()}:${region.start_column.to_str()}: "
	}

	at_error : Code.Meta, Str -> Error
	at_error = |meta, message| Unsupported("${Sql.at(meta)}${message}")

	located : Try(a, Error), Code.Meta -> Try(a, Error)
	located = |result, meta| match result {
		Ok(value) => Ok(value)
		Err(Unsupported(message)) => Err(Unsupported("${Sql.at(meta)}${message}"))
		Err(BadSchema(message)) => Err(BadSchema("${Sql.at(meta)}${message}"))
	}

	# --------------------------------------------------------------- encoding

	## The requirement that a record can become SQL values: the compiler
	## derives its encoder against [Sql.Encoding].
	a.Bindable : where [a.encoder_for : Sql.Encoding -> (a, List(Sql.Token) -> Try(List(Sql.Token), []))]

	## What the derived encoder writes: a column's name, then its value.
	Token := [Name(Str), Val(Value)]

	## The format the compiler derives a record's encoder against. A column
	## holds one scalar, so these are the scalars and the one record around
	## them.
	Encoding := [Row].{
		rename_field : Encoding, Str -> Str
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

	values_of : a -> Try(List({ name : Str, value : Value }), Error) where [a.Bindable]
	values_of = |record| {
		Shape : a
		encode = Shape.encoder_for(Encoding.Row)
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
