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
					_ => return Err(Unsupported("an ordering reads one result row"))
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
	## column list and nothing else. A record's fields arrive in name order,
	## so the columns do too.
	columns_of : Code(row -> cols) -> Try({ row_fields : List(Str), columns : List(Column) }, Error)
	columns_of = |code| {
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
					Err(_) => return Err(Unsupported("`${entry.name}` must read the row's field of that name"))
				}
				if read != entry.name {
					return Err(Unsupported("`${entry.name}` reads `${read}`; a column keeps its field's name"))
				}
				field = match fields.find_first(|f| f.name == read) {
					Ok(f) => f
					Err(_) => return Err(Unsupported("the row has no field `${read}`"))
				}
				sql_type = Sql.column_type(field.ty)?
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

	record_fields : Code.Ty -> Try(List({ name : Str, ty : Code.Ty, presence : [Required, Optional] }), Error)
	record_fields = |ty| match ty {
		Record(fields) => Ok(fields)
		Named(_, backing) => Sql.record_fields(backing)
		_ => Err(Unsupported("a row is a record, and this is `${ty.name()}`"))
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
		params : List(Binding),
		nodes : List({ id : U32, binding : Binding }),
		param : Str -> Str,
		depth : U64,
	}

	## A reified function applied to what its parameters stand for.
	evaluate : Code(f), List(Binding), (Str -> Str) -> Try(Binding, Error)
	evaluate = |code, bindings, param| {
		graph = Code.graph(code)
		root = graph.root_row()
		if root.params.len() != bindings.len() {
			return Err(Unsupported("this clause takes ${bindings.len().to_str()} argument(s)"))
		}
		Sql.eval(graph.to_tree(root.id), { graph: graph, params: bindings, nodes: [], param: param, depth: 0 })
	}

	render : Code(f), List(Binding), (Str -> Str) -> Try(Str, Error)
	render = |code, bindings, param| {
		value = Sql.evaluate(code, bindings, param)?
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
		Named(_, backing) => Sql.result_columns(backing)
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
			Prim(prim) => Sql.prim(prim.owner, prim.method, args, env)
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
				Row(Pair(left, right)) => if position == 0 Ok(Binding.Row(left)) else Ok(Binding.Row(right))
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

	key_is : Code.Key, Str -> Bool
	key_is = |key, name| match key {
		Tag(tag) => tag == name
		Lit(Bool(flag)) => (if flag "True" else "False") == name
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

	## The builtins a query may call, by owner and method.
	prim : Str, Str, List(Code.Tree), Env -> Try(Binding, Error)
	prim = |owner, method, args, env| {
		sql = |node| Sql.expr(node, env)
		match ("${owner}.${method}", args) {
			("Str.concat", [a, b]) => Ok(Binding.Expr("(${sql(a)?} || ${sql(b)?})"))
			("Str.starts_with", [s, prefix]) => {
				p = sql(prefix)?
				Ok(Binding.Expr("(substr(${sql(s)?}, 1, length(${p})) = ${p})"))
			}
			("Str.count_utf8_bytes", _) =>
				Err(Unsupported("`count_utf8_bytes` counts bytes, and SQL's `length` counts characters; the two disagree on any non-ASCII text"))
			("Try.is_ok", [opt]) => Sql.null_test(opt, "IS NOT NULL", env)
			("Try.is_err", [opt]) => Sql.null_test(opt, "IS NULL", env)
			("List.len", [rows]) => match Sql.eval(rows, env)? {
				Group(_) => Ok(Binding.Expr("COUNT(*)"))
				_ => Err(Unsupported("`len` counts a group's rows, and this is not one"))
			}
			("List.sum", [mapped]) => Sql.sum(mapped, env)
			("Bool.not", [operand]) => match operand {
				Op({ op: Prim({ owner: _, method: "is_eq" }), args: [lhs, rhs], .. }) => Ok(Binding.Expr("(${sql(lhs)?} <> ${sql(rhs)?})"))
				_ => Ok(Binding.Expr("(NOT ${sql(operand)?})"))
			}
			(_, [n]) if method == "to_dec" and owner.starts_with("Num.") => Ok(Binding.Expr("CAST(${sql(n)?} AS NUMERIC)"))
			(_, [n]) if method == "negate" => Ok(Binding.Expr("(-${sql(n)?})"))
			(_, [lhs, rhs]) => Sql.binary(owner, method, lhs, rhs, env)
			_ => Err(Unsupported("`${owner}.${method}` has no SQL form"))
		}
	}

	## `rows.map(f).sum()` over a group's rows is `SUM` of `f`, with `f`'s
	## row read as the group's row.
	sum : Code.Tree, Env -> Try(Binding, Error)
	sum = |mapped, env| match mapped {
		Op({ op: Prim({ owner: "List", method: "map" }), args: [rows, Op({ op: Closure(row), args: captured, .. })], .. }) =>
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
		Bool(b) => Ok(if b "TRUE" else "FALSE")
		Str(s) => Ok(Sql.quote(s))
		Bytes(_) => Err(Unsupported("a byte literal has no portable SQL form"))
	}

	## A two-operand builtin, as the SQL operator for its method.
	##
	## The normal form puts an integer literal first in a comparison, as
	## `10 <= quantity`. SQL reads as a column test, so a comparison whose
	## left operand is the only literal is written the other way round, with
	## the mirrored operator: the same comparison.
	binary : Str, Str, Code.Tree, Code.Tree, Env -> Try(Binding, Error)
	binary = |owner, method, lhs, rhs, env| {
		mirrored = Sql.mirror(method)
		flip = Sql.is_literal(lhs) and !Sql.is_literal(rhs) and !mirrored.is_empty()
		symbol = Sql.operator(owner, if flip mirrored else method)?
		left = Sql.expr(if flip rhs else lhs, env)?
		right = Sql.expr(if flip lhs else rhs, env)?
		Ok(Binding.Expr("(${left} ${symbol} ${right})"))
	}

	mirror : Str -> Str
	mirror = |method| match method {
		"is_lt" => "is_gt"
		"is_gt" => "is_lt"
		"is_lte" => "is_gte"
		"is_gte" => "is_lte"
		"is_eq" => "is_eq"
		_ => ""
	}

	is_literal : Code.Tree -> Bool
	is_literal = |tree| match tree {
		Op({ op: Lit(_), .. }) => Bool.True
		_ => Bool.False
	}

	## The SQL operator of a builtin's method.
	##
	## Roc's `%` and SQL's agree: both follow the sign of the dividend. Roc's
	## `//` and SQL's `/` agree only at an integer, where both truncate.
	operator : Str, Str -> Try(Str, Error)
	operator = |owner, method| {
		whole = owner.starts_with("Num.I") or owner.starts_with("Num.U")
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
			_ => Err(Unsupported("`${owner}.${method}` has no SQL operator"))
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

	# --------------------------------------------------------------- encoding

	## The requirement that a record can become SQL values: the compiler
	## derives its encoder against [Sql.Encoding].
	a.Bindable :  where [a.encoder_for : Sql.Encoding -> (a, List(Sql.Token) -> Try(List(Sql.Token), []))]

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
