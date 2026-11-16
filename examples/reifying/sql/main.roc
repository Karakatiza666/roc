# A shop's schema and queries, written against `Sql.roc`.
#
# The rows are ordinary Roc records. The same `Order` and `Product` values the
# queries describe are the ones the application builds, inserts, passes to its
# own functions and tests with `expect`. Every clause of every query, and every
# constraint of every migration, is a Roc function over those records, reified
# where a builder method asks for a `Code(f)`.
#
# `roc main.roc` prints one SQLite script: the migrations, the seed rows, and
# each query with its parameters written in. `check.py` runs it and compares
# each query's result with the one Roc computes from the same functions over
# the same rows.

app [main!] { sql: "package.roc", time: "time/package.roc", time_sql: "time_sql/package.roc" }

import sql.Sql
import time.Time
import time_sql.TimeSql

# ------------------------------------------------------------------- rows

Customer : { id : I64, name : Str, country : Str, email ?: Str }

Product : { id : I64, title : Str, price : Dec }

Order : { id : I64, customer_id : I64, product_id : I64, quantity : I64, discount : Dec }

customers : Sql.Table(Customer)
customers = Sql.table("customers")

products : Sql.Table(Product)
products = Sql.table("products")

orders : Sql.Table(Order)
orders = Sql.table("orders")

## Something that happened in the shop, and when. `Time` is another package's
## opaque type: `Sql.roc` knows nothing of it, and `TimeSql.extension` says
## what its column type and its comparisons are in SQL.
Event : { id : I64, title : Str, at : Time }

events : Sql.Table(Event)
events = Sql.table("events")

# --------------------------------------------------- ordinary Roc functions

## What one order line costs. A query that calls it computes it in the
## database; the application calls it on the rows it holds.
line_total : Order, Product -> Dec
line_total = |order, product| product.price * order.quantity.to_dec() * (1 - order.discount)

## A wholesale order.
is_bulk : Order -> Bool
is_bulk = |order| order.quantity >= 10

expect is_bulk({ id: 1, customer_id: 1, product_id: 1, quantity: 12, discount: 0 })

expect line_total({ id: 1, customer_id: 1, product_id: 1, quantity: 4, discount: 0.25 }, { id: 1, title: "Pen", price: 2.50 }) == 7.5

# -------------------------------------------------------------- migrations

## Each step lists the columns it creates, so a migration keeps saying what it
## said when it was written even after the record gains a field. The column
## types a Roc type cannot say, like a `NUMERIC`'s precision, are one more
## function over the row.
migrations : List(Sql.Migration)
migrations = [
	Sql.migration(
		"001_catalog",
		[
			products.create(|p| { id: p.id, title: p.title, price: p.price })
				.primary_key(|p| p.id)
				.numeric(|p| p.price, 10, 2)
				.check(|p| p.price > 0)
				.done(),
		],
	),
	Sql.migration(
		"002_customers_and_orders",
		[
			customers.create(|c| { id: c.id, name: c.name, country: c.country })
				.primary_key(|c| c.id)
				.varchar(|c| c.country, 2)
				.done(),
			orders.create(|o| { id: o.id, customer_id: o.customer_id, product_id: o.product_id, quantity: o.quantity, discount: o.discount })
				.primary_key(|o| o.id)
				.references(|o| o.customer_id, customers)
				.references(|o| o.product_id, products)
				.numeric(|o| o.discount, 3, 2)
				.check(|o| o.quantity > 0 and o.discount >= 0 and o.discount < 1)
				.done(),
		],
	),
	Sql.migration("003_customer_email", [customers.add_columns(|c| { email: c.?email }).done()]),
	Sql.migration("004_events", [events.create_with([TimeSql.extension], |e| { id: e.id, title: e.title, at: e.at }).primary_key(|e| e.id).done()]),
]

# Every field of every row type is created by exactly one migration.
expect Sql.schema_gaps(migrations) == []

# Without the third migration, the schema is missing a column the code reads.
expect Sql.schema_gaps(migrations.take_first(2)) == ["customers.email is never created"]

# ------------------------------------------------------------------ seeds

seed_products : List(Product)
seed_products = [
	{ id: 1, title: "Espresso machine", price: 249.00 },
	{ id: 2, title: "Coffee beans, 1kg", price: 18.50 },
	{ id: 3, title: "Milk jug", price: 12.25 },
	{ id: 4, title: "Gift card", price: 50.00 },
]

seed_customers : List(Customer)
seed_customers = [
	ada,
	grace,
	{ id: 3, name: "Edsger", country: "NL", email: "ewd@example.com" },
	{ id: 4, name: "O'Neil", country: "US", email: "oneil@example.com" },
]

## Two seed customers, one with an `email` and one without.
ada : Customer
ada = { id: 1, name: "Ada", country: "GB", email: "ada@example.com" }

grace : Customer
grace = { id: 2, name: "Grace", country: "US" }

seed_orders : List(Order)
seed_orders = [
	{ id: 1, customer_id: 1, product_id: 1, quantity: 1, discount: 0 },
	{ id: 2, customer_id: 1, product_id: 2, quantity: 12, discount: 0.10 },
	{ id: 3, customer_id: 2, product_id: 2, quantity: 3, discount: 0 },
	{ id: 4, customer_id: 2, product_id: 3, quantity: 10, discount: 0.25 },
	{ id: 5, customer_id: 3, product_id: 4, quantity: 2, discount: 0 },
	{ id: 6, customer_id: 4, product_id: 2, quantity: 20, discount: 0.15 },
]

seed_events : List(Event)
seed_events = [
	{ id: 1, title: "Supplier founded", at: Time.from_seconds(-86_400) },
	{ id: 2, title: "Shop opens", at: Time.from_seconds(1_700_000_000) },
	{ id: 3, title: "Spring sale", at: Time.from_seconds(1_710_000_000) },
	{ id: 4, title: "Stocktake", at: Time.from_nanos(1_720_000_000_000_000_001) },
]

## One `INSERT` of an event. The function reads the event's fields, so each
## is a `?` the program binds, and the `Time` binds as the bytes
## `Sql.Param` writes: the same bytes a filter that captures a `Time` binds.
insert_event : Event -> Try(Sql.Statement, Sql.Error)
insert_event = |e| Sql.bind_captured(events.insert_one(|{}| { id: e.id, title: e.title, at: e.at }))

## One `INSERT` of a customer. The function returns the captured row, so
## each column is a `?`, and a customer with no `email` binds `NULL` there.
insert_customer : Customer -> Try(Sql.Statement, Sql.Error)
insert_customer = |c| Sql.bind_captured(customers.insert_one(|{}| c))

expect insert_customer({ id: 5, name: "Zed", country: "DE" }).map_ok(|statement| statement.sql) == Ok("INSERT INTO customers (country, email, id, name) VALUES (?1, ?2, ?3, ?4)")
expect insert_customer({ id: 5, name: "Zed", country: "DE" }).map_ok(|statement| statement.inlined) == Ok("INSERT INTO customers (country, email, id, name) VALUES ('DE', NULL, 5, 'Zed')")
expect insert_customer({ id: 6, name: "Yu", country: "JP", email: "yu@example.com" }).map_ok(|statement| statement.inlined) == Ok("INSERT INTO customers (country, email, id, name) VALUES ('JP', 'yu@example.com', 6, 'Yu')")

# ---------------------------------------------------------------- queries

## Binary operators and `NUMERIC` arithmetic, over one table. A record's
## fields reach the translator in name order, so the result columns do too.
premium =
	Sql.from(products)
		.filter(|p| p.price >= 20 and p.title != "Gift card")
		.select(|p| { title: p.title, price: p.price, with_tax: p.price * 1.2 })
		.order_by(|r| r.price, Desc)

## Two filters are two conditions, each kept whole.
two_filters =
	Sql.from(products)
		.filter(|p| p.price < 20 or p.price > 100)
		.filter(|p| p.title != "Gift card")
		.select(|p| { title: p.title })

expect two_filters.to_sql() == Ok("SELECT products.title AS title\nFROM products\nWHERE ((products.price < 20.0) OR (products.price > 100.0)) AND (products.title <> 'Gift card')")

## A parameter is a field of a record the filter takes first. Every
## `filter_by` of a query takes the same record, so its type is the fields the
## filters read between them, and `bind` accepts exactly it.
PriceBand : { low : Dec, high : Dec }

in_band =
	Sql.from(products)
		.filter_by(|band, p| p.price >= band.low)
		.filter_by(|band, p| p.price <= band.high)
		.select(|p| { title: p.title, price: p.price })
		.order_by(|r| r.price, Asc)

## An optional field is a nullable column. Roc makes the absent case explicit
## with `??`, so the query says what SQL's `NULL` would have left unsaid.
contacts =
	Sql.from(customers)
		.filter(|c| c.country != "NL")
		.select(|c| { name: c.name, email: c.?email ?? "(none)" })
		.order_by(|r| r.name, Asc)

## Every customer's purchases: a three-way join. A join makes the row a pair
## of the rows so far and the table just joined, so a clause takes it apart
## with a tuple pattern, and the second join's condition reads the order out
## of the first join's pair.
Purchase : ((Customer, Order), Product)

purchases =
	Sql.from(customers)
		.join(orders, |c, o| o.customer_id == c.id)
		.join(products, |(_, o), p| o.product_id == p.id)

## One line of the report. It calls `line_total`, so the database computes
## the same total the application does, from one definition.
report_line : Purchase -> { customer : Str, product : Str, quantity : I64, total : Dec }
report_line = |((c, o), p)| { customer: c.name, product: p.title, quantity: o.quantity, total: line_total(o, p) }

bulk_purchase : Purchase -> Bool
bulk_purchase = |((_, o), _)| is_bulk(o)

bulk_lines =
	purchases
		.filter(bulk_purchase)
		.select(report_line)
		.order_by(|r| r.total, Desc)

## Revenue per country. The aggregate is ordinary Roc over a group's rows, so
## `rows.len()` is `COUNT(*)` and `rows.map(..).sum()` is `SUM`.
CountryRevenue : { country : Str, orders : U64, revenue : Dec }

country_revenue : Str, List(Purchase) -> CountryRevenue
country_revenue = |country, rows| {
	country: country,
	orders: rows.len(),
	revenue: rows.map(|((_, o), p)| line_total(o, p)).sum(),
}

revenue_by_country =
	purchases
		.group_by(|((c, _), _)| c.country)
		.aggregate(country_revenue)
		.order_by(|r| r.revenue, Desc)

## A query written inside a function, which reads the function's own
## parameter. The value exists only when the program runs, so the translator
## writes a `?` for it while the compiler runs, and the program binds the
## value the function was called with.
orders_of_at_least : I64 -> Try(Sql.Statement, Sql.Error)
orders_of_at_least = |min_quantity| Sql.bind_captured(Sql.select_where(orders, [], |o| o.quantity >= min_quantity))

## A filter that compares a column of another package's opaque type with a
## captured value of it. `TimeSql.extension` says `<` on `Time` is `<` on
## the column, and the captured `Time` binds as its `Sql.Param` bytes.
events_before : Time -> Try(Sql.Statement, Sql.Error)
events_before = |cutoff| Sql.bind_captured(Sql.select_where(events, [TimeSql.extension], |e| e.at < cutoff))

## `>` and `==` on `Time` come from the same extension, and `!=` is `NOT`
## of the extension's `==`.
events_after : Time -> Try(Sql.Statement, Sql.Error)
events_after = |cutoff| Sql.bind_captured(Sql.select_where(events, [TimeSql.extension], |e| e.at > cutoff))

events_at : Time -> Try(Sql.Statement, Sql.Error)
events_at = |t| Sql.bind_captured(Sql.select_where(events, [TimeSql.extension], |e| e.at == t))

events_not_at : Time -> Try(Sql.Statement, Sql.Error)
events_not_at = |t| Sql.bind_captured(Sql.select_where(events, [TimeSql.extension], |e| e.at != t))

## A filter that compares a whole row with a captured customer. The compiler
## compares an optional field by its presence first, so two customers with
## no `email` are equal, and the description says so: a test of each
## `email`, which SQL writes as `IS`, because `IS` treats `NULL` as a value.
## The fields the filter reads from `c` are slots of their own, and so is
## `c`, which the `email` test reads whole.
same_customer : Customer -> Try(Sql.Statement, Sql.Error)
same_customer = |c| Sql.bind_captured(Sql.select_where(customers, [], |row| row == c))

expect same_customer({ id: 2, name: "Grace", country: "US" }).map_ok(|statement| statement.inlined) == Ok("SELECT *\nFROM customers\nWHERE (customers.country = 'US') AND (customers.email IS NULL) AND (customers.id = 2) AND (customers.name = 'Grace')")

## The same filter with `!=`. The compiler pushes the `not` into the
## branches, and SQLite writes the answer as `IS NOT`.
other_customer : Customer -> Try(Sql.Statement, Sql.Error)
other_customer = |c| Sql.bind_captured(Sql.select_where(customers, [], |row| row != c))

expect other_customer({ id: 2, name: "Grace", country: "US" }).map_ok(|statement| statement.inlined) == Ok("SELECT *\nFROM customers\nWHERE (customers.country <> 'US') OR (customers.email IS NOT NULL) OR (customers.id <> 2) OR (customers.name <> 'Grace')")

# ------------------------------------------------ the same queries, in Roc

## The join, as ordinary Roc. It is what the SQL result is checked against.
purchases_in_memory : List(Purchase)
purchases_in_memory =
	seed_customers.join_map(
		|c| seed_orders.keep_if(|o| o.customer_id == c.id).join_map(
			|o| seed_products.keep_if(|p| p.id == o.product_id).map(|p| ((c, o), p)),
		),
	)

bulk_lines_in_memory : List({ customer : Str, product : Str, quantity : I64, total : Dec })
bulk_lines_in_memory = purchases_in_memory.keep_if(bulk_purchase).map(report_line)

revenue_by_country_in_memory : List(CountryRevenue)
revenue_by_country_in_memory = {
	countries = purchases_in_memory.fold([], |seen, purchase| if (seen.contains(purchase.0.0.country)) seen else seen.append(purchase.0.0.country))
	countries.map(|country| country_revenue(country, purchases_in_memory.keep_if(|purchase| purchase.0.0.country == country)))
}

orders_of_at_least_in_memory : I64 -> List(Order)
orders_of_at_least_in_memory = |min_quantity| seed_orders.keep_if(|o| o.quantity >= min_quantity)

## A `Time` in a result row is the blob the database stores, which is the
## bytes `Sql.Param` writes for it.
events_before_in_memory : Time -> List({ id : I64, title : Str, at : { blob : Str } })
events_before_in_memory = |cutoff| events_in_memory(|e| e.at < cutoff)

## The events `keep` keeps, as a result row of them reads.
events_in_memory : (Event -> Bool) -> List({ id : I64, title : Str, at : { blob : Str } })
events_in_memory = |keep| seed_events.keep_if(keep).map(|e| { id: e.id, title: e.title, at: { blob: Sql.hex(Sql.param_bytes(e.at)) } })

# ---------------------------------------------------------------- refusals

# A translator refuses what SQL cannot say, and names the construct. The
# line it was written on comes with source provenance, which is not in the
# description yet. `count_utf8_bytes` has an SQL look-alike, `length`, that counts characters
# instead, so a translator that mapped one onto the other would compute a
# different answer for any name with an accent in it.
byte_length = Sql.from(customers).filter(|c| c.name.count_utf8_bytes() > 5).select(|c| { name: c.name })

expect byte_length.to_sql() == Err(Unsupported("`count_utf8_bytes` counts bytes, and SQL's `length` counts characters; the two disagree on any non-ASCII text"))

# Roc's `//` truncates a `Dec` toward zero. SQL has no portable spelling of
# that, so the translator refuses it rather than emit a `/` that rounds
# differently in each database.
halves = Sql.from(products).select(|p| { half: p.price // 2 })

expect {
	match halves.to_sql() {
		Err(Unsupported(message)) => message.contains("`//` truncates a fraction")
		_ => Bool.False
	}
}

# A helper one clause calls twice. Each call is expanded in place, with its
# parameter bound to what the argument stands for.
with_tax : Dec -> Dec
with_tax = |price| price * 1.2

taxed = Sql.from(products).select(|p| { plain: with_tax(p.price), doubled: with_tax(p.price * 2) })

expect taxed.to_sql() == Ok("SELECT (products.price * 2.0) * 1.2 AS doubled, products.price * 1.2 AS plain\nFROM products")

# SQL has no recursion to spell a function that calls itself with, so a call
# of one is refused and the reason is named.
halve_until : Dec, U8 -> Dec
halve_until = |x, n| if (n == 0) x else halve_until(x, n - 1) / 2

halved = Sql.from(products).select(|p| { small: halve_until(p.price, 3) })

expect halved.to_sql() == Err(Unsupported("a function that calls itself has no SQL form; SQL has no recursion to spell it with"))

# A row is where columns come from, not a value a column can hold.
whole_rows = Sql.from(products).select(|p| { product: p })

expect {
	match whole_rows.to_sql() {
		Err(Unsupported(message)) => message.contains("a whole row has no SQL value")
		_ => Bool.False
	}
}

# A `Time` column is compared through the extension, never as SQL reads a
# builtin's `is_lt`.
expect events_before(Time.from_seconds(0)).map_ok(|statement| statement.sql) == Ok("SELECT *\nFROM events\nWHERE events.at < ?1")

# ------------------------------------------------------------------ output

expected_bulk_lines : Str
expected_bulk_lines =
	\\SELECT customers.name AS customer, products.title AS product, orders.quantity AS quantity, (products.price * CAST(orders.quantity AS NUMERIC)) * (1.0 - orders.discount) AS total
	\\FROM customers
	\\JOIN orders ON orders.customer_id = customers.id
	\\JOIN products ON orders.product_id = products.id
	\\WHERE orders.quantity >= 10
	\\ORDER BY total DESC

expect bulk_lines.to_sql() == Ok(expected_bulk_lines)

# A parameter is a placeholder until it is bound, and bound from the record
# type the filter reads.
expect {
	match in_band.bind({ low: 10, high: 20 }) {
		Ok(statement) => statement.sql.contains(":low") and statement.params.len() == 2
		Err(_) => Bool.False
	}
}

section : Str, Try(Str, Sql.Error) -> Str
section = |name, rendered| match rendered {
	Ok(sql) => "-- ${name}\n${sql}"
	Err(Unsupported(message)) => "-- ${name} is unsupported: ${message}"
	Err(BadSchema(message)) => "-- ${name} has a bad schema: ${message}"
}

query : Str, Try(Sql.Statement, Sql.Error), Str -> Str
query = |name, bound, reference| {
	checked = if (reference.is_empty()) "" else "\n-- roc: ${reference}"
	section("query: ${name}", bound.map_ok(|statement| "${statement.inlined};${checked}"))
}

## A statement with `?` placeholders. Its values go on a line of their own,
## as JSON, which `check.py` binds.
bound_query : Str, Try(Sql.Statement, Sql.Error), Str -> Str
bound_query = |name, bound, reference| {
	json = |value| match value {
		Integer(n) => n.to_str()
		Numeric(d) => d.to_str()
		Text(text) => Json.to_str(text)
		Boolean(b) => if (b) "true" else "false"
		Blob(bytes) => "{\"blob\": \"${Sql.hex(bytes)}\"}"
		Null => "null"
	}
	section(
		"query: ${name}",
		bound.map_ok(|statement| "-- params: [${Str.join_with(statement.params.map(|p| json(p.value)), ", ")}]\n${statement.sql};\n-- roc: ${reference}"),
	)
}

# --------------------------------------------------------------- numerals

## A numeral kept as the source wrote it. A literal of a type with its own
## `from_numeral` reifies as a `Numeral` literal, which the translator writes
## as exact decimal text.
Written := [Written(Numeral)].{
	from_numeral : Numeral -> Try(Written, [InvalidNumeral(Str)])
	from_numeral = |n| Ok(Written(n))
}

written : Written -> Code.Lit
written = |value| match value {
	Written(n) => Numeral(n)
}

expect Sql.literal(written(300.Written)) == Ok("300")
expect Sql.literal(written(0.050.Written)) == Ok("0.050")
expect Sql.literal(written(12345678901234567890123.25.Written)) == Ok("12345678901234567890123.25")

# The edge cases of the exact decimal text. Each one Dec holds reads back as
# the `Dec` that `Dec.from_numeral` makes of its numeral.
numeral : Written -> Numeral
numeral = |value| match value {
	Written(n) => n
}

## Whether the decimal text of `value` parses as the `Dec` its numeral converts to.
reads_as_dec : Written -> Bool
reads_as_dec = |value| {
	n = numeral(value)
	match (Dec.from_str(Sql.numeral_text(n)), Dec.from_numeral(n)) {
		(Ok(text), Ok(converted)) => text == converted
		_ => Bool.False
	}
}

negative : Written
negative = -2.5

negative_whole : Written
negative_whole = -7

# Zero, with no point and with one.
expect Sql.literal(written(0.Written)) == Ok("0")
expect reads_as_dec(0.Written)
expect Sql.literal(written(0.0.Written)) == Ok("0.0")
expect reads_as_dec(0.0.Written)
# Leading zeros after the point.
expect reads_as_dec(0.050.Written)
expect Sql.literal(written(0.000001.Written)) == Ok("0.000001")
expect reads_as_dec(0.000001.Written)
# Negative numbers.
expect Sql.literal(written(negative)) == Ok("-2.5")
expect reads_as_dec(negative)
expect Sql.literal(written(negative_whole)) == Ok("-7")
expect reads_as_dec(negative_whole)
# Digit bytes that carry in base 256, before the point and after it.
expect Sql.literal(written(255.Written)) == Ok("255")
expect reads_as_dec(255.Written)
expect Sql.literal(written(256.Written)) == Ok("256")
expect reads_as_dec(256.Written)
expect Sql.literal(written(65_535.Written)) == Ok("65535")
expect reads_as_dec(65_535.Written)
expect Sql.literal(written(65_536.Written)) == Ok("65536")
expect reads_as_dec(65_536.Written)
expect Sql.literal(written(0.256.Written)) == Ok("0.256")
expect reads_as_dec(0.256.Written)
# More than 20 digits: one Dec holds, and two it does not.
expect Sql.literal(written(100.000000000000000001.Written)) == Ok("100.000000000000000001")
expect reads_as_dec(100.000000000000000001.Written)
expect Sql.literal(written(340282366920938463463374607431768211456.Written)) == Ok("340282366920938463463374607431768211456")
expect Sql.literal(written(0.0000000000000000000000000001.Written)) == Ok("0.0000000000000000000000000001")
# Integers with no point.
expect reads_as_dec(300.Written)
expect Sql.literal(written(18446744073709551616.Written)) == Ok("18446744073709551616")
expect reads_as_dec(18446744073709551616.Written)

script : Str
script =
	Str.join_with(
		[
			section("migrations", Sql.migrate(migrations)),
			section("seed", products.insert(seed_products)),
			section("seed", seed_customers.map_try(insert_customer).map_ok(|statements| Str.join_with(statements.map(|statement| "${statement.inlined};"), "\n"))),
			section("seed", orders.insert(seed_orders)),
			section("seed", seed_events.map_try(insert_event).map_ok(|statements| Str.join_with(statements.map(|statement| "${statement.inlined};"), "\n"))),
			query("premium", premium.bind({}), ""),
			query("in_band", in_band.bind({ low: 10, high: 20 }), ""),
			query("contacts", contacts.bind({}), ""),
			query("bulk_lines", bulk_lines.bind({}), Json.to_str(bulk_lines_in_memory)),
			query("revenue_by_country", revenue_by_country.bind({}), Json.to_str(revenue_by_country_in_memory)),
			bound_query("orders_of_at_least", orders_of_at_least(10), Json.to_str(orders_of_at_least_in_memory(10))),
			bound_query("events_before", events_before(Time.from_seconds(1_705_000_000)), Json.to_str(events_before_in_memory(Time.from_seconds(1_705_000_000)))),
			bound_query("events_after_negative", events_after(Time.from_seconds(-100_000)), Json.to_str(events_in_memory(|e| e.at > Time.from_seconds(-100_000)))),
			bound_query("events_at", events_at(Time.from_nanos(1_720_000_000_000_000_001)), Json.to_str(events_in_memory(|e| e.at == Time.from_nanos(1_720_000_000_000_000_001)))),
			bound_query("events_not_at", events_not_at(Time.from_seconds(1_700_000_000)), Json.to_str(events_in_memory(|e| e.at != Time.from_seconds(1_700_000_000)))),
			bound_query("same_customer_without_email", same_customer(grace), Json.to_str(seed_customers.keep_if(|c| c == grace))),
			bound_query("same_customer_with_email", same_customer(ada), Json.to_str(seed_customers.keep_if(|c| c == ada))),
		],
		"\n\n",
	)

main! = |_args| {
	echo!("${script}\n")
	Ok({})
}
