import Ql
import Surreal
import Translate

# Tests of `Translate` on a small domain: each clause is reified through a
# helper below, which declares `Surreal`'s cut, and translated. Nothing
# outside this file imports it.
TranslateTest :: {}.{
	code_primitives = (Surreal.Link.get, Surreal.Link.id, Surreal.Id.is_eq, Surreal.Id.key, Surreal.Id.table, Surreal.Datetime.is_lt, Surreal.Datetime.is_lte, Surreal.Text.is_email, Surreal.Text.is_url, Surreal.Text.is_domain, Surreal.Text.is_ip, Surreal.Text.is_ipv4, Surreal.Text.is_ipv6, Surreal.Text.is_uuid, Surreal.Text.is_ulid, Surreal.Text.is_semver, Surreal.Text.is_alpha, Surreal.Text.is_alphanum, Surreal.Text.is_numeric, Surreal.Text.is_latitude, Surreal.Text.is_longitude, Surreal.Text.is_datetime, Surreal.Text.matches, Surreal.Text.similarity_jaro, Surreal.Text.similarity_jaro_winkler, Surreal.Text.distance_levenshtein, Surreal.Text.distance_damerau_levenshtein, Surreal.Text.distance_normalized_levenshtein, Surreal.Text.is_ascii, Surreal.Text.is_hexadecimal, Surreal.Hash.sha256, Surreal.Hash.blake3, Surreal.Hash.md5, Surreal.Hash.sha1, Surreal.Hash.sha512, Surreal.Array.distinct, Surreal.Array.union, Surreal.Array.intersect, Surreal.Array.complement, Surreal.Time.now, Surreal.Time.floor, Surreal.Time.ceil, Surreal.Time.round, Surreal.Time.group, Surreal.Time.plus, Surreal.Time.minus, Surreal.Time.wday, Surreal.Time.yday, Surreal.Time.week, Surreal.Time.unix, Surreal.Time.unix_millis, Surreal.Time.unix_micros, Surreal.Time.nano, Surreal.Time.format, Surreal.Time.from_unix, Surreal.Time.year, Surreal.Time.month, Surreal.Time.day, Surreal.Time.hour, Surreal.Time.minute, Surreal.Time.second, Surreal.Math.mean, Surreal.Math.median, Surreal.Math.stddev, Surreal.Math.variance, Surreal.Math.percentile, Surreal.Rand.uuid, Surreal.Rand.ulid, Surreal.Rand.int)

	## The graph of a clause over rows of the list's element type.
	describe1 : List(row), Code(row -> out) -> Code.Graph
	describe1 = |_, code| code.graph()

	describe2 : List(p), List(row), Code((p, row -> out)) -> Code.Graph
	describe2 = |_, _, code| code.graph()

	describe_group : List(k), List(row), Code((k, List(row) -> out)) -> Code.Graph
	describe_group = |_, _, code| code.graph()

	describe_pair : List(row), List(e), Code((row, List(e)) -> out) -> Code.Graph
	describe_pair = |_, _, code| code.graph()

	## A clause that reads values captured from around it, with each captured
	## value as its variable.
	describe_bound : List(row), Code(row -> Bool) -> Code.Bound(Try(Str, Ql.Error))
	describe_bound = |_, code| Code.bound(code, Translate.render(code.graph(), [Translate.document("", Bool.False)], Translate.variable))
}

Address : { city : Str, zip ?: Str }

Customer : { id : Str, name : Str, address : Address, tags : List(Str), born : Surreal.Datetime }

Product : { id : Str, title : Str, price : Dec }

Item : { product : Surreal.Link(Product), qty : I64 }

Payment : [Card({ last4 : Str }), Cash, Invoice({ contact : Surreal.Link(Customer), due : Str }), Points(I64), Split(I64, I64)]

Order : { id : Str, customer : Surreal.Link(Customer), items : List(Item), payment : Payment, total : Dec }

Purchased : { id : Str, from : Surreal.Link(Customer), to : Surreal.Link(Product), quantity : I64 }

customers : List(Customer)
customers = []

orders : List(Order)
orders = []

purchases : List(Purchased)
purchases = []

Sample : { id : Str, text : Str, other : Str, n : I64, m : I64, d : Dec, f : F64, nums : List(I64), grid : List(List(I64)), words : List(Str), opt ?: Str, email : Str, at : Surreal.Datetime, scores : List(F64), times : List(Surreal.Datetime) }

samples : List(Sample)
samples = []

ada_id : Surreal.Id(Customer)
ada_id = Surreal.Id.({ table: "customer", key: "ada", phantom: [] })

new_year : Surreal.Datetime
new_year = Surreal.Datetime.({ iso: "2020-01-01T00:00:00Z" })

half_second : Surreal.Datetime
half_second = Surreal.Datetime.({ iso: "2026-03-04T05:06:07.5Z" })

row : Translate.Binding
row = Translate.document("", Bool.False)

where_ : Code.Graph -> Try(Str, Ql.Error)
where_ = |graph| Translate.render(graph, [row], Translate.variable)

selected : Code.Graph -> Try(List({ name : Str, surql : Str }), Ql.Error)
selected = |graph| Translate.columns(graph, [row], Translate.variable)

line_total : Item -> I64
line_total = |i| i.qty * 2

same : Surreal.Datetime, Surreal.Datetime -> Bool
same = |a, b| a == b

iso_of : Surreal.Datetime -> Str
iso_of = |Surreal.Datetime.(d)| d.iso

hour_of : Sample -> Surreal.Datetime
hour_of = |s| Surreal.Time.floor(s.at, Surreal.Time.hours(1))

depth : I64 -> I64
depth = |n| if (n <= 0) 0 else depth(n - 1) + 1

# Queries, row by row.
expect where_(TranslateTest.describe1(orders, |o| o.customer.get().address.city == "Paris")) == Ok("customer.address.city = 'Paris'")
expect where_(TranslateTest.describe1(orders, |o| o.items.any(|i| i.qty > 3))) == Ok("items.any(|$v1| $v1.qty > 3)")
expect where_(
	TranslateTest.describe1(
		orders,
		|o| match o.payment {
			Card(c) => c.last4 == "4242"
			_ => Bool.False
		},
	),
) == Ok("(IF payment.kind = 'Card' THEN payment.last4 = '4242' ELSE false END)")
expect Translate.render(TranslateTest.describe2([{ min_total: 0 }], orders, |p, o| o.total >= p.min_total), [Translate.Binding.Params, row], Translate.variable) == Ok("total >= $min_total")
expect where_(TranslateTest.describe1(orders, |o| o.customer.id() == ada_id)) == Ok("customer = customer:⟨ada⟩")
expect selected(TranslateTest.describe1(orders, |o| { who: o.customer.get().name, n: o.items.len() })) == Ok([{ name: "n", surql: "items.len()" }, { name: "who", surql: "customer.name" }])
expect selected(TranslateTest.describe1(orders, |o| { customer: o.customer.get(), total: o.total })) == Ok([{ name: "customer", surql: "customer.*" }, { name: "total", surql: "total" }])
expect selected(TranslateTest.describe1(customers, |c| { note: c.address.?zip ?? "-" })) == Ok([{ name: "note", surql: "address.zip ?? '-'" }])
expect {
	graph = TranslateTest.describe_pair(customers, purchases, |(c, bought)| { name: c.name, titles: bought.keep_if(|e| e.quantity > 2).map(|e| e.to.get().title) })
	Translate.columns(graph, [Translate.Binding.Pair(row, Translate.outgoing("purchased"))], Translate.variable)
		== Ok([{ name: "name", surql: "name" }, { name: "titles", surql: "->purchased.filter(|$v1| $v1.quantity > 2).map(|$v2| $v2.out.title)" }])
}
expect {
	key = Translate.evaluate(TranslateTest.describe1(orders, |o| o.customer.get().address.city), [row], Translate.variable)
	graph = TranslateTest.describe_group([""], orders, |city, rows| { city, orders: rows.len(), revenue: rows.map(|o| o.total).sum() })
	match key {
		Ok(k) => Translate.columns(graph, [k, Translate.Binding.Group(row)], Translate.variable) == Ok([{ name: "city", surql: "customer.address.city" }, { name: "orders", surql: "count()" }, { name: "revenue", surql: "math::sum(total)" }])
		Err(_) => Bool.False
	}
}

# The writes that read a clause.
expect Translate.assignments(TranslateTest.describe1(orders, |o| { ..o, total: o.total * 0.9, payment: Cash }), [row], Translate.variable) == Ok([{ name: "payment", surql: "'Cash'" }, { name: "total", surql: "total * 0.9dec" }])
expect where_(TranslateTest.describe1(orders, |o| o.items.is_empty())) == Ok("items.len() = 0")
expect Translate.assignments(TranslateTest.describe1(orders, |o| { ..o, payment: Card({ last4: "1" }) }), [row], Translate.variable) == Ok([{ name: "payment", surql: "{ kind: 'Card', last4: '1' }" }])
expect Translate.assignments(TranslateTest.describe1(orders, |o| { ..o, payment: Split(1, 2) }), [row], Translate.variable) == Ok([{ name: "payment", surql: "{ kind: 'Split', _0: 1, _1: 2 }" }])
expect Translate.assignments(TranslateTest.describe1(orders, |o| o), [row], Translate.variable) == Err(Unsupported("this update changes no field"))

# The prim table.
expect where_(TranslateTest.describe1(orders, |o| o.customer.id().key() == "ada")) == Ok("record::id(customer) = 'ada'")
expect where_(TranslateTest.describe1(customers, |c| c.id != "bob")) == Ok("record::id(id) != 'bob'")
expect where_(TranslateTest.describe1(orders, |o| o.customer.get().id == "ada")) == Ok("record::id(customer) = 'ada'")
expect where_(TranslateTest.describe1(orders, |o| (o.total + 1) * 2 - o.total / 4 < 10)) == Ok("(((total + 1.0dec) * 2.0dec) - (total / 4.0dec)) < 10.0dec")
expect where_(TranslateTest.describe1(orders, |o| o.items.any(|i| i.qty // 2 == 1 and i.qty % 2 == 0))) == Ok("items.any(|$v1| (($v1.qty / 2) = 1) AND (($v1.qty % 2) = 0))")
expect where_(TranslateTest.describe1(orders, |o| o.total // 2 > 1)) == Err(Unsupported("`//` on `Num.Dec` truncates a fraction, and SurrealDB's `/` does not; divide with `/`"))
expect where_(TranslateTest.describe1(orders, |o| o.items.any(|i| i.qty.to_dec() > o.total))) == Ok("items.any(|$v1| <decimal>$v1.qty > total)")
expect where_(TranslateTest.describe1(orders, |o| o.items.len().to_i64_wrap() > 1)) == Ok("items.len() > 1")
expect where_(TranslateTest.describe1(customers, |c| "${c.name}!${c.address.city}" == "Ada!Paris")) == Ok("(name + '!' + address.city) = 'Ada!Paris'")
expect where_(TranslateTest.describe1(customers, |c| c.name.starts_with("A") or c.name.ends_with("a") or c.name.contains("d"))) == Ok("string::starts_with(name, 'A') OR string::ends_with(name, 'a') OR string::contains(name, 'd')")
expect where_(TranslateTest.describe1(customers, |c| c.tags.contains("vip") and !c.tags.is_empty())) == Ok("(tags CONTAINS 'vip') AND (!(tags.len() = 0))")
expect where_(TranslateTest.describe1(orders, |o| o.items.all(|i| i.qty > 0))) == Ok("items.all(|$v1| $v1.qty > 0)")
expect where_(TranslateTest.describe1(orders, |o| o.items.map(|i| i.qty).sum() > 5)) == Ok("math::sum(items.map(|$v1| $v1.qty)) > 5")
expect where_(TranslateTest.describe1(orders, |o| o.items.find_first(|i| i.qty > 1).is_ok())) == Ok("items.find(|$v1| $v1.qty > 1) IS NOT NONE")
expect where_(TranslateTest.describe1(orders, |o| o.items.map(|i| i.product.get().price).sum() > o.total)) == Ok("math::sum(items.map(|$v1| $v1.product.price)) > total")
expect where_(TranslateTest.describe1(customers, |c| c.born < new_year)) == Ok("born < d'2020-01-01T00:00:00Z'")
expect where_(TranslateTest.describe1(customers, |c| c.born == new_year)) == Ok("born = d'2020-01-01T00:00:00Z'")
expect where_(TranslateTest.describe1(customers, |c| c.address.?zip.is_err())) == Ok("address.zip IS NONE")
expect where_(TranslateTest.describe1(customers, |c| c.name.is_empty())) == Ok("name = ''")

# Unions, guards and optional values.
expect where_(
	TranslateTest.describe1(
		orders,
		|o| match o.payment {
			Points(n) => n > 3
			Cash => Bool.True
			_ => Bool.False
		},
	),
) == Ok("(IF payment = 'Cash' THEN true ELSE IF payment.kind = 'Points' THEN payment.value > 3 ELSE false END)")
expect where_(
	TranslateTest.describe1(
		orders,
		|o| match o.payment {
			Split(a, b) => a + b > 3
			_ => Bool.False
		},
	),
) == Ok("(IF payment.kind = 'Split' THEN (payment._0 + payment._1) > 3 ELSE false END)")
expect where_(
	TranslateTest.describe1(
		orders,
		|o| match o.payment {
			Invoice({ contact, due }) if due != "" => contact.get().name == "Ada"
			_ => Bool.False
		},
	),
) == Ok("(IF payment.kind = 'Invoice' THEN (IF payment.due = '' THEN false ELSE payment.contact.name = 'Ada' END) ELSE false END)")
expect selected(TranslateTest.describe1(customers, |c| { z: if (c.name == "Ada") "a" else "b" })) == Ok([{ name: "z", surql: "(IF name = 'Ada' THEN 'a' ELSE 'b' END)" }])
expect selected(
	TranslateTest.describe1(
		customers,
		|c| {
			z: match c.address.?zip {
				Ok(z) => "${z}!"
				Err(_) => "none"
			},
		},
	),
) == Ok([{ name: "z", surql: "(IF address.zip IS NONE THEN 'none' ELSE address.zip + '!' END)" }])

# Edges as a relation table's own rows.
expect Translate.render(TranslateTest.describe1(purchases, |e| e.from.get().name != e.to.get().title), [Translate.document("", Bool.True)], Translate.variable) == Ok("in.name != out.title")

# Helpers: one called twice is expanded twice, one that recurses is refused.
expect where_(TranslateTest.describe1(orders, |o| o.items.any(|i| line_total(i) > 4) or o.items.all(|i| line_total(i) < 100))) == Ok("items.any(|$v1| ($v1.qty * 2) > 4) OR items.all(|$v3| ($v3.qty * 2) < 100)")
expect where_(TranslateTest.describe1(orders, |o| depth(o.items.map(|i| i.qty).sum()) > 2)) == Err(Unsupported("a function that calls itself has no SurrealQL form"))

# Field paths for the schema builder.
expect Translate.path_of(TranslateTest.describe1(orders, |o| o.items.map(|i| i.qty))).map_ok(Translate.spell) == Ok("items[*].qty")
expect Translate.path_of(TranslateTest.describe1(customers, |c| c.address.?zip)).map_ok(Translate.spell) == Ok("address.zip")
expect Translate.paths_of(TranslateTest.describe1(customers, |c| { a: c.name, b: c.address.city })).map_ok(|ps| ps.map(Translate.spell)) == Ok(["name", "address.city"])
expect Translate.path_of(TranslateTest.describe1(orders, |o| o.customer.get().name)) == Err(Unsupported("a field path reads fields only; this one calls `Surreal.Link.get`"))

# Captured values.
expect Translate.captured(Named("Surreal.Id", Record([{ name: "key", ty: Str, presence: Required }, { name: "phantom", ty: ListOf(Str), presence: Required }, { name: "table", ty: Str, presence: Required }])), Wrap(Record([Str("ada"), List([]), Str("customer")]))).map_ok(Ql.literal) == Ok("customer:⟨ada⟩")
expect Translate.captured(Dec, Dec(2.5)).map_ok(Ql.literal) == Ok("2.5dec")

# More list operations, a union inside a closure, and records the clause builds.
Kinded : { id : Str, kinds : List([Big(I64), Small]) }

kinded : List(Kinded)
kinded = []

expect where_(
	TranslateTest.describe1(
		kinded,
		|k| k.kinds.any(
			|x| match x {
				Big(n) => n > 5
				Small => Bool.False
			},
		),
	),
) == Ok("kinds.any(|$v1| (IF $v1.kind = 'Big' THEN $v1.value > 5 ELSE false END))")
expect where_(TranslateTest.describe1(orders, |o| o.items.drop_if(|i| i.qty > 1).len() > 0)) == Ok("items.filter(|$v1| !($v1.qty > 1)).len() > 0")
expect where_(TranslateTest.describe1(orders, |o| o.items.count_if(|i| i.qty > 1) > 0)) == Ok("items.filter(|$v1| $v1.qty > 1).len() > 0")
expect where_(TranslateTest.describe1(customers, |c| ["Paris", "Rome"].contains(c.address.city))) == Ok("['Paris', 'Rome'] CONTAINS address.city")
expect where_(
	TranslateTest.describe1(
		orders,
		|o| match o.payment {
			Invoice(i) => i.contact.id() == ada_id
			_ => Bool.False
		},
	),
) == Ok("(IF payment.kind = 'Invoice' THEN payment.contact = customer:⟨ada⟩ ELSE false END)")
expect selected(TranslateTest.describe1(customers, |c| { place: { town: c.address.city }, first: c.born <= new_year })) == Ok([{ name: "first", surql: "born <= d'2020-01-01T00:00:00Z'" }, { name: "place", surql: "{ town: address.city }" }])
expect {
	graph = TranslateTest.describe_group([""], orders, |_, rows| { big: rows.keep_if(|o| o.total > 10).len() })
	Translate.columns(graph, [Translate.Binding.Expr("k"), Translate.Binding.Group(row)], Translate.variable) == Ok([{ name: "big", surql: "count(total > 10.0dec)" }])
}
expect Translate.render(TranslateTest.describe1(orders, |o| o.total > 1), [Translate.document("$after", Bool.False)], Translate.variable) == Ok("$after.total > 1.0dec")
expect Translate.render(TranslateTest.describe1(["x"], |s| s.contains("@")), [Translate.at("$value", Str)], Translate.variable) == Ok("string::contains($value, '@')")
expect where_(TranslateTest.describe1(orders, |o| o.items.any(|i| i.qty < 0) and o.items.len() > 3 and o.total != 0)) == Ok("items.any(|$v1| $v1.qty < 0) AND (items.len() > 3) AND (total != 0.0dec)")

# A captured `Id(Customer)` is refused: its phantom list carries `Customer`,
# whose `zip` is optional. An `Id(Product)` binds.
at_least : Dec, Surreal.Id(Product) -> Code.Bound(Try(Str, Ql.Error))
at_least = |min, pen| TranslateTest.describe_bound(orders, |o| o.total >= min and o.items.any(|i| i.product.id() == pen))

expect {
	bound = at_least(5, Surreal.Id.({ table: "product", key: "pen", phantom: [] }))
	bound.value() == Ok("(total >= $_1) AND items.any(|$v1| $v1.product = $_2)") and bound.inputs().len() == 2
}
expect where_(TranslateTest.describe1(customers, |c| c.born > new_year)) == Ok("born > d'2020-01-01T00:00:00Z'")
# A constant read twice is a kept definition, so it stays where the normal
# form puts it, on the left.
expect where_(TranslateTest.describe1(customers, |c| c.born > new_year and c.born >= new_year)) == Ok("(d'2020-01-01T00:00:00Z' < born) AND (d'2020-01-01T00:00:00Z' <= born)")

# Builtins on `Str`. The ASCII case change works per character, because `string::uppercase` also changes letters outside ASCII.
upper : Str -> Str
upper = |x| "array::join(string::split(${x}, '').map(|$ch| IF $ch >= 'a' AND $ch <= 'z' THEN string::uppercase($ch) ELSE $ch END), '')"

lower : Str -> Str
lower = |x| "array::join(string::split(${x}, '').map(|$ch| IF $ch >= 'A' AND $ch <= 'Z' THEN string::lowercase($ch) ELSE $ch END), '')"

expect where_(TranslateTest.describe1(samples, |s| s.text.with_ascii_uppercased() == "ADA")) == Ok("${upper("text")} = 'ADA'")
expect where_(TranslateTest.describe1(samples, |s| s.text.with_ascii_lowercased() == "ada")) == Ok("${lower("text")} = 'ada'")
expect where_(TranslateTest.describe1(samples, |s| s.text.caseless_ascii_equals(s.other))) == Ok("${lower("text")} = ${lower("other")}")
expect where_(TranslateTest.describe1(samples, |s| s.text.trim() == "x")) == Ok("string::replace(text, /^[\\s\\u{200E}\\u{200F}]+|[\\s\\u{200E}\\u{200F}]+$/, '') = 'x'")
expect where_(TranslateTest.describe1(samples, |s| s.text.trim_start() == "x")) == Ok("string::replace(text, /^[\\s\\u{200E}\\u{200F}]+/, '') = 'x'")
expect where_(TranslateTest.describe1(samples, |s| s.text.trim_end() == "x")) == Ok("string::replace(text, /[\\s\\u{200E}\\u{200F}]+$/, '') = 'x'")
expect where_(TranslateTest.describe1(samples, |s| s.text.repeat(2) == "xx")) == Ok("string::repeat(text, 2) = 'xx'")
expect where_(TranslateTest.describe1(samples, |s| s.text.with_prefix("a") == "ax")) == Ok("('a' + text) = 'ax'")
expect where_(TranslateTest.describe1(samples, |s| s.text.drop_prefix("a") == "x")) == Ok("(IF string::starts_with(text, 'a') THEN string::slice(text, string::len('a')) ELSE text END) = 'x'")
expect where_(TranslateTest.describe1(samples, |s| s.text.drop_suffix("a") == "x")) == Ok("(IF string::ends_with(text, 'a') THEN string::slice(text, 0, string::len(text) - string::len('a')) ELSE text END) = 'x'")
expect where_(TranslateTest.describe1(samples, |s| s.text.split_on(",").len() == 2)) == Ok("string::split(text, ',').len() = 2")
expect where_(TranslateTest.describe1(samples, |s| s.text.split_on("").len() == 1)) == Ok("[text].len() = 1")
expect where_(TranslateTest.describe1(samples, |s| s.text.split_on(s.other).len() == 2)) == Ok("(IF other = '' THEN [text] ELSE string::split(text, other) END).len() = 2")
expect where_(TranslateTest.describe1(samples, |s| Str.join_with(s.words, ",") == "a,b")) == Ok("array::join(words, ',') = 'a,b'")
expect where_(TranslateTest.describe1(samples, |s| s.text.replace_each("a", "b") == "x")) == Ok("string::replace(text, 'a', 'b') = 'x'")
expect where_(TranslateTest.describe1(samples, |s| s.text.replace_each("", "b") == "x")) == Ok("text = 'x'")
expect where_(TranslateTest.describe1(samples, |s| s.text.replace_each(s.other, "b") == "x")) == Ok("(IF other = '' THEN text ELSE string::replace(text, other, 'b') END) = 'x'")
expect where_(TranslateTest.describe1(samples, |s| s.text.count_utf8_bytes() > 3)) == Ok("bytes::len(<bytes>text) > 3")
expect where_(TranslateTest.describe1(samples, |s| s.text.to_str() == "x")) == Ok("text = 'x'")
expect where_(TranslateTest.describe1(samples, |s| I64.from_str(s.text).is_ok())) == Err(Unsupported("`from_str` accepts more forms than SurrealDB casts; parse in Roc and store a number"))
expect where_(TranslateTest.describe1(samples, |s| s.text.split_first(",").is_ok())) == Err(Unsupported("`Str.split_first` has no SurrealQL form"))

# Builtins on integers and `Dec`.
expect where_(TranslateTest.describe1(samples, |s| s.n.max(3) > 3)) == Ok("math::max([n, 3]) > 3")
expect where_(TranslateTest.describe1(samples, |s| s.n.min(s.m) > 3)) == Ok("math::min([n, m]) > 3")
expect where_(TranslateTest.describe1(samples, |s| s.f.max(1) > 0)) == Err(Unsupported("`max` on `Num.F64` differs from SurrealDB for NaN, -0.0 and how a float prints; use `Dec` or an integer"))
expect where_(TranslateTest.describe1(samples, |s| s.n.pow(2) > 3)) == Ok("math::pow(n, 2) > 3")
expect where_(TranslateTest.describe1(samples, |s| s.d.pow(2) > 3)) == Err(Unsupported("`pow` on `Dec` keeps 18 digits in Roc and 28 in SurrealDB; the two differ"))
expect where_(TranslateTest.describe1(samples, |s| s.n.mod_by(3) == 1)) == Ok("(((n % 3) + 3) % 3) = 1")
expect where_(TranslateTest.describe1(samples, |s| s.n.is_multiple_of(3))) == Ok("n % 3 = 0")
expect where_(TranslateTest.describe1(samples, |s| s.n.is_multiple_of(s.m))) == Ok("(IF m = 0 THEN n = 0 ELSE n % m = 0 END)")
expect where_(TranslateTest.describe1(samples, |s| s.n.is_multiple_of(0))) == Ok("(IF 0 = 0 THEN n = 0 ELSE n % 0 = 0 END)")
expect where_(TranslateTest.describe1(samples, |s| s.n.is_zero())) == Ok("n = 0")
expect where_(TranslateTest.describe1(samples, |s| s.n.is_negative())) == Ok("n < 0")
expect where_(TranslateTest.describe1(samples, |s| s.n.is_positive())) == Ok("n > 0")
expect where_(TranslateTest.describe1(samples, |s| s.d.is_negative())) == Ok("d < 0")
expect where_(TranslateTest.describe1(samples, |s| s.f.is_zero())) == Err(Unsupported("`is_zero` on `Num.F64` differs from SurrealDB for NaN, -0.0 and how a float prints; use `Dec` or an integer"))
expect where_(TranslateTest.describe1(samples, |s| s.n.is_even())) == Ok("n % 2 = 0")
expect where_(TranslateTest.describe1(samples, |s| s.n.is_odd())) == Ok("n % 2 != 0")
expect where_(TranslateTest.describe1(samples, |s| s.n.to_str() == "3")) == Ok("<string>n = '3'")
expect where_(TranslateTest.describe1(samples, |s| s.d.to_str() == "3")) == Err(Unsupported("`to_str` on `Dec` prints differently: Roc `3.0`, SurrealDB `3`; compare the number"))
expect where_(TranslateTest.describe1(samples, |s| s.d.round() == 3)) == Ok("(IF d >= 0 THEN math::floor(d + 0.5dec) ELSE math::ceil(d - 0.5dec) END) = 3.0dec")
expect where_(TranslateTest.describe1(samples, |s| s.d.floor() == 1)) == Ok("math::floor(d) = 1.0dec")
expect where_(TranslateTest.describe1(samples, |s| s.d.ceiling() == 1)) == Ok("math::ceil(d) = 1.0dec")
expect where_(TranslateTest.describe1(samples, |s| s.d.trunc() == 1)) == Ok("(IF d >= 0 THEN math::floor(d) ELSE math::ceil(d) END) = 1.0dec")

# Conversions between numbers. A conversion of a `Dec` that cuts a fraction is refused.
expect where_(TranslateTest.describe1(samples, |s| s.n.to_i128() > 1)) == Ok("n > 1")
expect where_(TranslateTest.describe1(samples, |s| s.n.to_i64_wrap() > 3)) == Ok("n > 3")
expect where_(TranslateTest.describe1(samples, |s| s.d.to_i64_wrap() > 3)) == Err(Unsupported("`to_i64_wrap` on `Num.Dec` cuts the fraction, and SurrealDB's `<int>` raises an error on one; use `to_i64_try`"))
expect where_(TranslateTest.describe1(samples, |s| s.f.to_i64_wrap() > 3)) == Err(Unsupported("`to_i64_wrap` on `Num.F64` cuts the fraction, and SurrealDB's `<int>` raises an error on one; use `to_i64_try`"))
expect where_(TranslateTest.describe1(samples, |s| s.n.to_u8_try().is_ok())) == Ok("(IF n >= 0 AND n <= 255 THEN n ELSE NONE END) IS NOT NONE")
expect where_(TranslateTest.describe1(samples, |s| s.n.to_i32_try().is_ok())) == Ok("(IF n >= -2147483648 AND n <= 2147483647 THEN n ELSE NONE END) IS NOT NONE")
expect where_(TranslateTest.describe1(samples, |s| s.n.to_u64_try().is_ok())) == Ok("(IF n >= 0 THEN n ELSE NONE END) IS NOT NONE")
expect where_(TranslateTest.describe1(samples, |s| s.n.to_i128().to_i64_try().is_ok())) == Ok("n IS NOT NONE")
expect where_(TranslateTest.describe1(samples, |s| (s.n.to_u8_try() ?? 0) > 1)) == Ok("((IF n >= 0 AND n <= 255 THEN n ELSE NONE END) ?? 0) > 1")
expect where_(TranslateTest.describe1(samples, |s| s.d.to_i64_try().is_ok())) == Ok("(IF d > -9223372036854775809dec AND d < 9223372036854775808dec THEN <int>(IF d >= 0 THEN math::floor(d) ELSE math::ceil(d) END) ELSE NONE END) IS NOT NONE")

# `Try` and `List` builtins. A `Try` is `NONE` when it is an `Err`.
expect where_(TranslateTest.describe1(samples, |s| s.?opt.ok_or("x") == "y")) == Ok("(opt ?? 'x') = 'y'")
expect where_(TranslateTest.describe1(samples, |s| s.nums.first().ok_or(0) > 1)) == Ok("(array::first(nums) ?? 0) > 1")
expect where_(TranslateTest.describe1(samples, |s| s.nums.last().is_ok())) == Ok("array::last(nums) IS NOT NONE")
expect where_(TranslateTest.describe1(samples, |s| s.nums.get(1).is_ok())) == Ok("array::at(nums, 1) IS NOT NONE")
expect where_(TranslateTest.describe1(samples, |s| s.nums.max().is_err())) == Ok("array::max(nums) IS NONE")
expect where_(TranslateTest.describe1(samples, |s| s.nums.min().is_ok())) == Ok("array::min(nums) IS NOT NONE")
expect where_(
	TranslateTest.describe1(
		samples,
		|s| match s.nums.first() {
			Ok(x) => x > 1
			Err(_) => Bool.False
		},
	),
) == Ok("(IF array::first(nums) IS NONE THEN false ELSE array::first(nums) > 1 END)")
expect where_(TranslateTest.describe1(samples, |s| s.nums.take_first(2).len() == 2)) == Ok("array::slice(nums, 0, 2).len() = 2")
expect where_(TranslateTest.describe1(samples, |s| s.nums.drop_first(2).len() == 1)) == Ok("array::slice(nums, 2).len() = 1")
expect where_(TranslateTest.describe1(samples, |s| s.nums.concat(s.nums).len() > 1)) == Ok("array::concat(nums, nums).len() > 1")
expect where_(TranslateTest.describe1(samples, |s| s.nums.append(1).len() > 1)) == Ok("array::append(nums, 1).len() > 1")
expect where_(TranslateTest.describe1(samples, |s| s.nums.prepend(1).len() > 1)) == Ok("array::prepend(nums, 1).len() > 1")
expect where_(TranslateTest.describe1(samples, |s| s.nums.rev().len() > 1)) == Ok("array::reverse(nums).len() > 1")
expect where_(TranslateTest.describe1(samples, |s| s.grid.join().len() > 1)) == Ok("array::flatten(grid).len() > 1")
expect where_(TranslateTest.describe1(samples, |s| s.nums == [1, 2])) == Ok("nums = [1, 2]")
# The edges of a relation keep their kind through `rev`, and give no single element.
expect {
	graph = TranslateTest.describe_pair(customers, purchases, |(_, bought)| { titles: bought.rev().map(|e| e.to.get().title) })
	Translate.columns(graph, [Translate.Binding.Pair(row, Translate.outgoing("purchased"))], Translate.variable) == Ok([{ name: "titles", surql: "array::reverse(->purchased).map(|$v1| $v1.out.title)" }])
}
expect {
	graph = TranslateTest.describe_pair(customers, purchases, |(_, bought)| { first: bought.first().is_ok() })
	Translate.columns(graph, [Translate.Binding.Pair(row, Translate.outgoing("purchased"))], Translate.variable) == Err(Unsupported("the edges of a relation take `keep_if`, `map`, `any`, `all` and `len`"))
}

# The functions of `Surreal.Text`: one SurrealQL function of the same arguments.
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_email(s.text))) == Ok("string::is_email(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_url(s.text))) == Ok("string::is_url(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_domain(s.text))) == Ok("string::is_domain(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_ip(s.text))) == Ok("string::is_ip(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_ipv4(s.text))) == Ok("string::is_ipv4(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_ipv6(s.text))) == Ok("string::is_ipv6(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_uuid(s.text))) == Ok("string::is_uuid(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_ulid(s.text))) == Ok("string::is_ulid(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_semver(s.text))) == Ok("string::is_semver(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_alpha(s.text))) == Ok("string::is_alpha(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_alphanum(s.text))) == Ok("string::is_alphanum(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_numeric(s.text))) == Ok("string::is_numeric(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_latitude(s.text))) == Ok("string::is_latitude(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_longitude(s.text))) == Ok("string::is_longitude(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_ascii(s.text))) == Ok("string::is_ascii(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_hexadecimal(s.text))) == Ok("string::is_hexadecimal(text)")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.is_datetime(s.text, "%Y"))) == Ok("string::is_datetime(text, '%Y')")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.matches(s.text, "^a"))) == Ok("string::matches(text, '^a')")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.similarity_jaro(s.text, s.other) > 0.8)) == Ok("string::similarity::jaro(text, other) > 0.8f")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.similarity_jaro_winkler(s.text, s.other) > 0.8)) == Ok("string::similarity::jaro_winkler(text, other) > 0.8f")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.distance_levenshtein(s.text, s.other) < 2)) == Ok("string::distance::levenshtein(text, other) < 2")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.distance_damerau_levenshtein(s.text, s.other) < 2)) == Ok("string::distance::damerau_levenshtein(text, other) < 2")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Text.distance_normalized_levenshtein(s.text, s.other) < 0.5)) == Ok("string::distance::normalized_levenshtein(text, other) < 0.5f")

# The hashes of `Surreal.Hash`, and the table of an id.
expect where_(TranslateTest.describe1(samples, |s| Surreal.Hash.sha256(s.text) == "x")) == Ok("crypto::sha256(text) = 'x'")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Hash.blake3(s.text) == "x")) == Ok("crypto::blake3(text) = 'x'")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Hash.md5(s.text) == "x")) == Ok("crypto::md5(text) = 'x'")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Hash.sha1(s.text) == "x")) == Ok("crypto::sha1(text) = 'x'")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Hash.sha512(s.text) == "x")) == Ok("crypto::sha512(text) = 'x'")
expect where_(TranslateTest.describe1(orders, |o| Surreal.Id.table(o.customer.id()) == "customer")) == Ok("record::tb(customer) = 'customer'")

# The functions of `Surreal.Array`.
expect where_(TranslateTest.describe1(samples, |s| Surreal.Array.distinct(s.nums).len() > 1)) == Ok("array::distinct(nums).len() > 1")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Array.union(s.nums, s.nums).len() > 1)) == Ok("array::union(nums, nums).len() > 1")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Array.intersect(s.nums, s.nums).len() > 1)) == Ok("array::intersect(nums, nums).len() > 1")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Array.complement(s.nums, s.nums).len() > 1)) == Ok("array::complement(nums, nums).len() > 1")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Array.distinct(s.words).contains("a"))) == Ok("array::distinct(words) CONTAINS 'a'")

# The functions of `Surreal.Time`. A duration is built in the clause.
expect where_(TranslateTest.describe1(samples, |s| s.at < Surreal.Time.now())) == Ok("at < time::now()")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.floor(s.at, Surreal.Time.hours(1)) < s.at)) == Ok("time::floor(at, duration::from_nanos(3600000000000)) < at")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.ceil(s.at, Surreal.Time.hours(1)) < s.at)) == Ok("time::ceil(at, duration::from_nanos(3600000000000)) < at")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.round(s.at, Surreal.Time.hours(1)) < s.at)) == Ok("time::round(at, duration::from_nanos(3600000000000)) < at")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.floor(s.at, Surreal.Time.mins(90)) < s.at)) == Ok("time::floor(at, duration::from_nanos(5400000000000)) < at")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.floor(s.at, Surreal.Time.nanos(7)) < s.at)) == Ok("time::floor(at, duration::from_nanos(7)) < at")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.floor(s.at, Surreal.Time.weeks(1)) < s.at)) == Ok("time::floor(at, duration::from_nanos(604800000000000)) < at")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.floor(s.at, Surreal.Time.hours(s.nums.len())) < s.at)) == Ok("time::floor(at, duration::from_nanos(nums.len() * 3600000000000)) < at")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.group(s.at, Year) < s.at)) == Ok("time::group(at, 'year') < at")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.group(s.at, Month) < s.at)) == Ok("time::group(at, 'month') < at")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.group(s.at, Day) < s.at)) == Ok("time::group(at, 'day') < at")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.group(s.at, Hour) < s.at)) == Ok("time::group(at, 'hour') < at")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.group(s.at, Minute) < s.at)) == Ok("time::group(at, 'minute') < at")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.group(s.at, Second) < s.at)) == Ok("time::group(at, 'second') < at")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.plus(s.at, Surreal.Time.days(1)) > s.at)) == Ok("at < (at + duration::from_nanos(86400000000000))")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.minus(s.at, Surreal.Time.days(1)) < s.at)) == Ok("(at - duration::from_nanos(86400000000000)) < at")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.wday(s.at) == 7)) == Ok("time::wday(at) = 7")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.yday(s.at) == 7)) == Ok("time::yday(at) = 7")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.week(s.at) == 7)) == Ok("time::week(at) = 7")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.unix(s.at) == 7)) == Ok("time::unix(at) = 7")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.nano(s.at) == 7)) == Ok("time::nano(at) = 7")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.unix_millis(s.at) == 7)) == Ok("time::millis(at) = 7")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.unix_micros(s.at) == 7)) == Ok("time::micros(at) = 7")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.year(s.at) == 3)) == Ok("time::year(at) = 3")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.month(s.at) == 3)) == Ok("time::month(at) = 3")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.day(s.at) == 3)) == Ok("time::day(at) = 3")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.hour(s.at) == 3)) == Ok("time::hour(at) = 3")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.minute(s.at) == 3)) == Ok("time::minute(at) = 3")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.second(s.at) == 3)) == Ok("time::second(at) = 3")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.format(s.at, "%Y") == "2026")) == Ok("time::format(at, '%Y') = '2026'")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.from_unix(s.n) < s.at)) == Ok("time::from_unix(n) < at")

# The statistics of `Surreal.Math` over a list, and over the rows of a group.
expect where_(TranslateTest.describe1(samples, |s| Surreal.Math.mean(s.scores) > 2.5)) == Ok("math::mean(scores) > 2.5f")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Math.median(s.scores) > 2.5)) == Ok("math::median(scores) > 2.5f")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Math.stddev(s.scores) > 1)) == Ok("math::stddev(scores) > 1f")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Math.variance(s.scores) > 1)) == Ok("math::variance(scores) > 1f")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Math.percentile(s.scores, 90) > 3)) == Ok("math::percentile(scores, 90f) > 3f")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Math.mean(s.nums.map(|n| n.to_f64())) > 2)) == Ok("math::mean(nums.map(|$v1| <float>$v1)) > 2f")
expect {
	graph = TranslateTest.describe_group([""], orders, |_, rows| { avg: Surreal.Math.mean(rows.map(|o| o.total.to_f64())) })
	Translate.columns(graph, [Translate.Binding.Expr("k"), Translate.Binding.Group(row)], Translate.variable) == Ok([{ name: "avg", surql: "math::mean(<float>total)" }])
}
expect {
	graph = TranslateTest.describe_group([""], orders, |_, rows| { mid: Surreal.Math.median(rows.map(|o| o.total.to_f64())) })
	Translate.columns(graph, [Translate.Binding.Expr("k"), Translate.Binding.Group(row)], Translate.variable) == Ok([{ name: "mid", surql: "math::median(<float>total)" }])
}
expect {
	graph = TranslateTest.describe_group([""], orders, |_, rows| { sd: Surreal.Math.stddev(rows.map(|o| o.total.to_f64())) })
	Translate.columns(graph, [Translate.Binding.Expr("k"), Translate.Binding.Group(row)], Translate.variable) == Ok([{ name: "sd", surql: "math::stddev(<float>total)" }])
}
expect {
	graph = TranslateTest.describe_group([""], orders, |_, rows| { spread: Surreal.Math.variance(rows.map(|o| o.total.to_f64())) })
	Translate.columns(graph, [Translate.Binding.Expr("k"), Translate.Binding.Group(row)], Translate.variable) == Ok([{ name: "spread", surql: "math::variance(<float>total)" }])
}
expect {
	graph = TranslateTest.describe_group([""], orders, |_, rows| { p: Surreal.Math.percentile(rows.map(|o| o.total.to_f64()), 90) })
	Translate.columns(graph, [Translate.Binding.Expr("k"), Translate.Binding.Group(row)], Translate.variable) == Err(Unsupported("`math::percentile` is not an aggregate in SurrealDB; use it on a list"))
}

# One `rows.map(f)` read by several aggregates: each aggregate writes its own expression.
expect {
	graph = TranslateTest.describe_group(
		[""],
		orders,
		|_, rows| {
			totals = rows.map(|o| o.total.to_f64())
			{ avg: Surreal.Math.mean(totals), mid: Surreal.Math.median(totals), spread: Surreal.Math.stddev(totals) }
		},
	)
	Translate.columns(graph, [Translate.Binding.Expr("k"), Translate.Binding.Group(row)], Translate.variable)
		== Ok([{ name: "avg", surql: "math::mean(<float>total)" }, { name: "mid", surql: "math::median(<float>total)" }, { name: "spread", surql: "math::stddev(<float>total)" }])
}
expect {
	graph = TranslateTest.describe_group([""], orders, |_, rows| { low: Surreal.Math.mean(rows.map(|o| o.total.to_f64())), high: Surreal.Math.variance(rows.map(|o| o.total.to_f64())) })
	Translate.columns(graph, [Translate.Binding.Expr("k"), Translate.Binding.Group(row)], Translate.variable) == Ok([{ name: "high", surql: "math::variance(<float>total)" }, { name: "low", surql: "math::mean(<float>total)" }])
}
expect {
	graph = TranslateTest.describe_group(
		[""],
		orders,
		|_, rows| {
			totals = rows.map(|o| o.total)
			{ sum: totals.sum(), sum_again: totals.sum() }
		},
	)
	Translate.columns(graph, [Translate.Binding.Expr("k"), Translate.Binding.Group(row)], Translate.variable) == Ok([{ name: "sum", surql: "math::sum(total)" }, { name: "sum_again", surql: "math::sum(total)" }])
}
expect {
	graph = TranslateTest.describe_group(
		[""],
		orders,
		|_, rows| {
			totals = rows.map(|o| o.total.to_f64())
			{ avg: Surreal.Math.mean(totals), p: Surreal.Math.percentile(totals, 90) }
		},
	)
	Translate.columns(graph, [Translate.Binding.Expr("k"), Translate.Binding.Group(row)], Translate.variable) == Err(Unsupported("`math::percentile` is not an aggregate in SurrealDB; use it on a list"))
}
expect {
	graph = TranslateTest.describe_group([""], orders, |_, rows| { n: rows.map(|o| o.total).len() })
	Translate.columns(graph, [Translate.Binding.Expr("k"), Translate.Binding.Group(row)], Translate.variable) == Err(Unsupported("a group's rows take `len`, `keep_if(..).len()` and `map(..).sum()`"))
}

# `Rand` gives a new value on every call. A default, a computed field and an update may use it, a query may not.
random_error : Str -> Try(Str, Ql.Error)
random_error = |name| Err(Unsupported("`${name}` gives a new value on every call: use it in a default, a computed field or an update"))

random_text : Code.Graph -> Try(Str, Ql.Error)
random_text = |graph| Translate.row_value(graph, [row], Translate.variable)

salted : Sample -> Str
salted = |s| s.text.concat(Surreal.Rand.int(1, s.n).to_str())

expect where_(TranslateTest.describe1(samples, |s| Surreal.Rand.int(1, 6) > s.n)) == random_error("Surreal.Rand.int")
expect where_(TranslateTest.describe1(samples, |s| salted(s) == s.text)) == random_error("Surreal.Rand.int")
expect where_(TranslateTest.describe1(samples, |s| s.words.any(|w| w == Surreal.Rand.uuid()))) == random_error("Surreal.Rand.uuid")
expect selected(TranslateTest.describe1(samples, |_s| { r: Surreal.Rand.ulid() })) == Err(Unsupported("`Surreal.Rand.ulid` gives a new value on every call: use it in a default, a computed field or an update"))
expect random_text(TranslateTest.describe1(samples, |_s| Surreal.Rand.ulid())) == Ok("rand::ulid()")
expect random_text(TranslateTest.describe1(samples, |_s| Surreal.Rand.uuid())) == Ok("<string>rand::uuid()")
expect random_text(TranslateTest.describe1(samples, |s| Surreal.Rand.int(1, s.n))) == Ok("rand::int(1, n)")
expect random_text(TranslateTest.describe1(samples, |s| salted(s))) == Ok("text + <string>rand::int(1, n)")
expect Translate.assignments(TranslateTest.describe1(customers, |c| { ..c, name: Surreal.Rand.ulid() }), [row], Translate.variable) == Ok([{ name: "name", surql: "rand::ulid()" }])

# `==` on datetimes compares the datetimes, also when one is a function result, is read twice or is a parameter.
# SurrealDB prints a fraction with 3, 6 or 9 digits and Roc without trailing zeros, so their texts differ.
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.floor(s.at, Surreal.Time.hours(1)) == new_year)) == Ok("time::floor(at, duration::from_nanos(3600000000000)) = d'2020-01-01T00:00:00Z'")
expect where_(TranslateTest.describe1(samples, |s| Surreal.Time.floor(s.at, Surreal.Time.hours(1)) == s.at)) == Ok("time::floor(at, duration::from_nanos(3600000000000)) = at")
expect where_(TranslateTest.describe1(samples, |s| new_year == Surreal.Time.floor(s.at, Surreal.Time.hours(1)))) == Ok("time::floor(at, duration::from_nanos(3600000000000)) = d'2020-01-01T00:00:00Z'")
expect where_(TranslateTest.describe1(samples, |s| same(s.at, hour_of(s)))) == Ok("at = time::floor(at, duration::from_nanos(3600000000000))")
expect where_(TranslateTest.describe1(samples, |s| s.times.any(|t| t == s.at))) == Ok("times.any(|$v1| $v1 = at)")
expect where_(TranslateTest.describe1(samples, |s| s.at == half_second)) == Ok("at = d'2026-03-04T05:06:07.5Z'")
expect where_(TranslateTest.describe1(samples, |s| s.at != new_year)) == Ok("at != d'2020-01-01T00:00:00Z'")
expect where_(TranslateTest.describe1(samples, |s| new_year != s.at)) == Ok("at != d'2020-01-01T00:00:00Z'")
expect where_(TranslateTest.describe1(samples, |s| s.times.any(|t| t != s.at))) == Ok("times.any(|$v1| $v1 != at)")
expect where_(TranslateTest.describe1(samples, |s| iso_of(s.at) == s.text)) == Err(Unsupported("the text of a datetime is compared with a datetime or a literal; SurrealDB prints a fraction with 3, 6 or 9 digits, so other texts differ"))
expect where_(TranslateTest.describe1(samples, |s| s.text == iso_of(s.at))) == Err(Unsupported("the text of a datetime is compared with a datetime or a literal; SurrealDB prints a fraction with 3, 6 or 9 digits, so other texts differ"))

# A `Duration` cannot be a captured value. A table with one has no column for it (see `TypesTest.roc`).
sample_table : Surreal.Table(Sample)
sample_table = Surreal.table("sample", |s| s)

floor_by : Surreal.Duration -> Try(Surreal.Statement, Ql.Error)
floor_by = |span| Surreal.bind_captured(Surreal.select_where(sample_table, |s| Surreal.Time.floor(s.at, span) < s.at))

expect floor_by(Surreal.Time.hours(1)).map_ok(|_| "bound") == Err(Unsupported("a captured `Duration` has no SurrealQL value; build it in the clause, as `Time.hours(1)`"))

# The mirrors run in Roc. Each value below is what SurrealDB 3.3.4 gives for the same input.
moment : Str -> Surreal.Datetime
moment = |text| match Surreal.datetime(text) {
	Ok(d) => d
	Err(_) => crash "a valid datetime"
}

expect ["", "abé", "a\nb", "😀", "A", "\u(7f)"].map(Surreal.Text.is_ascii) == [Bool.False, Bool.False, Bool.True, Bool.False, Bool.True, Bool.True]
expect ["", "FF0a", "0xff", "g", "ＦＦ", "abcdefABCDEF", "٣", "9a"].map(Surreal.Text.is_hexadecimal) == [Bool.False, Bool.True, Bool.False, Bool.False, Bool.False, Bool.True, Bool.False, Bool.True]
expect Surreal.Hash.sha256("") == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
expect Surreal.Hash.sha256("abc") == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
expect Surreal.Hash.sha256("é") == "4a99557e4033c3539de2eb65472017cad5f9557f7a0625a09f1c3f6e2ba69c4c"
expect Surreal.Hash.sha256("😀") == "f0443a342c5ef54783a111b51ba56c938e474c32324d90c3a60c9c8e3a37e2d9"
expect Surreal.Hash.sha256(Str.repeat("a", 1000)) == "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"
expect Surreal.Hash.blake3("") == "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
expect Surreal.Hash.blake3("abc") == "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85"
expect Surreal.Hash.blake3("é") == "46d0ec742ceaad149f9a3d109d1bd9e9ece7858161b43cf0008906478418e807"
expect Surreal.Hash.blake3("😀") == "728105475d1a9e2f0164862a43e44bea39fa5d8b73d484f9137b8ae65a66dd7a"
expect Surreal.Hash.blake3(Str.repeat("a", 1000)) == "9957a9014733dd6b6e2f6abcbe7b259a6da1aa0b0e184cd7bf1810e5c425f405"
expect Surreal.Id.table(ada_id) == "customer"

expect Surreal.Array.distinct([3.I64, 1, 3, 2, 1]) == [3, 1, 2]
expect Surreal.Array.distinct(List.repeat(1.I64, 0)) == []
expect Surreal.Array.distinct(["b", "a", "b", "é"]) == ["b", "a", "é"]
expect Surreal.Array.distinct([[1.I64], [1], [2, 3]]) == [[1], [2, 3]]
expect Surreal.Array.distinct([1.5.F64, 1.5, 0.0, -0.0, 0.0]) == [1.5, 0.0]
expect Surreal.Array.union([3.I64, 1], [2, 3, 1]) == [3, 1, 2]
expect Surreal.Array.union([1.I64, 1, 2], [2, 3, 3]) == [1, 2, 3]
expect Surreal.Array.union(["b", "a", "b", "é"], ["é", "c"]) == ["b", "a", "é", "c"]
expect Surreal.Array.union(List.repeat(1.I64, 0), [1]) == [1]
expect Surreal.Array.intersect([3.I64, 1, 3, 2, 1], [2, 3]) == [3, 2]
expect Surreal.Array.intersect([1.I64, 1, 2], [1, 2, 2]) == [1, 2]
expect Surreal.Array.intersect([1.I64, 1, 2], [2, 3, 3]) == [2]
expect Surreal.Array.intersect([1.I64, 2], List.repeat(1, 0)) == []
expect Surreal.Array.intersect(["b", "a", "b", "é"], ["é", "c"]) == ["é"]
expect Surreal.Array.complement([3.I64, 1, 2, 3], [2]) == [3, 1, 3]
expect Surreal.Array.complement([3.I64, 1, 3, 2, 1], [2, 3]) == [1, 1]
expect Surreal.Array.complement([1.I64, 1, 2], [2, 3, 3]) == [1, 1]
expect Surreal.Array.complement([1.I64, 1], [1]) == []
expect Surreal.Array.complement(["b", "a", "b", "é"], ["é", "c"]) == ["b", "a", "b"]
expect Surreal.Array.complement([1.5.F64, 0.0, -0.0], [0.0]) == [1.5]

expect {
	parts = |d| [Surreal.Time.year(d), Surreal.Time.month(d), Surreal.Time.day(d), Surreal.Time.hour(d), Surreal.Time.minute(d), Surreal.Time.second(d)]
	parts(moment("2026-03-04T05:06:07Z")) == [2026, 3, 4, 5, 6, 7] and parts(moment("2026-03-04T05:06:07.5Z")) == [2026, 3, 4, 5, 6, 7] and parts(moment("0000-01-01T00:00:00Z")) == [0, 1, 1, 0, 0, 0] and parts(moment("2024-02-29T23:59:59.999999999Z")) == [2024, 2, 29, 23, 59, 59] and parts(moment("9999-12-31T23:59:59Z")) == [9999, 12, 31, 23, 59, 59]
}
expect Surreal.Time.hours(1) == Surreal.Duration.({ nanos: 3600000000000 })
expect Surreal.Time.weeks(2) == Surreal.Duration.({ nanos: 1209600000000000 })
expect Surreal.Time.nanos(5) == Surreal.Duration.({ nanos: 5 })

expect Surreal.Math.mean([1.0, 2.0, 3.0, 4.0]) == 2.5
expect Surreal.Math.mean([0.1, 0.2, 0.3]) == 0.20000000000000004
expect Surreal.Math.mean([0.1, 0.7, 0.2, 0.4, 0.9]) == 0.45999999999999996
expect Surreal.Math.mean([1e16, 1.0, -1e16]) == 0.0
expect Surreal.Math.mean([5.0]) == 5.0
expect Surreal.Math.mean([1e308, 1e308]).is_infinite()
expect Surreal.Math.mean(List.repeat(1.0, 0)).is_nan()

# The nanoseconds since 1970 of `time::nano`, both ways.
expect moment("2026-03-04T05:06:07.123456789Z").to_unix_nanos() == 1772600767123456789
expect moment("1970-01-01T00:00:00Z").to_unix_nanos() == 0
expect moment("1969-12-31T23:59:59.5Z").to_unix_nanos() == -500000000
expect moment("2024-02-29T12:00:00.000000001Z").to_unix_nanos() == 1709208000000000001
expect moment("1900-03-01T00:00:00Z").to_unix_nanos() == -2203891200000000000
expect moment("2100-12-31T23:59:59.1Z").to_unix_nanos() == 4133980799100000000
expect Surreal.Datetime.from_unix_nanos(1772600767123456789) == Ok(moment("2026-03-04T05:06:07.123456789Z"))
expect Surreal.Datetime.from_unix_nanos(-1500000000) == Ok(moment("1969-12-31T23:59:58.5Z"))
expect Surreal.Datetime.from_unix_nanos(951868799000000000) == Ok(moment("2000-02-29T23:59:59Z"))
expect Surreal.Datetime.from_unix_nanos(-8000000000000000000) == Ok(moment("1716-06-28T09:46:40Z"))
expect Surreal.Datetime.from_unix_nanos(moment("0000-01-01T00:00:00Z").to_unix_nanos()) == Ok(moment("0000-01-01T00:00:00Z"))
expect Surreal.Datetime.from_unix_nanos(moment("9999-12-31T23:59:59.999999999Z").to_unix_nanos()) == Ok(moment("9999-12-31T23:59:59.999999999Z"))
expect Surreal.Datetime.from_unix_nanos(moment("9999-12-31T23:59:59.999999999Z").to_unix_nanos() + 1) == Err(BadDatetime)
expect Surreal.Datetime.from_unix_nanos(moment("0000-01-01T00:00:00Z").to_unix_nanos() - 1) == Err(BadDatetime)
expect ["0000-02-29T00:00:00Z", "0000-03-01T00:00:00Z", "1600-02-29T23:59:59.000001Z", "1899-12-31T23:59:59Z", "1969-12-31T23:59:59.999999999Z", "2000-03-01T00:00:00Z", "2038-01-19T03:14:07Z", "9999-01-31T10:20:30.5Z"].all(|text| Surreal.Datetime.from_unix_nanos(moment(text).to_unix_nanos()) == Ok(moment(text)))
