import Ql
import Surreal

# Tests of the queries and writes of `Surreal` on a small domain, one for
# each kind of query and write. Nothing outside this file imports it.
QueriesTest :: {}

Address : { city : Str, zip ?: Str }

Customer : { id : Str, name : Str, address : Address, tags : List(Str) }

Product : { id : Str, title : Str, price : Dec }

Item : { product : Surreal.Link(Product), qty : I64 }

Payment : [Card({ last4 : Str }), Cash]

Order : { id : Str, customer : Surreal.Link(Customer), items : List(Item), payment : Payment, total : Dec }

Purchased : { id : Str, from : Surreal.Link(Customer), to : Surreal.Link(Product), quantity : I64 }

customers : Surreal.Table(Customer)
customers = Surreal.table("customer", |c| c)

products : Surreal.Table(Product)
products = Surreal.table("product", |p| p)

orders : Surreal.Table(Order)
orders = Surreal.table("order", |o| o)

purchased : Surreal.Table(Purchased)
purchased = Surreal.relation("purchased", customers, products, |e| e)

pen_id : Surreal.Id(Product)
pen_id = Surreal.id_of("product", "pen")

Params : { min_total : Dec }

# ------------------------------------------------------------- queries

expect Surreal.from(orders).filter(|o| o.customer.get().address.city == "Paris").select_all().to_surql() == Ok("SELECT * FROM order WHERE customer.address.city = 'Paris'")
expect Surreal.from(orders).filter(|o| o.items.any(|i| i.qty > 3)).select_all().to_surql() == Ok("SELECT * FROM order WHERE items.any(|$v1| $v1.qty > 3)")
expect Surreal.from(orders).filter(|o| o.items.any(|i| i.qty > 3)).filter(|o| o.total > 10).select_all().to_surql() == Ok("SELECT * FROM order WHERE (items.any(|$v1| $v1.qty > 3)) AND (total > 10.0dec)")
expect Surreal.from(orders).filter(|o| o.items.any(|i| i.product.id() == pen_id)).select_all().to_surql() == Ok("SELECT * FROM order WHERE items.any(|$v1| $v1.product = product:⟨pen⟩)")
expect Surreal.from(orders).select(|o| { who: o.customer.get().name, n: o.items.len() }).to_surql() == Ok("SELECT items.len() AS n, customer.name AS who FROM order")
expect Surreal.from(orders).select(|o| { customer: o.customer.get(), total: o.total }).to_surql() == Ok("SELECT customer.* AS customer, total AS total FROM order")
expect Surreal.from(orders).fetch(|o| o.customer).select_all().to_surql() == Ok("SELECT * FROM order FETCH customer")
expect Surreal.from(customers).select(|c| { note: c.address.?zip ?? "-" }).to_surql() == Ok("SELECT address.zip ?? '-' AS note FROM customer")
expect Surreal.from(orders).fetch_each(|o| o.items.map(|i| i.product)).select_all().to_surql() == Ok("SELECT * FROM order FETCH items[*].product")
expect Surreal.from(orders).fetch(|o| o.customer).fetch_each(|o| o.items.map(|i| i.product)).select_all().to_surql() == Ok("SELECT * FROM order FETCH customer, items[*].product")
expect Surreal.from(customers).outgoing(purchased).select(|(c, bought)| { name: c.name, titles: bought.keep_if(|e| e.quantity > 2).map(|e| e.to.get().title) }).to_surql() == Ok("SELECT name AS name, ->purchased.filter(|$v1| $v1.quantity > 2).map(|$v2| $v2.out.title) AS titles FROM customer")
expect Surreal.from(products).incoming(purchased).select(|(p, buys)| { title: p.title, buyers: buys.map(|e| e.from.get().name) }).to_surql() == Ok("SELECT <-purchased.map(|$v1| $v1.in.name) AS buyers, title AS title FROM product")
expect Surreal.from(customers).outgoing(purchased).filter(|(_, bought)| bought.any(|e| e.quantity > 2)).select(|(c, _)| { name: c.name }).to_surql() == Ok("SELECT name AS name FROM customer WHERE ->purchased.any(|$v1| $v1.quantity > 2)")
expect Surreal.from(orders).group_by(|o| o.customer.get().address.city).aggregate(|city, rows| { city, orders: rows.len(), revenue: rows.map(|o| o.total).sum() }).to_surql() == Ok("SELECT customer.address.city AS city, count() AS orders, math::sum(total) AS revenue FROM order GROUP BY customer.address.city")
expect Surreal.from(orders).group_by(|o| o.customer.get().address.city).aggregate(|city, rows| { city, orders: rows.len(), revenue: rows.map(|o| o.total).sum() }).order_by(|r| r.revenue, Desc).limit(10).start(0).to_surql() == Ok("SELECT customer.address.city AS city, count() AS orders, math::sum(total) AS revenue FROM order GROUP BY customer.address.city ORDER BY revenue DESC LIMIT 10 START 0")
# The per-group function reads a link through `Grouped`'s own cut.
expect Surreal.from(orders).group_by(|o| o.total).aggregate(|total, rows| { total, paris: rows.keep_if(|o| o.customer.get().address.city == "Paris").len() }).to_surql() == Ok("SELECT count(customer.address.city = 'Paris') AS paris, total AS total FROM order GROUP BY total")
expect Surreal.from(orders).select(|o| { id: o.id, total: o.total }).order_by(|r| r.total, Asc).order_by(|r| r.id, Desc).to_surql() == Ok("SELECT record::id(id) AS id, total AS total FROM order ORDER BY total, id DESC")
expect Surreal.from(orders).select_value(|o| o.total).order_by(|t| t, Desc).limit(2).to_surql() == Ok("SELECT VALUE total FROM order ORDER BY total DESC LIMIT 2")
expect Surreal.from(orders).select_value(|o| o.customer.get().name).to_surql() == Ok("SELECT VALUE customer.name FROM order")

# ------------------------------------------------------ parameters

by_min : Surreal.Selected(Params, Order)
by_min = Surreal.from(orders).filter_by(|p, o| o.total >= p.min_total).select_all()

expect by_min.to_surql() == Ok("SELECT * FROM order WHERE total >= $min_total")
expect by_min.bind({ min_total: 20 }).map_ok(|s| s.surql) == Ok("SELECT * FROM order WHERE total >= $min_total")
expect by_min.bind({ min_total: 20 }).map_ok(|s| s.inlined) == Ok("SELECT * FROM order WHERE total >= 20.0dec")
expect by_min.bind({ min_total: 20 }).map_ok(|s| s.lets.map(|l| (l.name, Ql.literal(l.value)))) == Ok([("min_total", "20.0dec")])
expect by_min.bind({ min_total: 20 }).map_ok(|s| s.to_script()) == Ok("LET $min_total = 20.0dec;\nSELECT * FROM order WHERE total >= $min_total;")
expect by_min.bind({ min_total: 20 }).map_ok(|s| s.block("-- query: big_orders", ["-- ordered"])) == Ok("-- query: big_orders\n-- ordered\nLET $min_total = 20.0dec;\nSELECT * FROM order WHERE total >= $min_total;")
expect Surreal.from(orders).select_all().bind({}).map_ok(|s| s.to_script()) == Ok("SELECT * FROM order;")

# A parameter that is a record, a list or an id is bound whole.
Window : { lo : Dec, tags : List(Str), who : Surreal.Id(Product) }

windowed : Surreal.Selected(Window, Order)
windowed = Surreal.from(orders).filter_by(|p, o| o.total >= p.lo and o.items.any(|i| i.product.id() == p.who)).select_all()

expect windowed.bind({ lo: 1, tags: ["a"], who: Surreal.id_of("product", "pen") }).map_ok(|s| s.inlined) == Ok("SELECT * FROM order WHERE (total >= 1.0dec) AND items.any(|$v1| $v1.product = product:⟨pen⟩)")

# SurrealDB sets `$auth`, `$token`, `$session` and `$access` itself.
Locked : { session : Str }

locked : Surreal.Selected(Locked, Order)
locked = Surreal.from(orders).filter_by(|p, o| o.id == p.session).select_all()

expect locked.bind({ session: "x" }).map_ok(|s| s.surql) == Err(Unsupported("`$session` is a protected variable in SurrealDB; name the parameter otherwise"))

# Values captured from the function around the clause.
orders_over : Dec, Surreal.Id(Product) -> Code.Bound(Try({ surql : Str, slots : List(Code.Ty) }, Surreal.Error))
orders_over = |min, pen| Surreal.select_where(orders, |o| o.total >= min and o.items.any(|i| i.product.id() == pen))

expect {
	bound = orders_over(5, Surreal.id_of("product", "pen"))
	bound.value().map_ok(|b| b.surql) == Ok("SELECT * FROM order WHERE (total >= $_1) AND items.any(|$v1| $v1.product = $_2)") and bound.inputs().len() == 2
}
expect Surreal.bind_captured(orders_over(5, Surreal.id_of("product", "pen"))).map_ok(|s| s.inlined) == Ok("SELECT * FROM order WHERE (total >= 5.0dec) AND items.any(|$v1| $v1.product = product:⟨pen⟩)")
expect Surreal.bind_captured(orders_over(5, Surreal.id_of("product", "pen"))).map_ok(|s| s.to_script()) == Ok("LET $_1 = 5.0dec;\nLET $_2 = product:⟨pen⟩;\nSELECT * FROM order WHERE (total >= $_1) AND items.any(|$v1| $v1.product = $_2);")

# ------------------------------------------------------------ writes

pen : Product
pen = { id: "pen", title: "Pen", price: 1.5 }

mug : Product
mug = { id: "mug", title: "O'Mug", price: 4 }

edge1 : Edge
edge1 = { id: "e1", from: customers.link("ada"), to: products.link("pen"), quantity: 2 }

Edge : Purchased

expect products.insert([pen, mug]).map_ok(|s| s.surql) == Ok("BEGIN;\nINSERT INTO product [{ id: 'pen', price: 1.5dec, title: 'Pen' }, { id: 'mug', price: 4.0dec, title: 'O\\'Mug' }];\nCOMMIT")
expect products.insert([pen]).map_ok(|s| s.to_script()) == Ok("BEGIN;\nINSERT INTO product [{ id: 'pen', price: 1.5dec, title: 'Pen' }];\nCOMMIT;")
expect products.insert([]).map_ok(|s| s.surql) == Ok("BEGIN;\nINSERT INTO product [];\nCOMMIT")
expect purchased.insert([edge1]).map_ok(|s| s.surql) == Ok("BEGIN;\nINSERT RELATION INTO purchased [{ in: customer:⟨ada⟩, id: 'e1', quantity: 2, out: product:⟨pen⟩ }];\nCOMMIT")
expect products.create(pen).map_ok(|s| s.surql) == Ok("CREATE product:⟨pen⟩ CONTENT { price: 1.5dec, title: 'Pen' }")
expect products.upsert(mug).map_ok(|s| s.surql) == Ok("UPSERT product:⟨mug⟩ CONTENT { price: 4.0dec, title: 'O\\'Mug' }")
expect purchased.relate(edge1).map_ok(|s| s.surql) == Ok("RELATE customer:⟨ada⟩->purchased:⟨e1⟩->product:⟨pen⟩ CONTENT { quantity: 2 }")
expect products.relate(pen).map_ok(|s| s.surql) == Err(Unsupported("`product` is not a relation table, so it has no edges to relate"))
expect orders.update(|o| o.total > 100, |o| { ..o, total: o.total * 0.9, payment: Cash }).to_surql() == Ok("UPDATE order SET payment = 'Cash', total = total * 0.9dec WHERE total > 100.0dec")
expect orders.update(|o| o.total > 100, |o| o).to_surql() == Err(Unsupported("this update changes no field"))
expect orders.update(|o| o.total > 100, |o| { ..o, id: "x" }).to_surql() == Err(Unsupported("an update cannot change `id`, the record key"))
expect orders.delete(|o| o.items.is_empty()).to_surql() == Ok("DELETE order WHERE items.len() = 0")
expect customers.update(|c| c.name == "", |c| { ..c, name: Surreal.Rand.ulid() }).to_surql() == Ok("UPDATE customer SET name = rand::ulid() WHERE name = ''")
expect customers.update(|c| c.name == Surreal.Rand.ulid(), |c| { ..c, name: "x" }).to_surql() == Err(Unsupported("`Surreal.Rand.ulid` gives a new value on every call: use it in a default, a computed field or an update"))

Raise : { by : Dec, floor : Dec }

raise : Surreal.Write(Raise, Order)
raise = orders.update_by(|p, o| o.total < p.floor, |p, o| { ..o, total: o.total + p.by })

expect raise.to_surql() == Ok("UPDATE order SET total = total + $by WHERE total < $floor")
expect raise.bind({ by: 5, floor: 10 }).map_ok(|s| s.to_script()) == Ok("LET $by = 5.0dec;\nLET $floor = 10.0dec;\nUPDATE order SET total = total + $by WHERE total < $floor;")
expect raise.bind({ by: 5, floor: 10 }).map_ok(|s| s.inlined) == Ok("UPDATE order SET total = total + 5.0dec WHERE total < 10.0dec")

Cap : { max : Dec }

cap : Surreal.Write(Cap, Order)
cap = orders.delete_by(|p, o| o.total > p.max)

expect cap.bind({ max: 1000 }).map_ok(|s| s.inlined) == Ok("DELETE order WHERE total > 1000.0dec")

# A write, then the rows it changed: one block.
expect {
	write = orders.update(|o| o.total > 100, |o| { ..o, payment: Cash }).bind({})
	read = Surreal.from(orders).select_all().bind({})
	match (write, read) {
		(Ok(w), Ok(r)) => w.then(r).map_ok(|s| s.to_script()) == Ok("UPDATE order SET payment = 'Cash' WHERE total > 100.0dec;\nSELECT * FROM order;")
		_ => Bool.False
	}
}

# An optional parameter that is absent has no `LET`, so SurrealDB reads it as
# NONE, and the inlined text keeps its name.
Bounds : { lo : Dec, hi ?: Dec }

bounded : Surreal.Selected(Bounds, Order)
bounded = Surreal.from(orders).filter_by(|p, o| o.total >= p.lo and o.total <= (p.?hi ?? 1000)).select_all()

expect bounded.bind({ lo: 1 }).map_ok(|s| s.lets.len()) == Ok(1)
expect bounded.bind({ lo: 1, hi: 9 }).map_ok(|s| s.lets.len()) == Ok(2)
expect bounded.bind({ lo: 1 }).map_ok(|s| s.inlined.contains("$hi")) == Ok(Bool.True)
expect bounded.bind({ lo: 1, hi: 9 }).map_ok(|s| s.inlined.contains("$hi")) == Ok(Bool.False)
