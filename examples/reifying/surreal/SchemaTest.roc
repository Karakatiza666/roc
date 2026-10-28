import Surreal
import Schema
import Types

# Tests of the schema builder and `Surreal.schema` on a small domain. They sit
# here because a row type comes from a reified table, and only `Surreal`
# makes one. Nothing outside this file imports it.
SchemaTest :: {}

Address : { city : Str, zip ?: Str }

Customer := { id : Str, name : Str, email : Str, address : Address, tags : List(Str), referrer ?: Surreal.Link(Customer), age : U8 }

Product : { id : Str, title : Str, label : Str, price : Dec, stock : I32 }

Item : { product : Surreal.Link(Product), qty : I64 }

Payment : [Cash, Card({ last4 : Str }), Invoice({ contact : Surreal.Link(Customer), due : Str })]

Order : {
	id : Str,
	customer : Surreal.Link(Customer),
	items : List(Item),
	payment : Payment,
	gift ?: { to : Surreal.Link(Customer), note : Str },
	wishlist : List(Surreal.Link(Product)),
	total : Dec,
	created : Surreal.Datetime,
}

Purchase : { id : Str, from : Surreal.Link(Customer), to : Surreal.Link(Product), quantity : I64 }

customers : Surreal.Table(Customer)
customers = Surreal.table("customer", |c| c)

products : Surreal.Table(Product)
products = Surreal.table("product", |p| p)

orders : Surreal.Table(Order)
orders = Surreal.table("order", |o| o)

purchased : Surreal.Table(Purchase)
purchased = Surreal.relation("purchased", customers, products, |e| e)

# The constraints are Roc functions: the schema reifies them, and Roc runs them.
positive_qty : Item -> Bool
positive_qty = |i| i.qty > 0

total_matches_items : Order -> Bool
total_matches_items = |o| o.items.is_empty() or o.total > 0

expect positive_qty({ product: products.link("pen"), qty: 2 })
expect !positive_qty({ product: products.link("pen"), qty: 0 })

customer_def : Surreal.Defined
customer_def =
	customers.define()
		.unique(|c| c.email)
		.unique(|c| { city: c.address.city, name: c.name })
		.assert(|c| c.email, |e| e.contains("@"))
		.assert(
			|c| c.address.?zip,
			|z| match z {
				Ok(s) => s.starts_with("7")
				Err(_) => Bool.True
			},
		)
		.assert_each(|c| c.tags, |t| t != "")
		.check("named", |c| c.name != "")
		.default(|c| c.tags, ["new"])
		.done()

product_def : Surreal.Defined
product_def =
	products.define()
		.default(|p| p.stock, 0)
		.readonly(|p| p.title)
		.computed(|p| p.label, |p| p.title.concat("!"))
		.done()

order_def : Surreal.Defined
order_def =
	orders.define()
		.assert_each(|o| o.items, positive_qty)
		.check("total matches items", total_matches_items)
		.check("positive total", |o| o.total >= 0)
		.assert(
			|o| o.payment,
			|p| match p {
				Invoice(i) => i.due != ""
				_ => Bool.True
			},
		)
		.on_delete(products, Reject)
		.on_delete(customers, Cascade)
		.on_delete_at(|o| o.wishlist, Unset)
		.created_now(|o| o.created)
		.index(|o| o.total)
		.comment(|o| o.total, "in euros")
		.done()

purchased_def : Surreal.Defined
purchased_def =
	purchased.define()
		.check("positive quantity", |e| e.quantity > 0)
		.check("not a gift to self", |e| e.quantity < 100 or e.from.get().name != "")
		.unique(|e| { from: e.from, to: e.to })
		.done()

script_of : List(Surreal.Defined) -> List(Str)
script_of = |defs| match Surreal.schema(defs) {
	Ok(text) => text.split_on("\n")
	Err(BadSchema(why)) => ["BadSchema: ${why}"]
	Err(Unsupported(why)) => ["Unsupported: ${why}"]
}

# ------------------------------------------------- the whole script, in order

# Tables, then fields, then indexes, then row checks, then delete events,
# so no statement names a table defined after it.
expect script_of([customer_def, product_def, order_def, purchased_def]) == [
	"DEFINE TABLE OVERWRITE customer SCHEMAFULL;",
	"DEFINE TABLE OVERWRITE product SCHEMAFULL;",
	"DEFINE TABLE OVERWRITE order SCHEMAFULL;",
	"DEFINE TABLE OVERWRITE purchased TYPE RELATION IN customer OUT product ENFORCED SCHEMAFULL;",
	"DEFINE FIELD OVERWRITE address ON customer TYPE object;",
	"DEFINE FIELD OVERWRITE address.city ON customer TYPE string;",
	"DEFINE FIELD OVERWRITE address.zip ON customer TYPE option<string> ASSERT (IF $value IS NONE THEN true ELSE string::starts_with($value, '7') END);",
	"DEFINE FIELD OVERWRITE age ON customer TYPE int ASSERT $value >= 0 AND $value <= 255;",
	"DEFINE FIELD OVERWRITE email ON customer TYPE string ASSERT string::contains($value, '@');",
	"DEFINE FIELD OVERWRITE name ON customer TYPE string ASSERT $value != '';",
	"DEFINE FIELD OVERWRITE referrer ON customer TYPE option<record<customer>> REFERENCE ON DELETE REJECT ASSERT ($value = NONE OR (record::exists($value)));",
	"DEFINE FIELD OVERWRITE tags ON customer TYPE array<string> DEFAULT ['new'] ASSERT $value.all(|$item| $item != '');",
	"DEFINE FIELD OVERWRITE label ON product TYPE string VALUE $this.title + '!';",
	"DEFINE FIELD OVERWRITE price ON product TYPE decimal;",
	"DEFINE FIELD OVERWRITE stock ON product TYPE int DEFAULT 0 ASSERT $value >= -2147483648 AND $value <= 2147483647;",
	"DEFINE FIELD OVERWRITE title ON product TYPE string READONLY;",
	"DEFINE FIELD OVERWRITE created ON order TYPE datetime VALUE time::now() READONLY;",
	"DEFINE FIELD OVERWRITE customer ON order TYPE record<customer> REFERENCE ON DELETE CASCADE ASSERT record::exists($value);",
	"DEFINE FIELD OVERWRITE gift ON order TYPE option<object>;",
	"DEFINE FIELD OVERWRITE gift.note ON order TYPE string;",
	"DEFINE FIELD OVERWRITE gift.to ON order TYPE record<customer> ASSERT record::exists($value);",
	"DEFINE FIELD OVERWRITE items ON order TYPE array<object> ASSERT $value.all(|$e| object::keys($e).all(|$k| $k IN ['product', 'qty']));",
	"DEFINE FIELD OVERWRITE items[*].product ON order TYPE record<product> ASSERT record::exists($value);",
	"DEFINE FIELD OVERWRITE items[*].qty ON order TYPE int ASSERT $value > 0;",
	"DEFINE FIELD OVERWRITE payment ON order TYPE { kind: \"Card\", last4: string } | \"Cash\" | { kind: \"Invoice\", contact: record<customer>, due: string } ASSERT ((IF $value.kind = 'Invoice' THEN record::exists($value.contact) ELSE true END)) AND ((IF $value.kind = 'Invoice' THEN $value.due != '' ELSE true END));",
	"DEFINE FIELD OVERWRITE total ON order TYPE decimal ASSERT $value >= 0.0dec COMMENT 'in euros';",
	"DEFINE FIELD OVERWRITE wishlist ON order TYPE array<record<product>> REFERENCE ON DELETE UNSET ASSERT $value.all(|$e1| record::exists($e1));",
	"DEFINE FIELD OVERWRITE quantity ON purchased TYPE int ASSERT $value > 0;",
	"DEFINE INDEX OVERWRITE customer_email_unique ON customer FIELDS email UNIQUE;",
	"DEFINE INDEX OVERWRITE customer_address_city_name_unique ON customer FIELDS address.city, name UNIQUE;",
	"DEFINE INDEX OVERWRITE order_total_index ON order FIELDS total;",
	"DEFINE INDEX OVERWRITE order_gift_to_link ON order FIELDS gift.to;",
	"DEFINE INDEX OVERWRITE order_items_product_link ON order FIELDS items[*].product;",
	"DEFINE INDEX OVERWRITE purchased_in_out_unique ON purchased FIELDS in, out UNIQUE;",
	"DEFINE EVENT OVERWRITE order_check_total_matches_items ON order WHEN $event IN ['CREATE', 'UPDATE'] THEN { IF !(($after.items.len() = 0) OR ($after.total > 0.0dec)) { THROW 'order: total matches items' } };",
	"DEFINE EVENT OVERWRITE purchased_check_not_a_gift_to_self ON purchased WHEN $event IN ['CREATE', 'UPDATE'] THEN { IF !(($after.quantity < 100) OR ($after.in.name != '')) { THROW 'purchased: not a gift to self' } };",
	"DEFINE EVENT OVERWRITE order_gift_to_on_delete ON customer WHEN $event = 'DELETE' THEN { DELETE order WHERE gift.to = $before.id };",
	"DEFINE EVENT OVERWRITE order_items_product_on_delete ON product WHEN $event = 'DELETE' THEN { IF (SELECT VALUE id FROM order WHERE items.any(|$e1| $e1.product = $before.id) LIMIT 1) != [] { THROW <string>$before.id + ' is referenced by order.items[*].product' } };",
	"DEFINE EVENT OVERWRITE order_payment_Invoice_contact_on_delete ON customer WHEN $event = 'DELETE' THEN { DELETE order WHERE (payment.kind = 'Invoice' AND payment.contact = $before.id) };",
]

## The statements of a script that contain `part`.
lines_with : List(Surreal.Defined), Str -> List(Str)
lines_with = |defs, part| script_of(defs).keep_if(|line| line.contains(part))

problem_of : List(Surreal.Defined) -> Str
problem_of = |defs| match Surreal.schema(defs) {
	Ok(_) => "ok"
	Err(BadSchema(why)) => "BadSchema: ${why}"
	Err(Unsupported(why)) => "Unsupported: ${why}"
}

# `Rand` gives a new value on every call: a default and a computed field may use it, a constraint may not.
expect lines_with([products.define().default_by(|p| p.label, |_| Surreal.Rand.ulid()).done()], "label ON product") == ["DEFINE FIELD OVERWRITE label ON product TYPE string DEFAULT rand::ulid();"]
expect lines_with([products.define().default_by(|p| p.label, |p| p.title.concat(Surreal.Rand.int(1, p.stock.to_i64()).to_str())).done()], "label ON product") == ["DEFINE FIELD OVERWRITE label ON product TYPE string DEFAULT $this.title + <string>rand::int(1, $this.stock);"]
expect lines_with([products.define().computed(|p| p.label, |_| Surreal.Rand.uuid()).done()], "label ON product") == ["DEFINE FIELD OVERWRITE label ON product TYPE string VALUE <string>rand::uuid();"]
expect problem_of([products.define().assert(|p| p.stock, |n| n.to_i64() > Surreal.Rand.int(0, 5)).done()]) == "Unsupported: `Surreal.Rand.int` gives a new value on every call: use it in a default, a computed field or an update"
expect problem_of([products.define().check("lucky", |p| p.stock.to_i64() > Surreal.Rand.int(0, 5)).done()]) == "Unsupported: `Surreal.Rand.int` gives a new value on every call: use it in a default, a computed field or an update"
expect problem_of([products.define().default(|p| p.stock, 0).default_by(|p| p.stock, |_| 1).done()]) == "BadSchema: `stock` has two defaults"

# ------------------------------------------------------- where a check goes

# One top-level field, read at any depth: that field's ASSERT, over `$value`.
expect lines_with([customers.define().check("city", |c| c.address.city != "").done()], "ASSERT") == [
	"DEFINE FIELD OVERWRITE address ON customer TYPE object ASSERT $value.city != '';",
	"DEFINE FIELD OVERWRITE age ON customer TYPE int ASSERT $value >= 0 AND $value <= 255;",
	"DEFINE FIELD OVERWRITE referrer ON customer TYPE option<record<customer>> REFERENCE ON DELETE REJECT ASSERT ($value = NONE OR (record::exists($value)));",
]

# Through a link, still one field of this row.
expect lines_with([customers.define().done(), products.define().done(), orders.define().check("adult buyer", |o| o.customer.get().age >= 18).done()], "ON order TYPE record<customer>") == [
	"DEFINE FIELD OVERWRITE customer ON order TYPE record<customer> REFERENCE ON DELETE REJECT ASSERT (record::exists($value)) AND ($value.age >= 18);",
	"DEFINE FIELD OVERWRITE gift.to ON order TYPE record<customer> ASSERT record::exists($value);",
]

# Two fields: an event over `$after`.
expect lines_with([customers.define().check("name in email", |c| c.email.contains(c.name)).done()], "_check_") == [
	"DEFINE EVENT OVERWRITE customer_check_name_in_email ON customer WHEN $event IN ['CREATE', 'UPDATE'] THEN { IF !(string::contains($after.email, $after.name)) { THROW 'customer: name in email' } };",
]

# The record key is not a field definition, so a check on it is an event.
expect lines_with([customers.define().check("key", |c| c.id != "root").done()], "_check_") == [
	"DEFINE EVENT OVERWRITE customer_check_key ON customer WHEN $event IN ['CREATE', 'UPDATE'] THEN { IF !(record::id($after.id) != 'root') { THROW 'customer: key' } };",
]

# No field: always or never true.
expect problem_of([customers.define().check("always", |_| Bool.True).done()]) == "BadSchema: the check `always` reads no field, so it is always or never true"

# An element check that reads two element fields goes on the list.
expect lines_with([customers.define().done(), products.define().done(), orders.define().assert_each(|o| o.items, |i| i.qty > 0 and i.product.get().stock > 0).done()], "ON order TYPE array<object>") == [
	"DEFINE FIELD OVERWRITE items ON order TYPE array<object> ASSERT ($value.all(|$e| object::keys($e).all(|$k| $k IN ['product', 'qty']))) AND ($value.all(|$item| ($item.qty > 0) AND ($item.product.stock > 0)));",
]

# ------------------------------------------------------ paths that are refused

expect problem_of([orders.define().assert(|o| o.items.map(|i| i.qty), |qs| qs.len() > 0).done()]) == "Unsupported: `assert` reads one field; for each element of a list use `assert_each`"
expect problem_of([customers.define().assert(|c| c.name.concat("x"), |n| n != "").done()]) == "Unsupported: a field path reads fields only; this one calls `Str.concat`"
expect problem_of([customers.define().assert(|c| c.id, |k| k != "").done()]) == "BadSchema: `customer.id` has no field definition to put this on; the record key and an edge's ends are SurrealDB's own"
expect problem_of([customers.define().default(|c| c.tags, []).default(|c| c.tags, ["a"]).done()]) == "BadSchema: `tags` has two defaults"
expect problem_of([customers.define().done(), products.define().done(), orders.define().on_delete(orders, Cascade).done()]) == "BadSchema: no link in `order` points at table `order`"
expect problem_of([customers.define().done(), products.define().done(), orders.define().on_delete_at(|o| o.total, Cascade).done()]) == "BadSchema: `order.total` is not a link"
expect problem_of([customers.define().done(), products.define().done(), orders.define().on_delete(customers, Unset).done()]) == "BadSchema: `order.customer` is required, so a delete cannot unset it; make it optional (`?:`) or use Reject, Cascade or Ignore"
expect problem_of([customers.define().done(), products.define().done(), orders.define().on_delete_at(|o| o.customer, Cascade).on_delete(customers, Unset).done()]) == "BadSchema: `order.gift.to`: the link is a required field, so it cannot be unset; make it optional (`?:`) or use Reject, Cascade or Ignore"

# ------------------------------------------------- one link, every shape

P : { id : Str, title : Str }

Shapes : {
	id : Str,
	root : Surreal.Link(P),
	maybe ?: Surreal.Link(P),
	many : List(Surreal.Link(P)),
	obj : { l ?: Surreal.Link(P), n : I64 },
	rows : List({ l : Surreal.Link(P), n : I64 }),
	arm : [Empty, Has({ l : Surreal.Link(P) })],
	key : Surreal.Id(P),
}

ps : Surreal.Table(P)
ps = Surreal.table("p", |r| r)

shapes : Surreal.Table(Shapes)
shapes = Surreal.table("h", |r| r)

## The statements a policy gives the links of `h`.
policy_lines : Surreal.Defined -> List(Str)
policy_lines = |holder| script_of([ps.define().done(), holder]).keep_if(|line| line.contains("REFERENCE") or line.contains("ON p WHEN") or line.contains("_link"))

shapes_with : [Reject, Unset, Cascade, Ignore] -> List(Str)
shapes_with = |policy| policy_lines(shapes.define().on_delete(ps, policy).done())

Unsettable : { id : Str, maybe ?: Surreal.Link(P), many : List(Surreal.Link(P)), obj : { l ?: Surreal.Link(P), n : I64 }, rows : List({ l : Surreal.Link(P), n : I64 }) }

unsettable : Surreal.Table(Unsettable)
unsettable = Surreal.table("h", |r| r)

# The sites `Schema` walks are the ones `Types.link_sites` lists, with the same shapes.
expect {
	source = Surreal.source(shapes)
	mine = match Schema.sites(source) {
		Ok(sites) => sites.map(|s| (Schema.site_path(s.hops), Schema.shape(s)))
		Err(_) => []
	}
	theirs = Types.link_sites(source.row_ty).map(|s| (s.path, s.shape))
	mine == theirs and mine.len() == 7
}

expect shapes_with(Reject) == [
	"DEFINE FIELD OVERWRITE key ON h TYPE record<p> REFERENCE ON DELETE REJECT ASSERT record::exists($value);",
	"DEFINE FIELD OVERWRITE many ON h TYPE array<record<p>> REFERENCE ON DELETE REJECT ASSERT $value.all(|$e1| record::exists($e1));",
	"DEFINE FIELD OVERWRITE maybe ON h TYPE option<record<p>> REFERENCE ON DELETE REJECT ASSERT ($value = NONE OR (record::exists($value)));",
	"DEFINE FIELD OVERWRITE root ON h TYPE record<p> REFERENCE ON DELETE REJECT ASSERT record::exists($value);",
	"DEFINE INDEX OVERWRITE h_obj_l_link ON h FIELDS obj.l;",
	"DEFINE INDEX OVERWRITE h_rows_l_link ON h FIELDS rows[*].l;",
	"DEFINE EVENT OVERWRITE h_arm_Has_l_on_delete ON p WHEN $event = 'DELETE' THEN { IF (SELECT VALUE id FROM h WHERE (arm.kind = 'Has' AND arm.l = $before.id) LIMIT 1) != [] { THROW <string>$before.id + ' is referenced by h.arm.l' } };",
	"DEFINE EVENT OVERWRITE h_obj_l_on_delete ON p WHEN $event = 'DELETE' THEN { IF (SELECT VALUE id FROM h WHERE obj.l = $before.id LIMIT 1) != [] { THROW <string>$before.id + ' is referenced by h.obj.l' } };",
	"DEFINE EVENT OVERWRITE h_rows_l_on_delete ON p WHEN $event = 'DELETE' THEN { IF (SELECT VALUE id FROM h WHERE rows.any(|$e1| $e1.l = $before.id) LIMIT 1) != [] { THROW <string>$before.id + ' is referenced by h.rows[*].l' } };",
]

expect shapes_with(Cascade) == [
	"DEFINE FIELD OVERWRITE key ON h TYPE record<p> REFERENCE ON DELETE CASCADE ASSERT record::exists($value);",
	"DEFINE FIELD OVERWRITE many ON h TYPE array<record<p>> REFERENCE ON DELETE CASCADE ASSERT $value.all(|$e1| record::exists($e1));",
	"DEFINE FIELD OVERWRITE maybe ON h TYPE option<record<p>> REFERENCE ON DELETE CASCADE ASSERT ($value = NONE OR (record::exists($value)));",
	"DEFINE FIELD OVERWRITE root ON h TYPE record<p> REFERENCE ON DELETE CASCADE ASSERT record::exists($value);",
	"DEFINE INDEX OVERWRITE h_obj_l_link ON h FIELDS obj.l;",
	"DEFINE INDEX OVERWRITE h_rows_l_link ON h FIELDS rows[*].l;",
	"DEFINE EVENT OVERWRITE h_arm_Has_l_on_delete ON p WHEN $event = 'DELETE' THEN { DELETE h WHERE (arm.kind = 'Has' AND arm.l = $before.id) };",
	"DEFINE EVENT OVERWRITE h_obj_l_on_delete ON p WHEN $event = 'DELETE' THEN { DELETE h WHERE obj.l = $before.id };",
	"DEFINE EVENT OVERWRITE h_rows_l_on_delete ON p WHEN $event = 'DELETE' THEN { DELETE h WHERE rows.any(|$e1| $e1.l = $before.id) };",
]

# Ignore: native `IGNORE` at the root, and no event or index below it.
expect shapes_with(Ignore) == [
	"DEFINE FIELD OVERWRITE key ON h TYPE record<p> REFERENCE ON DELETE IGNORE ASSERT record::exists($value);",
	"DEFINE FIELD OVERWRITE many ON h TYPE array<record<p>> REFERENCE ON DELETE IGNORE ASSERT $value.all(|$e1| record::exists($e1));",
	"DEFINE FIELD OVERWRITE maybe ON h TYPE option<record<p>> REFERENCE ON DELETE IGNORE ASSERT ($value = NONE OR (record::exists($value)));",
	"DEFINE FIELD OVERWRITE root ON h TYPE record<p> REFERENCE ON DELETE IGNORE ASSERT record::exists($value);",
]

# Unset: an optional field is set to NONE; a link, or an object that holds
# one, leaves its list.
expect policy_lines(unsettable.define().on_delete(ps, Unset).done()) == [
	"DEFINE FIELD OVERWRITE many ON h TYPE array<record<p>> REFERENCE ON DELETE UNSET ASSERT $value.all(|$e1| record::exists($e1));",
	"DEFINE FIELD OVERWRITE maybe ON h TYPE option<record<p>> REFERENCE ON DELETE UNSET ASSERT ($value = NONE OR (record::exists($value)));",
	"DEFINE INDEX OVERWRITE h_obj_l_link ON h FIELDS obj.l;",
	"DEFINE INDEX OVERWRITE h_rows_l_link ON h FIELDS rows[*].l;",
	"DEFINE EVENT OVERWRITE h_obj_l_on_delete ON p WHEN $event = 'DELETE' THEN { UPDATE h SET obj.l = NONE WHERE obj.l = $before.id };",
	"DEFINE EVENT OVERWRITE h_rows_l_on_delete ON p WHEN $event = 'DELETE' THEN { UPDATE h SET rows = rows.filter(|$e1| !($e1.l = $before.id)) WHERE rows.any(|$e1| $e1.l = $before.id) };",
]

# Unset is refused where nothing can be unset: a required root, an arm.
expect problem_of([ps.define().done(), shapes.define().on_delete(ps, Unset).done()]) == "BadSchema: `h.arm.l`: an arm of a union cannot be unset; use Reject, Cascade or Ignore"
expect problem_of([ps.define().done(), shapes.define().on_delete(ps, Unset).on_delete_at(|h| h.root, Cascade).done()]) == "BadSchema: `h.arm.l`: an arm of a union cannot be unset; use Reject, Cascade or Ignore"

# `on_delete_at` wins over `on_delete` for its one path.
expect policy_lines(unsettable.define().on_delete(ps, Cascade).on_delete_at(|h| h.rows.map(|r| r.l), Ignore).on_delete_at(|h| h.many, Unset).done()) == [
	"DEFINE FIELD OVERWRITE many ON h TYPE array<record<p>> REFERENCE ON DELETE UNSET ASSERT $value.all(|$e1| record::exists($e1));",
	"DEFINE FIELD OVERWRITE maybe ON h TYPE option<record<p>> REFERENCE ON DELETE CASCADE ASSERT ($value = NONE OR (record::exists($value)));",
	"DEFINE INDEX OVERWRITE h_obj_l_link ON h FIELDS obj.l;",
	"DEFINE EVENT OVERWRITE h_obj_l_on_delete ON p WHEN $event = 'DELETE' THEN { DELETE h WHERE obj.l = $before.id };",
]

# ------------------------------------------------------------------ cycles

A := { id : Str, b : Surreal.Link(B) }

B := { id : Str, a : Surreal.Link(A) }

C := { id : Str, d ?: Surreal.Link(D) }

D := { id : Str, c : Surreal.Link(C) }

Boss := { id : Str, boss : Surreal.Link(Boss) }

a_rows : Surreal.Table(A)
a_rows = Surreal.table("a", |r| r)

b_rows : Surreal.Table(B)
b_rows = Surreal.table("b", |r| r)

c_rows : Surreal.Table(C)
c_rows = Surreal.table("c", |r| r)

d_rows : Surreal.Table(D)
d_rows = Surreal.table("d", |r| r)

bosses : Surreal.Table(Boss)
bosses = Surreal.table("boss", |r| r)

expect problem_of([a_rows.define().done(), b_rows.define().done()]) == "BadSchema: required links form a cycle (a.b -> b.a -> a), so no row of it can be written first; make one of them optional (`?:`)"
expect problem_of([bosses.define().done()]) == "BadSchema: required links form a cycle (boss.boss -> boss), so no row of it can be written first; make one of them optional (`?:`)"

# Through an optional field or a union arm a cycle can be filled.
expect problem_of([c_rows.define().done(), d_rows.define().done()]) == "ok"
expect problem_of([customers.define().done()]) == "ok"

# A self-link read through `.?`, in a check over two fields.
not_self_referred : Customer -> Bool
not_self_referred = |c| match c.?referrer {
	Ok(r) => r.get().name != c.name
	Err(_) => Bool.True
}

expect lines_with([customers.define().check("not self-referred", not_self_referred).done()], "_check_") == [
	"DEFINE EVENT OVERWRITE customer_check_not_self_referred ON customer WHEN $event IN ['CREATE', 'UPDATE'] THEN { IF !((IF $after.referrer IS NONE THEN true ELSE $after.referrer.name != $after.name END)) { THROW 'customer: not self-referred' } };",
]
