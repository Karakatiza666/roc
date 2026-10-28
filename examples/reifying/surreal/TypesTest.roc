import Ql
import Surreal
import Types

# Tests of `Types` and of the table constructors on a small domain. They sit
# here because a row type comes from a reified table, and only `Surreal`
# makes one. Nothing outside this file imports it.
TypesTest :: {}

Address : { city : Str, zip ?: Str }

Customer := { id : Str, name : Str, email : Str, address : Address, tags : List(Str), referrer ?: Surreal.Link(Customer), age : U8, born : Surreal.Datetime }

Product : { id : Str, title : Str, price : Dec, stock : I32, ratio : F64, live : Bool }

Item : { product : Surreal.Link(Product), qty : I64 }

Payment : [Cash, Card({ last4 : Str }), Invoice({ contact : Surreal.Link(Customer), due : Str }), Check(I64), Wire(Str, I64), Gift(Surreal.Link(Product))]

Order : { id : Str, customer : Surreal.Link(Customer), items : List(Item), payment : Payment, gift ?: { to : Surreal.Link(Customer), note : Str }, wishlist : List(Surreal.Link(Product)), by : Surreal.Id(Customer), placed : Surreal.Datetime }

Purchase : { id : Str, from : Surreal.Link(Customer), to : Surreal.Link(Product), since : I64 }

customers : Surreal.Table(Customer)
customers = Surreal.table("customer", |c| c)

products : Surreal.Table(Product)
products = Surreal.table("product", |p| p)

orders : Surreal.Table(Order)
orders = Surreal.table("order", |o| o)

purchased : Surreal.Table(Purchase)
purchased = Surreal.relation("purchased", customers, products, |e| e)

# The schema list, as `Surreal.schema` will build it from the tables.
# Every row of the type table, one field each.
Status := [Active, Closed]

Kitchen : {
	id : Str,
	i8 : I8,
	u8 : U8,
	i16 : I16,
	u16 : U16,
	i32 : I32,
	u32 : U32,
	i64 : I64,
	f32 : F32,
	f64 : F64,
	dec : Dec,
	flag : Bool,
	text : Str,
	at : Surreal.Datetime,
	who : Surreal.Id(Product),
	near : { x : Str, y ?: I64 },
	note ?: Str,
	names : List(Str),
	rows : List({ s : Str, n : U8 }),
	many : List(Surreal.Link(Product)),
	plain : [Red, Green],
	status : Status,
	bytes : List(U8),
	deep : List(List(I8)),
	pick : [Pad, Pair(Str, I64), Box({ w : I64 })],
	maybe ?: Surreal.Link(Product),
}

kitchen : Surreal.Table(Kitchen)
kitchen = Surreal.table("kitchen", |k| k)

registry : Types.Registry
registry = [Surreal.source(customers), Surreal.source(products), Surreal.source(orders), Surreal.source(purchased), Surreal.source(kitchen)]

defs_of : Str -> List(Str)
defs_of = |name| match registry.find_first(|s| s.name == name) {
	Ok(s) => match Types.field_defs(name, s.row_ty, registry) {
		Ok(defs) => defs.map(|d| "${d.path} ${d.ty} [${Str.join_with(d.asserts, " ; ")}]")
		Err(BadSchema(why)) => [why]
		Err(Unsupported(why)) => [why]
	}
	Err(_) => ["not listed"]
}

check_of : Types.Source, Types.Registry -> Str
check_of = |source, reg| match Types.check_table(source, reg) {
	Ok(_) => "ok"
	Err(BadSchema(why)) => why
	Err(Unsupported(why)) => why
}

# ------------------------------------------------------------ type mapping

expect defs_of("customer") == [
	"address object []",
	"address.city string []",
	"address.zip option<string> []",
	"age int [$value >= 0 AND $value <= 255]",
	"born datetime []",
	"email string []",
	"name string []",
	"referrer option<record<customer>> [($value = NONE OR (record::exists($value)))]",
	"tags array<string> []",
]

expect defs_of("product") == [
	"live bool []",
	"price decimal []",
	"ratio float []",
	"stock int [$value >= -2147483648 AND $value <= 2147483647]",
	"title string []",
]

expect defs_of("order") == [
	"by record<customer> [record::exists($value)]",
	"customer record<customer> [record::exists($value)]",
	"gift option<object> []",
	"gift.note string []",
	"gift.to record<customer> [record::exists($value)]",
	"items array<object> [$value.all(|$e| object::keys($e).all(|$k| $k IN ['product', 'qty']))]",
	"items[*].product record<product> [record::exists($value)]",
	"items[*].qty int []",
	"payment { kind: \"Card\", last4: string } | \"Cash\" | { kind: \"Check\", value: int } | { kind: \"Gift\", value: record<product> } | { kind: \"Invoice\", contact: record<customer>, due: string } | { kind: \"Wire\", _0: string, _1: int } [(IF $value.kind = 'Gift' THEN record::exists($value.value) ELSE true END) ; (IF $value.kind = 'Invoice' THEN record::exists($value.contact) ELSE true END)]",
	"placed datetime []",
	"wishlist array<record<product>> [$value.all(|$e1| record::exists($e1))]",
]

expect defs_of("purchased") == [
	"since int []",
]

expect defs_of("kitchen") == [
	"at datetime []",
	"bytes array<int> [$value.all(|$e1| $e1 >= 0 AND $e1 <= 255)]",
	"dec decimal []",
	"deep array<array<int>> [$value.all(|$e1| $e1.all(|$e2| $e2 >= -128 AND $e2 <= 127))]",
	"f32 float []",
	"f64 float []",
	"flag bool []",
	"i16 int [$value >= -32768 AND $value <= 32767]",
	"i32 int [$value >= -2147483648 AND $value <= 2147483647]",
	"i64 int []",
	"i8 int [$value >= -128 AND $value <= 127]",
	"many array<record<product>> [$value.all(|$e1| record::exists($e1))]",
	"maybe option<record<product>> [($value = NONE OR (record::exists($value)))]",
	"names array<string> []",
	"near object []",
	"near.x string []",
	"near.y option<int> []",
	"note option<string> []",
	"pick { kind: \"Box\", w: int } | \"Pad\" | { kind: \"Pair\", _0: string, _1: int } []",
	"plain \"Green\" | \"Red\" []",
	"rows array<object> [$value.all(|$e| object::keys($e).all(|$k| $k IN ['n', 's']))]",
	"rows[*].n int [$value >= 0 AND $value <= 255]",
	"rows[*].s string []",
	"status \"Active\" | \"Closed\" []",
	"text string []",
	"u16 int [$value >= 0 AND $value <= 65535]",
	"u32 int [$value >= 0 AND $value <= 4294967295]",
	"u8 int [$value >= 0 AND $value <= 255]",
	"who record<product> [record::exists($value)]",
]

# -------------------------------------------------- rows that are not schemas

NoId : { name : Str }

IdInt : { id : I64 }

IdOptional : { id ?: Str }

Big : { id : Str, n : U64 }

Wide : { id : Str, xs : List({ q : I128 }) }

Huge : { id : Str, h : U128 }

KindArm : { id : Str, p : [A({ kind : Str }), B] }

Tuple : { id : Str, t : (I64, Str) }

Tried : { id : Str, t : Try(I64, Str) }

Mapped : { id : Str, d : Dict(Str, I64) }

Spanned : { id : Str, span : Surreal.Duration }

Orphan : { id : Str, c : Surreal.Link(Product) }

Twin : { id : Str, x : I64 }

Empty : { id : Str, e : [] }

Ref : { id : Str, c : Surreal.Link(Twin) }

WrongFrom : { id : Str, from : Surreal.Link(Product), to : Surreal.Link(Product) }

NoTo : { id : Str, from : Surreal.Link(Customer) }

IdFrom : { id : Str, from : Surreal.Id(Customer), to : Surreal.Link(Product) }

bad_table : Surreal.Table(row) -> Types.Source
bad_table = |t| Surreal.source(t)

no_id : Surreal.Table(NoId)
no_id = Surreal.table("no_id", |r| r)

id_int : Surreal.Table(IdInt)
id_int = Surreal.table("id_int", |r| r)

id_optional : Surreal.Table(IdOptional)
id_optional = Surreal.table("id_optional", |r| r)

big : Surreal.Table(Big)
big = Surreal.table("big", |r| r)

wide : Surreal.Table(Wide)
wide = Surreal.table("wide", |r| r)

huge : Surreal.Table(Huge)
huge = Surreal.table("huge", |r| r)

kind_arm : Surreal.Table(KindArm)
kind_arm = Surreal.table("kind_arm", |r| r)

tuple : Surreal.Table(Tuple)
tuple = Surreal.table("tuple", |r| r)

tried : Surreal.Table(Tried)
tried = Surreal.table("tried", |r| r)

mapped : Surreal.Table(Mapped)
mapped = Surreal.table("mapped", |r| r)

spanned : Surreal.Table(Spanned)
spanned = Surreal.table("spanned", |r| r)

orphan : Surreal.Table(Orphan)
orphan = Surreal.table("orphan", |r| r)

twin_a : Surreal.Table(Twin)
twin_a = Surreal.table("twin_a", |r| r)

twin_b : Surreal.Table(Twin)
twin_b = Surreal.table("twin_b", |r| r)

ref : Surreal.Table(Ref)
ref = Surreal.table("ref", |r| r)

empty : Surreal.Table(Empty)
empty = Surreal.table("empty", |r| r)

wrong_from : Surreal.Table(WrongFrom)
wrong_from = Surreal.relation("wrong_from", customers, products, |r| r)

no_to : Surreal.Table(NoTo)
no_to = Surreal.relation("no_to", customers, products, |r| r)

id_from : Surreal.Table(IdFrom)
id_from = Surreal.relation("id_from", customers, products, |r| r)

expect check_of(bad_table(no_id), registry) == "table `no_id` needs a required field `id : Str`; it is the record key"
expect check_of(bad_table(id_int), registry) == "table `id_int` needs a required field `id : Str`; it is the record key"
expect check_of(bad_table(id_optional), registry) == "table `id_optional` needs a required field `id : Str`; it is the record key"
expect check_of(bad_table(big), registry) == "field `n`: U64 does not fit SurrealDB's `int`, which is 64-bit signed"
expect check_of(bad_table(wide), registry) == "field `xs[*].q`: I128 does not fit SurrealDB's `int`, which is 64-bit signed"
expect check_of(bad_table(huge), registry) == "field `h`: U128 does not fit SurrealDB's `int`, which is 64-bit signed"
expect check_of(bad_table(kind_arm), registry) == "field `p`: the arm `A` has a field named `kind`, which tells the arms apart"
expect check_of(bad_table(tuple), registry) == "field `t`: a tuple has no SurrealDB type"
expect check_of(bad_table(tried), registry) == "field `t`: `Builtin.Try` has no SurrealDB type"
expect check_of(bad_table(mapped), registry) == "field `d`: `Builtin.Dict` has no SurrealDB type"
expect check_of(bad_table(spanned), registry) == "field `span`: `Surreal.Duration` has no SurrealDB type"
expect check_of(bad_table(orphan), [Surreal.source(customers)]) == "field `c`: no table holds the row type `{ id : Str, live : Bool, price : Dec, ratio : F64, stock : I32, title : Str }`; list its table in the schema"
expect check_of(bad_table(ref), [Surreal.source(twin_a), Surreal.source(twin_b)]) == "field `c`: tables `twin_a` and `twin_b` have the same row type, so a link to it is ambiguous; make one of the rows a nominal type (`:=`)"
expect check_of(bad_table(empty), registry) == "field `e`: an empty union has no values"
expect check_of(bad_table(wrong_from), registry) == "edge table `wrong_from` needs a required field `from` that is a `Link` to a row of table `customer`"
expect check_of(bad_table(no_to), registry) == "edge table `no_to` needs a required field `to` that is a `Link` to a row of table `product`"
expect check_of(bad_table(id_from), registry) == "edge table `id_from` needs a required field `from` that is a `Link` to a row of table `customer`"
expect check_of(Surreal.source(purchased), registry) == "ok"
expect check_of(Surreal.source(orders), registry) == "ok"

sites_of : Str -> List(Str)
sites_of = |name| match registry.find_first(|s| s.name == name) {
	Ok(s) => Types.link_sites(s.row_ty).map(
		|l| {
			table = match Types.table_for(registry, l.target) {
				Ok(t) => t
				Err(BadSchema(why)) => why
				Err(Unsupported(why)) => why
			}
			"${l.path} top=${l.top} -> ${table} ${if (l.is_id) "id" else "link"} required=${Str.inspect(l.required)} elements=${Str.inspect(l.elements)} ${Str.inspect(l.shape)}"
		},
	)
	Err(_) => ["not listed"]
}

# --------------------------------------------------------------- link sites

expect sites_of("order") == [
	"by top=by -> customer id required=True elements=False Root",
	"customer top=customer -> customer link required=True elements=False Root",
	"gift.to top=gift -> customer link required=False elements=False InObject",
	"items[*].product top=items -> product link required=False elements=False InList",
	"payment.value top=payment -> product link required=False elements=False InUnionArm({ tag: \"Gift\" })",
	"payment.contact top=payment -> customer link required=False elements=False InUnionArm({ tag: \"Invoice\" })",
	"wishlist top=wishlist -> product link required=False elements=True RootList",
]

# The self-link of `Customer` reads back as the table `customer`.
expect sites_of("customer") == ["referrer top=referrer -> customer link required=False elements=False RootOptional"]

expect sites_of("kitchen") == [
	"many top=many -> product link required=False elements=True RootList",
	"maybe top=maybe -> product link required=False elements=False RootOptional",
	"who top=who -> product id required=True elements=False Root",
]

# An edge table lists its two ends as sites too.
expect sites_of("purchased") == [
	"⟨from⟩ top=⟨from⟩ -> customer link required=True elements=False Root",
	"to top=to -> product link required=True elements=False Root",
]

# ---------------------------------------------------------- the registry

expect Types.check_registry(registry) == Ok({})
expect Types.check_registry([Surreal.source(twin_a), Surreal.source(twin_b)]) == Err(BadSchema("tables `twin_a` and `twin_b` have the same row type, so a link to it is ambiguous; make one of the rows a nominal type (`:=`)"))
expect Types.check_registry([Surreal.source(twin_a), Surreal.source(twin_a)]) == Err(BadSchema("two tables are named `twin_a`"))

# A link finds its table whether it reaches the row as a nominal or as a record.
expect Types.table_for(registry, Surreal.source(customers).row_ty) == Ok("customer")
expect Types.table_for(registry, Surreal.source(products).row_ty) == Ok("product")
expect Types.table_for([Surreal.source(products)], Surreal.source(customers).row_ty).is_err()

# The key is the same for the type however it was reached.
expect Types.key(Surreal.source(customers).row_ty) == "N:Customer"
expect Types.key(Surreal.source(products).row_ty) == "{id:Str,live:Bool,price:Dec,ratio:F64,stock:I32,title:Str}"

# A table that is not listed has no definitions.
expect defs_of("missing") == ["not listed"]
