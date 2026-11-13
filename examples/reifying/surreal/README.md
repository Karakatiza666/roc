# A SurrealDB ORM over reified Roc functions

This example has moved. The ORM is now a package of its own:

| | |
| --- | --- |
| Repository | [github.com/Karakatiza666/roc-reify-surrealdb](https://github.com/Karakatiza666/roc-reify-surrealdb) |
| Local checkout | `../../../../roc-reify-surrealdb` from this directory, if you keep the two repos side by side |
| Examples | a veterinary clinic and a monitoring database (script apps), and apps for basic-cli (`client.roc`, `watch.roc`) and basic-webserver (`server.roc`) |
| Compiler | this repo, branch `reify`, at or after commit `846019dd8d` |

The package README has the setup for both platforms, every feature with its
SurrealQL, the rules and limits, and how to run the checks. This page keeps
the part that belongs to this repo: what the package does that only works
because of `Code(f)`. The language feature is described in
[docs/langref/reifying.md](../../../docs/langref/reifying.md).

In short: a function that stands where the type says `Code(f)` is described by
the compiler and passed to the library as data. The library translates the
description to SurrealQL. The function stays an ordinary Roc function, so the
program can call it, test it with `expect`, and compare it with the database.

The snippets below are from the package. The SurrealQL is what its examples
print.

## Rows are the app's records

A row type is a plain Roc record. The same type is the seed data, the schema,
the argument of the app's functions, and the type that a result is decoded at.
Helpers are written over open rows, so one function serves every row that has
the fields it reads (`examples/Clinic.roc`):

```roc
seen_from : { seen : Surreal.Datetime, ..r }, Surreal.Datetime -> Bool
seen_from = |v, at| v.seen >= at

## Seen at or after the parameter `since`.
seen_since : { since : Surreal.Datetime, ..p }, { seen : Surreal.Datetime, ..r } -> Bool
seen_since = |p, v| Clinic.seen_from(v, p.since)

dose_cost : { doses : I64, medication : Surreal.Link({ unit_price : Dec, ..m }), ..d } -> Dec
dose_cost = |d| d.doses.to_dec() * d.medication.get().unit_price

bill : { fee : Dec, items : List({ doses : I64, medication : Surreal.Link({ unit_price : Dec, ..m }), ..d }), ..r } -> Dec
bill = |v| v.fee + v.items.map(|d| Clinic.dose_cost(d)).sum()

recent = |q| q.filter_by(Clinic.seen_since)   # annotated with open rows in the file
```

A query fragment such as `recent` has no single type. Each use that fixes the
row is described at that row (see "Query Fragments" in the language
reference). `examples/main.roc` uses it with a projection that reads links and
calls `bill`:

```roc
visit_line : Visit -> VisitLine
visit_line = |v| { id: v.id, patient: v.patient.get().name, vet: v.vet.get().name, bill: Clinic.bill(v) }

Clinic.by_id(Clinic.recent(Surreal.from(visits)).select(visit_line)).prepare({ since: at("2026-03-01T00:00:00Z") })
```

```surql
LET $since = d'2026-03-01T00:00:00Z';
SELECT fee + math::sum(items.map(|$v1| <decimal>$v1.doses * $v1.medication.unit_price)) AS bill, record::id(id) AS id, patient.name AS patient, vet.name AS vet FROM visit WHERE $since <= seen ORDER BY id;
```

Three helpers that call each other, a field read through a link
(`v.patient.get().name` is `patient.name`), and a parameter record became one
statement. In Roc, `.get()` reads the row that the link holds. In the query it is a
traversal.

A session reads the reply at the Roc type of the query. `session.run!(prepared)`
for a `Prepared(List(VisitLine))` gives `List(VisitLine)`, and a reply that does
not fit is an error.

## Constraints are Roc functions

A constraint is the function that the program already has. The schema builder
takes it as a `Code`, and `expect` runs it in Roc (`examples/main.roc`):

```roc
valid_email : Str -> Bool
valid_email = |email| email.contains("@") and !email.starts_with("@")

expect valid_email("ada@example.org")
expect !valid_email("ada.example.org")

owners.define().assert(|o| o.email, valid_email)   # among other rules
```

```surql
DEFINE FIELD OVERWRITE email ON owner TYPE string ASSERT string::contains($value, '@') AND (!string::starts_with($value, '@'));
```

A rule over several fields is an event, and a `match` is an `IF`
(`examples/main.roc`, `examples/Clinic.roc`):

```roc
fee_covers_items : { fee : Dec, items : List(item), ..r } -> Bool
fee_covers_items = |v| v.items.is_empty() or v.fee > 0

visits.define().check("items need a fee", Clinic.fee_covers_items)   # among other rules

possible_species : Species -> Bool
possible_species = |species| match species {
	Bird(b) => b.wingspan_cm > 0
	_ => Bool.True
}

patients.define().assert(|p| p.species, possible_species)   # among other rules
```

```surql
DEFINE EVENT OVERWRITE visit_check_items_need_a_fee ON visit WHEN $event IN ['CREATE', 'UPDATE'] THEN { IF !(($after.items.len() = 0) OR ($after.fee > 0.0dec)) { THROW 'visit: items need a fee' } };
DEFINE FIELD OVERWRITE species ON patient TYPE { kind: "Bird", wingspan_cm: int } | "Cat" | "Dog" | { kind: "Exotic", latin: string } ASSERT ((IF $value.kind = 'Bird' THEN $value.wingspan_cm >= 0 AND $value.wingspan_cm <= 255 ELSE true END)) AND ((IF $value.kind = 'Bird' THEN $value.wingspan_cm > 0 ELSE true END));
```

The same goes for a computed field, and for a whole Roc function that becomes a
SurrealDB function (`examples/monitoring.roc`):

```roc
fever : Dec, I64 -> Bool
fever = |temp_c, pulse| temp_c > 39.0 or pulse > 120

fever_fn : Surreal.DbFn((Dec, I64 -> Bool))
fever_fn = Surreal.db_fn("fever", fever)

vitals.define().computed(|v| v.fevered, |v| fever_fn.call2(v.temp_c, v.pulse))   # among other rules
Surreal.from(vitals).filter(|v| fever_fn.call2(v.temp_c, v.pulse)).select(vital_line)
```

```surql
DEFINE FUNCTION OVERWRITE fn::fever($a1: decimal, $a2: int) -> bool { RETURN ($a1 > 39.0dec) OR ($a2 > 120) };
DEFINE FIELD OVERWRITE fevered ON vital TYPE bool VALUE fn::fever($this.temp_c, $this.pulse);
SELECT record::id(id)[1] AS at, record::id(id)[0] AS kennel, pulse AS pulse, temp_c AS temp_c FROM vital WHERE fn::fever(temp_c, pulse);
```

One Roc function is the SurrealDB function, the computed field, the filter,
and the function that Roc code calls.

## The same function computes the expected result

Each query in the printed script carries the result that Roc computes with the
same functions over the same rows. The checker sends both to SurrealDB and
compares them (`examples/main.roc`):

```roc
in_city : CityParam, Owner -> Bool
in_city = |p, o| o.address.city == p.city

owners_in_city : Str -> List(OwnerCard)
owners_in_city = |city| seed_owners.keep_if(|o| in_city({ city: city }, o)).map(owner_card)

block(
	"-- query: owners_in_city",
	["-- ordered"],
	Surreal.from(owners).filter_by(in_city).select(owner_card).order_by(|r| r.id, Asc).prepare({ city: "Oslo" }),
	Surreal.Mirror.literal(owners_in_city("Oslo")),
)
```

```surql
-- query: owners_in_city
-- ordered
-- roc: [{ id: 'jon', name: 'Jon Berg', phone: 'none' }, { id: 'mara', name: 'Mara Ito', phone: '555-0142' }]
LET $city = 'Oslo';
SELECT record::id(id) AS id, name AS name, phone ?? 'none' AS phone FROM owner WHERE address.city = $city ORDER BY id;
```

`tests/check.py` runs the statement on a real server, evaluates the `-- roc:`
literal on the same server, and fails if the two differ. The query is written
once. The Roc side is the same function, run by Roc. For live queries, the
`Mirror` predicts the notices of each write in Roc from the same clauses, and
`examples/watch.roc` checks every notice the server sends against it.

## Refactoring does not change the translation

The description is a normal form: two ways to write one computation arrive as
one graph. So a rename, a binding added or reordered, and a helper inlined or
extracted give the same description. `examples/refactored.roc` is
`examples/main.roc` with those changes:

```roc
# main.roc
valid_email = |email| email.contains("@") and !email.starts_with("@")

# refactored.roc
valid_email = |address| {
	not_first = !address.starts_with("@")
	has_at = address.contains("@")
	has_at and not_first
}
```

Its last `expect` compares the whole script with the one `main.roc` prints:

```roc
import "expected_output.surql" as expected_output : Str

expect "${script}\n" == expected_output
```

The two scripts are equal byte for byte. `roc test examples/refactored.roc`
checks it. A string-built query has no such property: each rewrite is a new
query to review.

## Live queries watch what the clauses read

A live query keeps the result of a query current. The library decides what to
watch from the clauses. It does not take a list of tables from the user
(`examples/monitoring.roc`):

```roc
KennelSite : { label : Str, site : Str }

kennel_sites = Surreal.from(kennel_reads).select(|k| { label: k.label, site: k.site.name }).live({}, definitions)
```

```surql
LIVE SELECT VALUE { row: { label: label, site: site.name }, now: true } FROM kennel;
LIVE SELECT VALUE (SELECT VALUE { ref: id, row: { label: label, site: site.name }, now: true } FROM kennel WHERE site = $parent.id) FROM site WHERE $before IS NONE OR $after IS NONE OR $before.name != $after.name;
```

The projection reads `k.site.name`, so the description has a hop from `kennel`
to `site` and names the field `name`. The second statement watches `site`: a
new name of a site is a notice for each kennel that links to it. A write to
another field of `site` sends nothing, because the clause does not read it.
The same walk handles edge tables (`incoming`, `Out` and `In` fields), rows
of other tables read in a clause (`rows()`), and links of links. A link that
no clause reads is not watched.

## Permissions are Roc clauses

A table permission is a function over the row and the record user of the
session (`examples/client.roc`):

```roc
memos.define()
	.permit([Select], |m| m.owner.id() == users.auth() or m.shared)
	.permit([Create, Update, Delete], |m| m.owner.id() == users.auth())
	.permit_field(|m| m.text, [Update], |m| !m.shared)
	.on_delete(users, Cascade)
	.done()
```

```surql
DEFINE TABLE OVERWRITE memo SCHEMAFULL PERMISSIONS FOR select WHERE (owner = $auth.id) OR shared, FOR create, update, delete WHERE owner = $auth.id;
DEFINE FIELD OVERWRITE text ON memo TYPE string PERMISSIONS FOR update WHERE !shared;
```

The row is the memo's own record type. `users.auth()` is `$auth.id`, and a
clause of a query can read it the same way. A read of a field the memo does
not have is a type error, as in any Roc function, not a rule that fails at run
time.

## A translator extension is keyed by the function's identity

The translator cannot know a type that an app or another package defines.
`Temperature` in `tests/Temperature.roc` is an opaque type with no SurrealDB
in it. An extension gives the SurrealQL of its functions, keyed by
`Code.prim`, the id the compiler gives each definition
(`tests/ExtensionTest.roc`):

```roc
temperature_surreal : Surreal.Extension
temperature_surreal = Surreal.extension(
	{
		prims: [
			{ prim: Code.prim(Temperature.from_celsius), render: only },
			{ prim: Code.prim(Temperature.celsius), render: only },
			{ prim: Code.prim(Temperature.is_gt), render: binary(">") },
		],
	},
)

fever : Temperature -> Try(Surreal.Prepared(List(Reading)), Ql.Error)
fever = |limit| Surreal.bind_captured(Surreal.select_where_with(readings, [temperature_surreal], |r| Temperature.from_celsius(r.temp_c) > limit))
```

`fever(Temperature.from_celsius(38.5))` is:

```surql
LET $_1 = 38.5dec;
SELECT record::id(id) AS id, patient, temp_c FROM reading WHERE (temp_c > $_1);
```

The id is the definition, not its name. `Temperature.is_gt` and `Dec.is_gt`
are two ids (`expect Code.prim(Temperature.is_gt) != Code.prim(Dec.is_gt)`), so
a `>` on two temperatures is refused without the extension, and is never read
as the builtin `>`. The extension is a value, and a glue package can export it.
The language reference describes this under
[Extending a Translator](../../../docs/langref/reifying.md#extending-a-translator).

## Where the rest is

The package README lists every feature, with the rules that the translator
follows, the refusals it reports, and its design limits. It also has a
"Findings" section: what the package could not do ergonomically with the
language, which was fed back into the compiler's structural proposal
(`roc-reify-structural-proposal.md` in this repo).
