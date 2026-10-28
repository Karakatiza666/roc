# A SurrealDB ORM over reified Roc functions

Row types are plain Roc records. A table is a `Surreal.Table(row)` over one.
Every query clause, every projection and every database constraint is a Roc
function over that record. The builder takes the function as a `Code(f)`, so
the compiler describes it, and `Translate.roc` turns the description into
SurrealQL. The same records are the seed data, the arguments of the
application's own functions, and the inputs of its tests.

`roc main.roc` prints one SurrealQL script: the schema, the seed rows, the
queries, the writes the database must refuse, and the writes it must accept.
`check.py` runs it on a real server and compares each query with the result
that Roc computes from the same functions over the same rows.

| File | What it is |
| --- | --- |
| `package.roc` | The package header. It exposes `Surreal`. |
| `Surreal.roc` | The public API: ids, links, datetimes, tables, the schema builder, queries and writes. Also the package functions for SurrealDB (`Text`, `Hash`, `Array`, `Time`, `Math`, `Rand`). |
| `Translate.roc` | The translator. A `Code` graph in, a SurrealQL expression out. |
| `Schema.roc` | `DEFINE` statements from row types and builder clauses. It also writes the delete policy of every link. |
| `Types.roc` | Roc types as SurrealDB types, the `BadSchema` checks, and the list of link sites of a row. |
| `Encode.roc` | The format that the derived `encoder_for` runs against. It turns a row into a SurrealQL literal. |
| `Ql.roc` | SurrealQL text: values, quoting, identifiers and the error type. |
| `main.roc` | A veterinary clinic: rows, constraints, seeds, queries, writes, and the script. |
| `builtins.roc` | Tables with seed rows for the builtin mappings and for the package functions (`Text`, `Hash`, `Array`, `Time`, `Math`, `Rand`, `Id.table`). It prints its own script, with a Roc result for each of its 38 queries and writes. |
| `refactored.roc` | `main.roc` with the parameters of the reified functions renamed and bindings added, reordered, inlined and extracted. It prints `expected_output.surql` byte for byte, which its last `expect` checks. |
| `TypesTest.roc` | Tests of `Types` and the table constructors on a small domain. |
| `TranslateTest.roc` | Tests of the translator, one per kind of clause. |
| `SchemaTest.roc` | Tests of the schema builder and of the link policies. |
| `QueriesTest.roc` | Tests of queries, parameters, captured values and writes. |
| `check.py` | Runs the scripts of `main.roc` and `builtins.roc` on SurrealDB and compares every block. Python standard library only. |
| `expected_output.surql` | What `roc main.roc` prints. |

## Run it

There is no public SurrealDB endpoint to run against. Surrealist's sandbox
runs in the browser as WASM, so it has no address that a script can reach.
The example runs against a local server instead:

```
docker run --rm -d --name surreal-roc -p 8000:8000 surrealdb/surrealdb:v3.3.4 start --user root --pass root memory
```

```
roc examples/reifying/surreal/main.roc                  # the SurrealQL script
roc examples/reifying/surreal/main.roc | diff - examples/reifying/surreal/expected_output.surql
roc examples/reifying/surreal/builtins.roc              # the SurrealQL script of the builtin rows
roc test examples/reifying/surreal/main.roc             # the expects of main.roc and of the modules it imports
roc test examples/reifying/surreal/builtins.roc         # the expects of builtins.roc
roc test examples/reifying/surreal/refactored.roc       # the same, and the script is expected_output.surql
roc test examples/reifying/surreal/TypesTest.roc
roc test examples/reifying/surreal/TranslateTest.roc
roc test examples/reifying/surreal/SchemaTest.roc
roc test examples/reifying/surreal/QueriesTest.roc
python3 examples/reifying/surreal/check.py              # run both scripts on SurrealDB 3.3.4, compare with Roc
```

`check.py` runs `main.roc` and then `builtins.roc` in one fresh database, and it reads `SURREAL_URL` (default `http://localhost:8000`),
`SURREAL_USER` and `SURREAL_PASS` (default `root`). It prints one line for
each block and exits with 0 when all blocks agree. It removes and creates its own database at the start.

| Block header | What the checker does |
| --- | --- |
| `-- schema`, `-- seed: T` | Every statement must succeed. |
| `-- query: N`, `-- write: N` | The last statement result must equal the `-- roc:` literal. `-- ordered` keeps the order. Without it, the rows are compared as a multiset. |
| `-- rejects: N` | Some statement must fail, and its error must contain the `-- error:` text. |

The `-- roc:` literal is a SurrealQL value that Roc printed. The checker sends
`RETURN <literal>` to the same server, so both sides use one serialiser.
It asks for CBOR, not JSON. JSON prints a decimal as a string, so the decimal
`42` and the string `"42"` look the same. CBOR tags a decimal, so the checker
treats a number-like string as a string, and only a tagged decimal is
compared as a decimal. A string field `"42"` against the number `42` fails.

## What it covers

The first rows are the three headline features: constraints of each kind, links
in nested fields with the same constraints as top-level ones, and unions as
Roc tag unions with `match` in a query.

| Feature | Roc | SurrealQL | Where |
| --- | --- | --- | --- |
| Check over one field | `.check("weight above zero", \|p\| p.weight_kg > 0)` | `weight_kg ... TYPE decimal ASSERT $value > 0.0dec` | `main.roc:385` |
| Check over several fields | `.check("items need a fee", fee_covers_items)` | `DEFINE EVENT ... ON visit WHEN $event IN ['CREATE', 'UPDATE'] THEN { IF !(..) { THROW 'visit: items need a fee' } }` | `main.roc:398` |
| Check on an edge table | `.check("since a real year", \|e\| e.since_year >= 1990)` | `since_year ON treats TYPE int ASSERT $value >= 1990` | `main.roc:408` |
| Assert on a field, with a function the program also calls | `.assert(\|o\| o.email, valid_email)` | `ASSERT string::contains($value, '@') AND (!string::starts_with($value, '@'))` | `main.roc:354` |
| Assert on a nested path, with a SurrealDB function | `.assert(\|v\| v.contact.email, \|e\| Surreal.Text.is_email(e))` | `DEFINE FIELD contact.email ON vet TYPE string ASSERT string::is_email($value)` | `main.roc:366` |
| Assert on each element | `.assert_each(\|o\| o.tags, \|t\| t != "")` | `tags ... ASSERT $value.all(\|$item\| $item != '')` | `main.roc:355` |
| Assert on a field of each record in a list | `.assert_each(\|v\| v.items, positive_doses)` | `items[*].doses ON visit TYPE int ASSERT $value > 0` | `main.roc:396` |
| Assert on a union | `.assert(\|p\| p.species, possible_species)` | `species ... ASSERT (IF $value.kind = 'Bird' THEN $value.wingspan_cm > 0 ELSE true END)` | `main.roc:383` |
| Unique, with a nested path | `.unique(\|v\| v.contact.email)` | `DEFINE INDEX ... ON vet FIELDS contact.email UNIQUE` | `main.roc:365` |
| Unique, over several fields and a link | `.unique(\|p\| { name: p.name, owner: p.owner })` | `DEFINE INDEX ... ON patient FIELDS name, owner UNIQUE` | `main.roc:382` |
| Unique, over the ends of an edge | `.unique(\|e\| { from: e.from, to: e.to })` | `DEFINE INDEX ... ON treats FIELDS in, out UNIQUE` | `main.roc:409` |
| Index | `.index(\|o\| o.address.city)` | `DEFINE INDEX ... ON owner FIELDS address.city` | `main.roc:358` |
| Default value | `.default(\|o\| o.tags, [])` | `tags ... TYPE array<string> DEFAULT []` | `main.roc:357` |
| Computed field | `.computed(\|m\| m.label, \|m\| label_of(m.name, m.form))` | `label ON medication TYPE string VALUE $this.name + ' (' + $this.form + ')'` | `main.roc:375` |
| Read-only field | `.readonly(\|v\| v.license)` | `license ON vet TYPE string READONLY ASSERT ..` | `main.roc:368` |
| Range from the Roc type | `Vet : VetRow(U8)`, `stock : I32` | `years ... TYPE int ASSERT $value >= 0 AND $value <= 255` | `main.roc:35` |
| Link in an optional object | `chip ?: { code : Str, implanted_by : Surreal.Link(Vet) }` | `chip.implanted_by ... TYPE record<vet> ASSERT record::exists($value)`, and an event on `vet` that throws on delete | `main.roc:52` |
| Link in a list of records | `vaccines : List({ name : Str, given : Str, vet : Surreal.Link(Vet) })` | `vaccines[*].vet ... TYPE record<vet> ASSERT record::exists($value)`, and an event on `vet` | `main.roc:49` |
| Link in a list of records, second site | `items : List({ medication : Surreal.Link(Medication), doses : I64 })` | `items[*].medication ... ASSERT record::exists($value)`, and an event on `medication` | `main.roc:66` |
| Link in a union arm | `Referred({ to : Surreal.Link(Vet), reason : Str })` | `IF $value.kind = 'Referred' THEN record::exists($value.to) ELSE true END`, and an event on `vet` | `main.roc:69` |
| Optional link to a row of the same table | `referred_by ?: Surreal.Link(Owner)` in `Owner := { .. }`, `.on_delete(owners, Unset)` | `referred_by ON owner TYPE option<record<owner>> REFERENCE ON DELETE UNSET ASSERT ($value = NONE OR (record::exists($value)))` | `main.roc:23` |
| Top-level link, same constraints | `owner : Surreal.Link(Owner)`, `.on_delete(owners, Cascade)` | `owner ... TYPE record<owner> REFERENCE ON DELETE CASCADE ASSERT record::exists($value)` | `main.roc:388` |
| Top-level list of links, per-path policy | `allergies : List(Surreal.Link(Medication))`, `.on_delete_at(\|p\| p.allergies, Unset)` | `allergies ... TYPE array<record<medication>> ... REFERENCE ON DELETE UNSET` | `main.roc:390` |
| A write that names a missing target is refused at every depth | `patients.create(ghost_chip_patient)`, and one row for each other shape | `ASSERT record::exists($value)` fails for the field `chip.implanted_by` | `main.roc:879` |
| A delete of a target in use is refused at every depth | `vets.delete(\|v\| v.id == "tia")` | the event throws: `is referenced by visit.outcome.to` | `main.roc:883` |
| A tag union is a literal union | `Species : [Dog, Cat, Bird({ wingspan_cm : U8 }), Exotic({ latin : Str })]` | `TYPE { kind: "Bird", wingspan_cm: int } \| "Cat" \| "Dog" \| { kind: "Exotic", latin: string }` | `main.roc:46` |
| `match` in a projection | `species_label(p.species)` with `match` on `Dog`, `Cat`, `Bird(_)`, `Exotic(other)` | `(IF species.kind = 'Bird' THEN 'bird' ELSE IF species = 'Cat' THEN 'cat' ELSE IF species = 'Dog' THEN 'dog' ELSE species.latin END)` | `main.roc:123` |
| `match` in a filter | `wide_wings(p)` reads the wingspan of `Bird(wings)` | `WHERE (IF species.kind = 'Bird' THEN species.wingspan_cm >= 20 ELSE false END)` | `main.roc:148` |
| `match` that reads a link in an arm | `Referred(r) => "referred to ${r.to.get().name}"` | `'referred to ' + outcome.to.name` | `main.roc:134` |
| `match` on an optional object | `match p.?chip { Ok(c) => .., Err(_) => .. }` | `(IF chip IS NONE THEN 'nobody' ELSE chip.implanted_by.name END)` | `main.roc:452` |
| A union in a write | `{ ..v, years: v.years + 1, specialty: Surgery({ board: "ECVS" }) }` | `UPDATE vet SET specialty = { kind: 'Surgery', board: 'ECVS' }, years = years + 1 WHERE ..` | `main.roc:545` |
| A parameter record | `filter_by(in_city)`, `.bind({ city: "Oslo" })` | `LET $city = 'Oslo'; .. WHERE address.city = $city` | `main.roc:417` |
| Optional field with `??` | `o.?phone ?? "none"` | `phone ?? 'none'` | `main.roc:423` |
| `.?` on an optional self-link | `match o.?referred_by { Ok(r) => r.get().name, Err(_) => "nobody" }` | `(IF referred_by IS NONE THEN 'nobody' ELSE referred_by.name END)` | `main.roc:431` |
| A link read with `get()` | `p.owner.get().name` | `owner.name` | `main.roc:444` |
| A link compared by id | `v.vet.id() == ruth_id` | `$v1.vet = vet:⟨ruth⟩` | `main.roc:469` |
| `fetch` of links | `.fetch(\|p\| p.owner).fetch_each(\|p\| p.vaccines.map(\|v\| v.vet))` | `FETCH owner, vaccines[*].vet` | `main.roc:835` |
| Graph traversal | `.outgoing(treats)`, `.incoming(treats)` with `edges.keep_if(..).len()` | `->treats.len()`, `<-treats.filter(\|$v1\| $v1.primary).map(..)` | `main.roc:799` |
| A count as `I64` | `edges.len().to_i64_wrap()` | `->treats.len()` (the conversion is the identity) | `main.roc:493` |
| Group and aggregate | `.group_by(\|v\| v.vet.get().name).aggregate(ledger_line)` | `math::sum(fee) AS revenue, count() AS visits .. GROUP BY vet.name` | `main.roc:811` |
| A statistic over a group | `avg_fee: Surreal.Math.mean(rows.map(\|v\| v.fee.to_f64()))` in `ledger_line` | `math::mean(<float>fee) AS avg_fee .. GROUP BY vet.name` | `main.roc:504` |
| The database clock in a read | `.filter(\|v\| v.seen < Surreal.Time.now())` | `WHERE seen < time::now()` | `main.roc:785` |
| A helper that the program also calls | `bill(v)` in `visit_line` | `fee + math::sum(items.map(\|$v1\| <decimal>$v1.doses * $v1.medication.unit_price))` | `main.roc:145` |
| A captured run-time value | `cheaper_than(limit)`, with `select_where(medications, \|m\| m.unit_price < limit)` | `LET $_1 = 0.9dec; SELECT * FROM medication WHERE unit_price < $_1` | `main.roc:514` |
| Order, limit and start | `.order_by(\|r\| r.id, Asc).limit(2).start(2)` | `ORDER BY id LIMIT 2 START 2` | `main.roc:829` |
| Update and delete with a parameter | `medications.update_by(low_stock, refill)`, `visits.delete_by(too_old)` | `UPDATE medication SET stock = stock + $add WHERE stock < $floor`, `DELETE visit WHERE seen < $before` | `main.roc:924` |
| Seeds through the derived encoder | `vets.insert(seed_vets)`, `treats.insert(seed_treats)` | `INSERT INTO vet [..]`, `INSERT RELATION INTO treats [..]` | `main.roc:851` |
| Writes the database must refuse | ``rejects("check_as_assert", "field `weight_kg`", patients.create(light_patient))`` | the check reports a failed statement | `main.roc:861` |

`check.py` runs the whole script with the Roc result next to each query. A
query and its Roc result use the same functions: `owner_card`, `pet_line`,
`case_load`, `ledger_line` and the others run over the seed rows in the program
(`main.roc:734`), and over the stored rows in the database. The checker tests
that the two results agree.

## How it is built

A clause is a function over the row. The translator reads the root row of its
`Code` graph as a tree and evaluates the tree (`Translate.roc:406`).
Each parameter is bound to what it stands for in SurrealQL. A node that the
tree keeps as a definition is evaluated once, where its block defines it.

| Binding | Stands for | A field read off it is |
| --- | --- | --- |
| `Row` at `Doc` | The record a statement runs over: `""`, `$after` in an event, `$this` in a field | A path: `address.city` |
| `Row` at `Ref` | The record behind a link after `get()`, or an edge `$v1` | A path through the record: `owner.name` |
| `Row` at `Obj` | An object inside a record | A path |
| `Pair(l, r)` | A row and its edge list from `outgoing` or `incoming` | Nothing. `.0` and `.1` pick a side (`Translate.roc:499`) |
| `ListOf` | A list at a path, or the edges `->t` | Nothing. A list operation makes a closure over `$v1`, `$v2` (`Translate.roc:1174`) |
| `Union` | A tag-union value | Nothing. A `match` is an `IF .. THEN .. END` (`Translate.roc:645`) |
| `Maybe` | A read of an optional field | Nothing. `??`, `is_ok` and `match` test it for `NONE` |
| `Params` | The parameter record of a `filter_by` | The variable `$name` |
| `Group` | The rows of a group | Nothing. `len`, `keep_if(..).len()` and `map(..).sum()` aggregate it (`Translate.roc:1132`) |
| `Column` | `rows.map(f)` over a `Group`: the expression `f` reads | Nothing. Each aggregate (`sum`, `mean`, `median`, `stddev`, `variance`) writes its own call, so one `map` may feed several (`Translate.roc:1156`) |
| `Moment` | The text of a datetime, which is how the derived `==` on a `Datetime` arrives | Not a record. `==` compares the datetimes (see below) |
| `Expr`, `Infix` | The text of a scalar. `Infix` needs parentheses as an operand | Not a record |
| `Fields` | A record that the body built | The binding of that field |

A call to one of the application's own functions is a `Call` of another row
of the same graph. The translator expands it with that row's parameters bound
the same way (`Translate.roc:1213`). A function that calls itself is
refused. The builtins and the cut functions a clause may call are rows of one
table (`Translate.roc:735`, `Translate.roc:755`). The functions of `Surreal.Text`, `Hash`, `Array`, `Time`, `Math` and `Rand` are rows of a second table (`Translate.roc:930`, `Translate.roc:993`). A row maps a builtin only when
SurrealDB 3.3.4 gives the same result as Roc. `builtins.roc` checks the risky
rows on a live server.

### Supported builtins

`s` is a string, `n` and `m` are integers, `d` is a `Dec`, `list` is a list field.

| Roc builtin | SurrealQL | Note |
| --- | --- | --- |
| `a + b`, `"${a}${b}"`, `s.is_empty()`, `a == b`, `a < b` | `a + b`, `s = ''`, `a = b`, `a < b` | |
| `s.starts_with(x)`, `ends_with`, `contains` | `string::starts_with(s, x)` and the same for the others | |
| `s.with_ascii_uppercased()`, `with_ascii_lowercased` | `array::join(string::split(s, '').map(\|$ch\| IF $ch >= 'a' AND $ch <= 'z' THEN string::uppercase($ch) ELSE $ch END), '')` | `string::uppercase` also changes `ß` and `é`, and Roc does not |
| `s.caseless_ascii_equals(x)` | Both sides lowercased as above, then `=` | |
| `s.trim()`, `trim_start`, `trim_end` | `string::replace(s, /^[\s\u{200E}\u{200F}]+\|[\s\u{200E}\u{200F}]+$/, '')` | `string::trim` keeps U+200E and U+200F |
| `s.repeat(n)`, `s.with_prefix(p)`, `Str.join_with(list, x)` | `string::repeat(s, n)`, `p + s`, `array::join(list, x)` | |
| `s.drop_prefix(p)`, `drop_suffix` | `IF string::starts_with(s, p) THEN string::slice(s, string::len(p)) ELSE s END` | |
| `s.split_on(x)` | `string::split(s, x)` | An empty `x` gives `[s]` in Roc. A literal `""` is read at translation. Another `x` gets an `IF x = ''` guard |
| `s.replace_each(a, b)` | `string::replace(s, a, b)` | An empty `a` gives `s` in Roc. Same literal rule and guard |
| `s.count_utf8_bytes()` | `bytes::len(<bytes>s)` | `string::len` counts characters |
| `s.to_str()`, `n.to_str()` | `s`, `<string>n` | |
| `n.max(m)`, `n.min(m)` (also `Dec`) | `math::max([n, m])`, `math::min([n, m])` | |
| `n.pow(m)` | `math::pow(n, m)` | |
| `n.mod_by(m)` | `(((n % m) + m) % m)` | Floored modulus, as Roc |
| `n.is_multiple_of(m)` | `n % m = 0` | A divisor that is not a non-zero literal gets `IF m = 0 THEN n = 0 ELSE ..` |
| `n.is_zero()`, `is_negative`, `is_positive` (also `Dec`) | `n = 0`, `n < 0`, `n > 0` | |
| `n.is_even()`, `n.is_odd()` | `n % 2 = 0`, `n % 2 != 0` | |
| `d.round()` | `IF d >= 0 THEN math::floor(d + 0.5dec) ELSE math::ceil(d - 0.5dec) END` | `math::round` rounds a tie to even, and Roc rounds it away from zero |
| `d.floor()`, `d.ceiling()`, `d.trunc()` | `math::floor(d)`, `math::ceil(d)`, `IF d >= 0 THEN math::floor(d) ELSE math::ceil(d) END` | No `math::trunc` in SurrealDB |
| `n.to_i64()`, `to_i128`, `to_u32` and other conversions without a check | `n` | An integer is an `int` already. Integer owners only |
| `n.to_u8_try()` and the other `to_<int>_try` | `Maybe(IF n >= 0 AND n <= 255 THEN n ELSE NONE END)` | |
| `d.to_i64_try()` | `Maybe(IF d > -9223372036854775809dec AND d < 9223372036854775808dec THEN <int>(trunc) ELSE NONE END)` | Roc cuts the fraction, then tests the range |
| `n.to_dec()`, `n.to_f64()` | `<decimal>n`, `<float>n` | |
| `list.len()`, `list.is_empty()`, `list.contains(x)` | `list.len()`, `list.len() = 0`, `list CONTAINS x` | |
| `list.any(f)`, `all`, `map`, `keep_if`, `drop_if`, `count_if`, `find_first` | `list.any(\|$v1\| ..)`, `.all`, `.map`, `.filter`, `.find` | |
| `list.map(f).sum()` | `math::sum(list.map(\|$v1\| ..))` | |
| `list.first()`, `last`, `get(i)`, `min`, `max` | `array::first(list)`, `array::last`, `array::at(list, i)`, `array::min`, `array::max` | A `Try` is a `Maybe`: `NONE` stands for `Err`. `math::max([])` is `NULL`, so it is not used |
| `list.take_first(n)`, `drop_first(n)`, `rev()`, `join()` | `array::slice(list, 0, n)`, `array::slice(list, n)`, `array::reverse`, `array::flatten` | |
| `list.concat(l)`, `append(x)`, `prepend(x)`, `list == l` | `array::concat`, `array::append`, `array::prepend`, `list = l` | |
| `t.is_ok()`, `t.is_err()`, `t.ok_or(x)`, `t ?? x` | `t IS NOT NONE`, `t IS NONE`, `t ?? x` | `t` comes from an optional field or a `Try` row above |
| `link.get()`, `link.id()` | A traversal of the stored record id, and the id itself | |
| `id.key()` | `record::id(id)` | |
| `a < b` on a `Datetime` | `a < b`, with the literal written as `d'..'` | |
| `a == b`, `a != b` on a `Datetime` | `a = b`, `a != b`, with the literal written as `d'..'` | Compared as datetimes, never as text: SurrealDB prints a fraction with 3, 6 or 9 digits (`.500Z`), and Roc without trailing zeros (`.5Z`). The text of a datetime is compared only with a datetime or a literal (`Translate.roc:914`) |

A `Try` builtin maps only when the error has one tag and SurrealQL gives
`NONE`, not `NULL`, for it. A `match` writes the `Ok` expression again in each arm.

### Refused builtins

| Roc builtin | Reason |
| --- | --- |
| `from_str` on `I64`, `Dec`, `F64` | Roc accepts `1_0`, `0x1f` and `1e3`. `<int>` raises an error and does not give `NONE` |
| `to_i64`, `to_i64_wrap` on `Dec` or `F64` | Roc cuts the fraction. `<int>` raises an error. Use `to_i64_try` |
| `to_str` on `Dec`, `F32`, `F64` | Roc prints `3.0`, SurrealDB prints `3` or `3f` |
| `pow` on `Dec`, and `max`, `min`, `pow`, sign tests on `F32`, `F64` | Digits, NaN and -0.0 differ |
| `//` on `Dec` | Roc cuts the fraction. Divide with `/` |
| `replace_first`, `replace_last` | `string::replace` replaces every match |
| `Str.len` | The Roc type gives only an error |
| `split_first`, `split_last`, `to_utf8`, `from_utf8`, `drop_first_bytes` | A record result in a `Try`, or a byte list |
| `div_floor_by`, `div_ceil_by`, `abs_diff`, shifts, `bitwise_*`, `to_<int>_wrap`, narrowing `to_<int>_wrap`, `*_saturated` | No SurrealQL function with the same meaning |
| `div_try` | Two error tags, and a `Maybe` cannot tell them apart |
| `sort`, `fold`, `map_try`, `split_*`, `chunks_of` | No SurrealQL form |

A refused builtin is a translation error with the reason, never a wrong query.

### Package functions

SurrealDB has functions that Roc has no builtin for. They are functions of one
nominal for each namespace, inside `Surreal`: `Text`, `Hash`, `Array`, `Time`, `Math`
and `Rand` (from `Surreal.roc:241`). A call is written `Surreal.Text.is_email(s)`. The nominal has
no value, so it is not a method of `Str`. The name is `Text` and not `Str`,
because a nominal named `Str` shadows the builtin in the whole module. In the
tables below `Datetime` is `Surreal.Datetime`.

A function is in the cut (`Surreal.code_primitives`), so the reifier does not read
its body and the translator maps it to one SurrealQL function (the `functions`
table, `Translate.roc:930`). It has one of two kinds of body, and no third:

| Kind | Body | Where a call runs |
| --- | --- | --- |
| Mirror | A real Roc implementation that gives the SurrealDB result. A live block proves it equal | In a clause (as SurrealQL) and in Roc: an `expect`, seed data and the `-- roc:` reference |
| Database only | `crash "Surreal.Text.is_email runs in the database only"` | In a clause only. A call outside a clause stops the program with that message |

A stand-in that gives a plausible value is not allowed: it would give a wrong
answer without a message. A database-only function has no Roc result, so its
live block has the expected rows written by hand next to the seed rows
(`builtins.roc`). The cut lists must hold the same names in every nominal that
takes a `Code` parameter. `check_cuts.py` compares them, and `check.py` runs it
first.

#### `Text`

`is_alpha`, `is_alphanum` and `is_numeric` are Unicode: `abé` is alphabetic and
the Arabic digits `١٢٣` are numeric. An empty text is false for every `is_*` check.
`matches` takes Rust regex syntax, and a pattern that is not anchored finds a
part of the text. `distance_normalized_levenshtein` is a similarity: 1 for equal
texts. The distances count characters, not bytes.

| Roc | Type | SurrealQL | Kind | Live block |
| --- | --- | --- | --- | --- |
| `Text.is_email` | `Str -> Bool` | `string::is_email(a)` | database only | text_checks |
| `Text.is_url` | `Str -> Bool` | `string::is_url(a)` | database only | text_checks |
| `Text.is_domain` | `Str -> Bool` | `string::is_domain(a)` | database only | text_checks |
| `Text.is_ip` | `Str -> Bool` | `string::is_ip(a)` | database only | text_addresses |
| `Text.is_ipv4` | `Str -> Bool` | `string::is_ipv4(a)` | database only | text_addresses |
| `Text.is_ipv6` | `Str -> Bool` | `string::is_ipv6(a)` | database only | text_addresses |
| `Text.is_uuid` | `Str -> Bool` | `string::is_uuid(a)` | database only | text_identifiers |
| `Text.is_ulid` | `Str -> Bool` | `string::is_ulid(a)` | database only | text_identifiers |
| `Text.is_semver` | `Str -> Bool` | `string::is_semver(a)` | database only | text_identifiers |
| `Text.is_alpha` | `Str -> Bool` | `string::is_alpha(a)` | database only | text_unicode |
| `Text.is_alphanum` | `Str -> Bool` | `string::is_alphanum(a)` | database only | text_unicode |
| `Text.is_numeric` | `Str -> Bool` | `string::is_numeric(a)` | database only | text_unicode |
| `Text.is_latitude` | `Str -> Bool` | `string::is_latitude(a)` | database only | text_places |
| `Text.is_longitude` | `Str -> Bool` | `string::is_longitude(a)` | database only | text_places |
| `Text.is_datetime` | `Str, Str -> Bool` | `string::is_datetime(a, b)` | database only | text_dates |
| `Text.matches` | `Str, Str -> Bool` | `string::matches(a, b)` | database only | text_pattern |
| `Text.similarity_jaro` | `Str, Str -> F64` | `string::similarity::jaro(a, b)` | database only | text_similarity |
| `Text.similarity_jaro_winkler` | `Str, Str -> F64` | `string::similarity::jaro_winkler(a, b)` | database only | text_similarity |
| `Text.distance_levenshtein` | `Str, Str -> I64` | `string::distance::levenshtein(a, b)` | database only | text_distance |
| `Text.distance_damerau_levenshtein` | `Str, Str -> I64` | `string::distance::damerau_levenshtein(a, b)` | database only | text_distance |
| `Text.distance_normalized_levenshtein` | `Str, Str -> F64` | `string::distance::normalized_levenshtein(a, b)` | database only | text_distance |
| `Text.is_ascii` | `Str -> Bool` | `string::is_ascii(a)` | mirror | text_unicode |
| `Text.is_hexadecimal` | `Str -> Bool` | `string::is_hexadecimal(a)` | mirror | text_unicode |

#### `Hash`

The hash of a text is lower-case hex. Password hashes (`argon2`, `bcrypt`,
`scrypt`, `pbkdf2`) are not included (see the dropped functions below).

| Roc | Type | SurrealQL | Kind | Live block |
| --- | --- | --- | --- | --- |
| `Hash.sha256` | `Str -> Str` | `crypto::sha256(a)` | mirror | hashes |
| `Hash.blake3` | `Str -> Str` | `crypto::blake3(a)` | mirror | hashes |
| `Hash.md5` | `Str -> Str` | `crypto::md5(a)` | database only | hashes_old |
| `Hash.sha1` | `Str -> Str` | `crypto::sha1(a)` | database only | hashes_old |
| `Hash.sha512` | `Str -> Str` | `crypto::sha512(a)` | database only | hashes_old |

#### `Array`

The functions take lists of values that have `is_eq`. They keep the first place
of a value, as SurrealDB does: `distinct([3, 1, 3, 2, 1])` is `[3, 1, 2]`.
`complement(a, b)` is the values of `a` that `b` has not. It is not
`array::difference`, which is a symmetric difference.

| Roc | Type | SurrealQL | Kind | Live block |
| --- | --- | --- | --- | --- |
| `Array.distinct` | `List(a) -> List(a)` | `array::distinct(a)` | mirror | arrays |
| `Array.union` | `List(a), List(a) -> List(a)` | `array::union(a, b)` | mirror | arrays |
| `Array.intersect` | `List(a), List(a) -> List(a)` | `array::intersect(a, b)` | mirror | arrays |
| `Array.complement` | `List(a), List(a) -> List(a)` | `array::complement(a, b)` | mirror | arrays |

#### `Time` and `Duration`

A `Duration` is `Duration := { nanos : U64 }`, a `U64` because SurrealDB refuses
a negative duration. The constructors are plain Roc, not in the cut. A call is
inlined, and one rule in `Translate.wrap` writes `duration::from_nanos(N)`:

| Roc | Type | Nanoseconds |
| --- | --- | --- |
| `Time.nanos`, `micros`, `millis`, `secs`, `mins`, `hours`, `days`, `weeks` | `U64 -> Duration` | 1, 1000, 1000000, 10^9, 6 * 10^10, 3.6 * 10^12, 8.64 * 10^13, 6.048 * 10^14 |

A `Duration` is not a column type and not a captured value (both are refused
with a message). Every part of a time is read in UTC, as the library keeps every
`Datetime`. `Time.unix` counts seconds, `unix_millis` milliseconds, `unix_micros`
microseconds and `nano` nanoseconds since 1970, each rounded down. The two
extractors are `unix_millis` and `unix_micros` because `Time.millis` and
`Time.micros` already make a `Duration`. `wday` is Monday 1 to Sunday 7, `week`
is the ISO week, and `yday` counts from 1.

| Roc | Type | SurrealQL | Kind | Live block |
| --- | --- | --- | --- | --- |
| `Time.now` | `() -> Datetime` | `time::now()` | database only | now_filter, now_future |
| `Time.floor` | `Datetime, Duration -> Datetime` | `time::floor(a, b)` | database only | time_buckets |
| `Time.ceil` | `Datetime, Duration -> Datetime` | `time::ceil(a, b)` | database only | time_buckets |
| `Time.round` | `Datetime, Duration -> Datetime` | `time::round(a, b)` | database only | time_buckets |
| `Time.group` | `Datetime, [Year, Month, Day, Hour, Minute, Second] -> Datetime` | `time::group(t, 'month')` | database only | time_group |
| `Time.plus` | `Datetime, Duration -> Datetime` | `t + d` | database only | time_plus |
| `Time.minus` | `Datetime, Duration -> Datetime` | `t - d` | database only | time_plus |
| `Time.wday` | `Datetime -> I64` | `time::wday(a)` | database only | time_calendar |
| `Time.yday` | `Datetime -> I64` | `time::yday(a)` | database only | time_calendar |
| `Time.week` | `Datetime -> I64` | `time::week(a)` | database only | time_calendar |
| `Time.unix` | `Datetime -> I64` | `time::unix(a)` | database only | time_epoch |
| `Time.unix_millis` | `Datetime -> I64` | `time::millis(a)` | database only | time_epoch |
| `Time.unix_micros` | `Datetime -> I64` | `time::micros(a)` | database only | time_epoch |
| `Time.nano` | `Datetime -> I64` | `time::nano(a)` | database only | time_epoch |
| `Time.format` | `Datetime, Str -> Str` | `time::format(a, b)` | database only | time_format |
| `Time.from_unix` | `I64 -> Datetime` | `time::from_unix(a)` | database only | time_from_unix |
| `Time.year` | `Datetime -> I64` | `time::year(a)` | mirror | time_parts |
| `Time.month` | `Datetime -> I64` | `time::month(a)` | mirror | time_parts |
| `Time.day` | `Datetime -> I64` | `time::day(a)` | mirror | time_parts |
| `Time.hour` | `Datetime -> I64` | `time::hour(a)` | mirror | time_parts |
| `Time.minute` | `Datetime -> I64` | `time::minute(a)` | mirror | time_parts |
| `Time.second` | `Datetime -> I64` | `time::second(a)` | mirror | time_parts |

#### `Math`

The statistics take `List(F64)` and give `F64`. SurrealDB's result type depends
on the element type (an `int` array has a `float` mean, a `decimal` array has a
`decimal` one), and a Roc signature cannot say that. Convert an `I64` or `Dec`
field with `to_f64()`, which the translator writes as `<float>`. Over a group's
rows the same call is an aggregate: `Math.mean(rows.map(|v| v.fee.to_f64()))` is
`math::mean(<float>fee)`. `percentile` is refused over a group, because
SurrealDB gives `NULL` there. The mean of a list with no value is not a number.
`stddev` and `variance` are the sample ones.

| Roc | Type | SurrealQL | Kind | Live block |
| --- | --- | --- | --- | --- |
| `Math.mean` | `List(F64) -> F64` | `math::mean(list)` | mirror | stats_mean, group_shared_map |
| `Math.median` | `List(F64) -> F64` | `math::median(list)` | database only | stats_spread, group_shared_map |
| `Math.stddev` | `List(F64) -> F64` | `math::stddev(list)` | database only | stats_spread, group_shared_map |
| `Math.variance` | `List(F64) -> F64` | `math::variance(list)` | database only | stats_spread, group_shared_map |
| `Math.percentile` | `List(F64), F64 -> F64` | `math::percentile(list, p)` | database only | stats_spread |

#### `Rand` and the effect rule

Each `Rand` function gives a new value on every call, and `Time.now` is not the
same twice in one statement. One rule says where each may be used:

| Function | Query filter, projection, order, group key | `check`, `assert` | `computed`, `default_by`, update `SET` |
| --- | --- | --- | --- |
| `Time.now` | allowed | allowed | allowed |
| `Rand.*` | refused | refused | allowed |

A `rand::` call in a `WHERE` or a `SELECT` makes one query give other rows each
time, and in a `check` or `assert` it makes a write pass or fail by chance. In a
computed field, a default and an `UPDATE .. SET` a new value is the aim. The
caller states which case it is: `Translate.evaluate` sets `Env.random` to false,
and `Translate.row_value` (`Translate.roc:121`) sets it true. `Schema.computed`,
`Schema.default_by` (`Schema.roc:132`) and `Translate.assignments` call `row_value`.
`Def.default_by` (`Surreal.roc:715`) is the `DEFAULT <expr>` form of `default`:
`.default_by(|k| k.uid, |_| Surreal.Rand.ulid())`.

| Roc | Type | SurrealQL | Kind | Live block |
| --- | --- | --- | --- | --- |
| `Rand.uuid` | `() -> Str` | `<string>rand::uuid()` | database only | rand_defaults |
| `Rand.ulid` | `() -> Str` | `rand::ulid()` | database only | rand_defaults |
| `Rand.int` | `I64, I64 -> I64` | `rand::int(a, b)` | database only | rand_defaults, rand_update |

| Case | Result |
| --- | --- |
| `Surreal.Rand.int(1, 6)` in a filter or a `check` | `Unsupported`: "`Surreal.Rand.int` gives a new value on every call: use it in a default, a computed field or an update" |
| `.default_by(\|k\| k.roll, \|_\| Surreal.Rand.int(1, 6))` | `DEFAULT rand::int(1, 6)` |
| `.computed(\|k\| k.tag, \|_\| Surreal.Rand.ulid())` | `VALUE rand::ulid()` |
| `keyeds.update(\|k\| .., \|k\| { ..k, roll: Surreal.Rand.int(9, 9) })` | `SET roll = rand::int(9, 9)` |

A `uuid` is its own type in SurrealDB and a `string` column refuses it, so the
translator writes the cast `<string>rand::uuid()`.

#### `Id.table`

| Roc | Type | SurrealQL | Kind | Live block |
| --- | --- | --- | --- | --- |
| `Id.table` | `Id(row) -> Str` | `record::tb(id)` | mirror | ids |

It is in the cut of the existing nominal `Id`, next to `Id.key`. It reads the
table of a link that can point at several tables.

#### Dropped, renamed and left out

| Function | Decision | Reason |
| --- | --- | --- |
| `array::sort` | Left out | `List.sort` does not reify, so a package function would be the way, and it needs a change to the compiler |
| `array::difference` | Replaced by `Array.complement` | SurrealDB's `array::difference` is a symmetric difference. `array::complement` is the values of the first list that the second has not, which is what the name `complement` says |
| `time::millis`, `time::micros` | Renamed `Time.unix_millis`, `Time.unix_micros` | `Time.millis` and `Time.micros` make a `Duration`. The prefix `unix_` matches `Time.unix` and `Time.from_unix` |
| `string::similarity::fuzzy`, `smithwaterman` | Left out | Both give 0 for `('martha', 'marhta')` on SurrealDB 3.3.4, so the meaning is not clear |
| `string::distance::hamming` | Left out | An error for texts of different length. A clause cannot guard it, because the length is in characters |
| `string::distance::osa_distance` | Left out | "Invalid function" in 3.3.4 |
| `crypto::argon2`, `bcrypt`, `scrypt`, `pbkdf2` | Left out | A random salt makes each call differ, and password hashing belongs to a sign-up flow, not to a clause |
| `Datetime - Datetime` | Left out | An error in SurrealDB when the result is negative. Subtract `Time.unix(a) - Time.unix(b)` |
| `time::timezone`, `is_leap_year`, `max`, `min` | Left out | Low use, or a Roc builtin and a test say the same |
| `math::mode`, `spread`, `product`, `top`, `bottom`, `midhinge`, `trimean`, `interquartile`, `nearestrank` | Left out | Rarely needed in a clause. They exist in 3.3.4 |
| `rand::string`, `bool`, `float`, `enum`, `time`, `guid` | Left out | Rare. The first three have the shape of `rand::int`, so one row of `functions` adds each |
| `geo::*`, `http::*`, `sleep`, `session::*`, `sequence::*`, `meta::*`, `value::*`, `object::*`, `parse::*`, `vector::*`, `search::*`, `ml::*`, `fn::*` | Left out | A point type, a side effect, a different kind of clause, or a different feature |
| `record::id`, `record::exists`, `type::is_*` | Not needed | `Id.key` and `Link.id` read the id, the schema asserts that every link exists, and the Roc type of a column fixes the type |

#### Time packages other than `Surreal`

A `Surreal.Datetime` is UTC text, `2026-03-04T05:06:07.5Z`, in the form that
SurrealDB prints (a fraction has no trailing zeros). A Roc time package has its
own instant type. Convert through the nanoseconds since 1970-01-01T00:00:00Z:

| Method | Type | Notes |
| --- | --- | --- |
| `Surreal.Datetime.to_unix_nanos` | `Datetime -> I128` | The same count as `time::nano`. `I128` holds every year. Mirror: it runs in Roc |
| `Surreal.Datetime.from_unix_nanos` | `I128 -> Try(Datetime, [BadDatetime])` | A year outside 0 to 9999 is refused. A negative count rounds down. Mirror |
| `Surreal.datetime` | `Str -> Try(Datetime, [BadDatetime])` | `YYYY-MM-DDTHH:MM:SS`, a fraction of up to 9 digits, and `Z`. Another offset is refused |

```roc
# `instant` is a value of another time package, and `nanos_of` and `of_nanos`
# are that package's own conversions to and from nanoseconds since 1970.
at = Surreal.Datetime.from_unix_nanos(nanos_of(instant))
back = of_nanos(Surreal.Datetime.to_unix_nanos(at))
```

`Surreal.Datetime.from_unix_nanos(1772600767123456789)` is
`Ok(2026-03-04T05:06:07.123456789Z)` (`TranslateTest.roc`).

The description is a normal form, so two spellings of one computation reach
the translator as one. A record that a body builds arrives with its fields in
name order, so `SELECT` and `SET` lists are in name order too.

The Roc type of a field decides its SurrealDB type (`Types.roc:273`):

| Roc | SurrealDB `TYPE` | Extra constraint |
| --- | --- | --- |
| `Str` | `string` | |
| `Bool` | `bool` | |
| `I64` | `int` | |
| `I8`, `I16`, `I32`, `U8`, `U16`, `U32` | `int` | `ASSERT $value >= lo AND $value <= hi`, the Roc range |
| `U64`, `I128`, `U128` | Refused with `BadSchema` | The type does not fit `int`, and it has no encoder |
| `F32`, `F64` | `float` | |
| `Dec` | `decimal` | |
| `Surreal.Datetime` | `datetime` | |
| `Surreal.Id(row)`, `Surreal.Link(row)` | `record<table>` | `record::exists($value)`, and a delete policy for a link |
| `{ a : A }` nested | `object`, then `DEFINE FIELD f.a` | |
| `f ?: T` | `option<T>` | |
| `List(T)` of a scalar | `array<T>` | |
| `List({ .. })` | `array<object>`, then `DEFINE FIELD f[*].a` | A key check, so an object has no other keys |
| `List(Link(row))` | `array<record<table>>` | `$value.all(\|$e1\| record::exists($e1))` |
| `[A, B]` | `"A" \| "B"` | |
| `[A, B({ x : X }), C(Y), D(Y, Z)]` | `"A" \| { kind: "B", x: X } \| { kind: "C", value: Y } \| { kind: "D", _0: Y, _1: Z }` | A link in an arm is checked with `IF $value.kind = 'B' THEN .. END` |
| A named type `T := ..` | The type of its backing | |
| `Try`, `Dict`, `Set`, tuples, functions | Refused with `BadSchema` that names the type | |

One rule for a union payload serves the schema, the encoder and the translator,
so the three agree:

| Arm | Written as | A `match` reads |
| --- | --- | --- |
| No payload | `'A'` | Nothing |
| One record payload | `{ kind: 'B', ..fields }` | `u.x` for a field `x` |
| One other payload | `{ kind: 'C', value: v }` | `u.value` |
| Several payloads | `{ kind: 'D', _0: .., _1: .. }` | `u._0`, `u._1` |

Every link at any depth must exist when a row is written, and has a policy for
the delete of its target. The default policy is `Reject`. The schema picks the
mechanism from the shape of the link (`Schema.roc:348`):

| Shape of the link | Existence | Reject, Cascade | Unset | Mechanism |
| --- | --- | --- | --- | --- |
| Root, required (`owner`) | `ASSERT record::exists($value)` | native `REFERENCE ON DELETE` | Refused: the field is required | Native |
| Root, optional (`referrer ?:`) | `ASSERT $value = NONE OR record::exists($value)` | native | Native `UNSET` | Native |
| Root, list (`allergies`) | `$value.all(\|$e1\| record::exists($e1))` | native | Native `UNSET`: the element goes | Native |
| In an object (`chip.implanted_by`) | `ASSERT record::exists($value)` on the path | Event on the target table: `THROW`, or `DELETE` of the holder | Event: sets `NONE`. The field must be optional | Generated event |
| In a list of objects (`vaccines[*].vet`, `items[*].medication`) | `ASSERT record::exists($value)` on the path | Event: `THROW`, or `DELETE` of the holder | Event: filters out the element | Generated event |
| In a union arm (`outcome` arm `Referred`) | `IF $value.kind = 'Referred' THEN record::exists($value.to) ELSE true END` | Event on the target table | Refused: an arm field cannot be unset | Generated event |

`Ignore` writes nothing for the delete. All 44 shape and policy cases were run
on SurrealDB 3.3.4. A native `REFERENCE` works only on a root field, which is
why the other shapes use events. The two mechanisms differ in a few places:

| Native `REFERENCE` | Generated event |
| --- | --- |
| Reverse lookup `<~visit` works | No reverse lookup. Query with `WHERE $id IN items.medication` |
| The behaviour belongs to the referencing field | The behaviour lives on the target table, in an event named `<table>_<path>_on_delete` |
| Error text: `Cannot delete .. as it is referenced by ..` | The `THROW` text: `.. is referenced by visit.items[*].medication` |
| Indexed | A scan per delete, so the schema adds `DEFINE INDEX .. _link` for each nested link path |

Rows are written one at a time and each link must exist, so seeds go in
dependency order. A cycle of required links is a `BadSchema` that names the
cycle (`Schema.roc:619`).

Values cross into SurrealQL through the compiler's derived `encoder_for`,
pointed at `Encode.roc`. A row, a parameter record and a default use it. An
absent optional field is a key that is left out. `Link`, `Id` and `Datetime`
have hand-written encoders.

## Findings: what current Roc and reification cannot do ergonomically

Each finding below was reproduced with a `roc` built at commit `f0e659f0a7`. Each one has a minimal snippet.

| # | Finding | Effect on the library | Kind |
| --- | --- | --- | --- |
| 1 | A captured `Id(row)` is refused when `row` has an optional field | `select_where` examples use a row with no optional field | Reifier limit |
| 2 | A value built from a table, like `table.id("pen")`, does not reify inside a clause | `Surreal.id_of` builds an id without a table | Reifier limit |
| 3 | A record update `{ ..r, f: x }` has the type of `r`, so it cannot change the type of a field | A row of another field type is written in full | Language |
| 4 | `{ x }` with a single field parses as a block | Write `{ x: x }` | Language |
| 5 | `in` is a reserved word | Edge rows name their ends `from` and `to`. The translator writes `in` and `out` | Language |

### 1. A captured `Id` of a row with an optional field

```roc
Customer : { id : Str, zip ?: Str }
Order : { id : Str, customer : Surreal.Link(Customer) }

of_customer : Surreal.Id(Customer) -> Try(Surreal.Statement, Surreal.Error)
of_customer = |who| Surreal.bind_captured(Surreal.select_where(orders, |o| o.customer.id() == who))
# cannot bind this captured value: a captured record with an optional field
```

An `Id(Customer)` holds a phantom `List(Customer)`, so the site sees the
optional `zip` though the value never holds a customer. Remove `zip ?:` and
the capture binds. The example uses a captured `Dec` instead
(`main.roc:514`).

### 2. A table-built constant in a clause

```roc
ruth_id = vets.id("ruth")     # read inside a clause:
# cannot reify this type: a reified value that is not a function
```

The error points at the identity lambda of the table. A constant that reads
the table has no description. `Surreal.id_of("vet", "ruth")` has no table, so it
folds into a literal (`main.roc:110`). So a clause compares a link with an id,
`v.vet.id() == ruth_id`. The translator refuses a `Link` value written in a
clause (`Translate.roc:598`) and asks for `link.id()` and an `Id`.

### 3. A record update keeps the type of its base

```roc
# ruth : Vet, where years : U8
old_vet : VetRow(I64)
old_vet = { ..ruth, id: "bad", years: 300 }
# type mismatch: it has the type Vet, but the annotation says VetRow(I64)
```

`{ ..base, f: v }` has the type of `base`. A row whose `years` is an `I64`, so
that the database can refuse 300, is another type. `main.roc` writes `old_vet`
in full (`main.roc:646`).

### 4 and 5. Syntax

```roc
q = { x }          # a block that returns x, so: Nothing is named x in this scope
T : { in : Str }   # expected a field name: `in` is a keyword
```

## Design limits

| Limit | Why |
| --- | --- |
| A `match` whose arms return whole records is refused | A whole record has no single SurrealQL value. Return the fields |
| No unique constraint through an optional record | SurrealDB does not index a path through an optional object |
| A field of a union arm cannot be named `kind` | `kind` is the tag of the arm in SurrealQL |
| SurrealDB cannot index a union sub-path | An index needs a path of one type |
| `REFERENCE` works only on root fields | Links in objects, lists of objects and union arms use generated events |
| `MERGE` breaks unions | An `update` writes `SET` for each changed field |
| `created_now` overwrites a value that a create gives | A seed cannot set it. A query must not select it for a `-- roc:` comparison |
| `==` on a union is refused | The derived `is_eq` has no SurrealQL form. Write a `match` |
| A captured run-time value works in `select_where` only | The other clauses take a parameter record, which types the values by name |
| `U64`, `I128` and `U128` are refused as field types | They do not fit `int`, and the derived encoder has no case for them. `len().to_i64_wrap()` makes a count an `I64` |
| The schema is the current type, with no migration history | `OVERWRITE` re-defines. A removed field stays in the database |
| Two tables with an equal row type are ambiguous as link targets | The link carries the row type, not the table. Make one row a nominal |
| `Link.get()` on a link that was not fetched crashes in Roc | In a clause it is a traversal. The program has only the rows it fetched |
| No result decoding | The Echo platform has no database driver. `Selected(p, out)` keeps `out`, so a driver can decode with `out.parser_for` |
| The order of an edge list differs between Roc and SurrealDB | Compare as multisets, or sort in the clause |
| A datetime in Roc orders as its string | This is right for the normalised UTC strings that `Surreal.datetime` accepts |
| Each nominal with a `Code` method repeats the cut | The reifier reads the cut of the nominal that owns the method. 69 names stand in 6 lists, and the compiler does not compare them. `check_cuts.py` does. A name missing from one list shows only as the refusal "a clause cannot crash", and only where a method of that nominal calls the function |
| A database-only function stops the program outside a clause | It has no Roc body. A named function that calls one with constant arguments (`Time.now()`, `Rand.ulid()`) runs the call when `roc test` compiles it, and stops. Write the call in the lambda that the builder takes |
| `Rand` works in `default_by`, `computed` and an update only | See the effect rule |
| `group_by` takes a field, not a function call | SurrealDB reads `GROUP BY time::group(at, 'month')` as an idiom and refuses it ("Missing group idiom"). `Time.group` works in a projection, not as a key |
| The text of a datetime is compared with a datetime or a literal only | The datetimes are compared, not the text, so a fraction of 3, 6 or 9 digits does not matter |
| `Array.sort` is not available | `List.sort` does not reify, and a package function needs a change to the compiler |

## The cost

| Module | Lines | Code lines | Role |
| --- | --- | --- | --- |
| `Ql.roc` | 196 | 161 | Values, quoting, errors |
| `Encode.roc` | 157 | 100 | The encoder format |
| `Types.roc` | 554 | 451 | Type mapping, checks, link sites |
| `Translate.roc` | 1296 | 1051 | The translator |
| `Schema.roc` | 662 | 543 | `DEFINE` statements, link policies |
| `Surreal.roc` | 1238 | 769 | The API, with its own `expect`s |
| `TypesTest.roc`, `TranslateTest.roc`, `SchemaTest.roc`, `QueriesTest.roc` | 1495 | 1154 | Tests |
| `main.roc` | 988 | 739 | The example |
| `builtins.roc` | 978 | 735 | The live check of the builtin rows and the package functions |
| `refactored.roc` | 1082 | 823 | The same, refactored |

The library is 4103 lines, 3075 of them code. The translator is the largest part.
Its `op` has one arm per `Code.Op` variant
(`Translate.roc:468`). A new SurrealQL function is one row in `builtin`
(`Translate.roc:755`), or one row of `functions` (`Translate.roc:930`) for a package function, with a test in `TranslateTest.roc` and, when its result is risky, a query in `builtins.roc`. Nothing in `main.roc` is SurrealQL-specific except
the method names. Its queries use Roc's operators, its `match`, its optional
fields and its `??`, and each query uses functions that the application also
calls.
