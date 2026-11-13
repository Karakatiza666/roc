# A SQL DSL over reified Roc functions

Row types are plain Roc records. A table is a `Sql.Table(row)` over one, and
every query clause and every migration constraint is a Roc function over that
record. The builder takes the function as a `Code(f)`, so the compiler
describes it, and `Sql.roc` translates the description into SQL. The same
records are the seed data, the arguments of the application's own functions,
and the inputs of its tests.

| File | What it is |
| --- | --- |
| `Sql.roc` | The builder and the translator. A `Code` graph in, SQL out. |
| `main.roc` | A shop's schema, migrations, seed rows and queries. It is an app over three packages: `sql` (this directory), `time` and `time_sql`. |
| `time/` | A package with an opaque `Time`, which knows nothing of SQL. |
| `time_sql/` | The glue package: `TimeSql.extension` tells the translator what `Time`'s comparisons and column type are in SQL. |
| `check.py` | Runs the printed script on SQLite and compares query results with the ones Roc computes. |
| `expected_output.sql` | What `roc main.roc` prints. |
| `extensions.roc` | Unit tests of extensions over a sibling module's opaque type: refusals without an extension, an operation the extension does not cover, a module's own `Bool.not` refused by its id and covered by an extension that leaves the builtin `NOT` alone, `==` on an `F64` column, and the order of the bytes `Sql.Param` writes. |
| `Bool.roc` | A module's own `Bool` with a `not` and a `level`: the same owner and method as the builtin's `not`, a different id. |
| `Stamp.roc` | The opaque type `extensions.roc` extends the translator with. |
| `refactored.roc` | `main.roc` with the parameters of the reified functions renamed and bindings added and reordered. It prints `expected_output.sql` byte for byte, which its last `expect` checks. |

```
roc examples/reifying/sql/main.roc          # the SQLite script
roc test examples/reifying/sql/main.roc     # 18 expects
roc test examples/reifying/sql/refactored.roc  # 11 expects: ten of those, and the script is expected_output.sql
roc test examples/reifying/sql/extensions.roc  # 17 expects
python3 examples/reifying/sql/check.py      # run it on SQLite, bind the `?` values, compare with Roc
```

## What it covers

| Feature | Roc | SQL | Where |
| --- | --- | --- | --- |
| Binary operators | `p.price >= 20 and p.title != "Gift card"` | `(products.price >= 20.0) AND (products.title <> 'Gift card')` | `main.roc:168` |
| `NUMERIC` arithmetic | `p.price * 1.2` over a `Dec` | `products.price * 1.2` | `main.roc:169` |
| A captured run-time value | `\|o\| o.quantity >= min_quantity` inside `orders_of_at_least` | `?1 <= orders.quantity`, which `check.py` binds to the value | `main.roc:248` |
| Another package's opaque type | `\|e\| e.at < cutoff`, `cutoff : Time`, with `TimeSql.extension` | `events.at < ?1`, and `?1` is the blob `Sql.Param` wrote, which `check.py` binds | `main.roc:254` |
| `>`, `==` and `!=` on it | `\|e\| e.at > cutoff`, `e.at == t`, `e.at != t` | `events.at > ?1`, `events.at = ?1`, `NOT (events.at = ?1)` | `main.roc:259`, `main.roc:262`, `main.roc:265` |
| A column of an opaque type, and its rows | `events.create_with([TimeSql.extension], ..)`, `events.insert_one(\|{}\| { .., at: e.at })` | `at BLOB NOT NULL`, and `INSERT .. VALUES (X'80..', ..)` with the same bytes a filter binds | `main.roc:95`, `main.roc:151` |
| A captured row with an optional field | `customers.insert_one(\|{}\| c)` inside `insert_customer`, for a customer with and without `email` | `INSERT INTO customers (country, email, id, name) VALUES (?1, ?2, ?3, ?4)`. A field the row does not hold arrives as `Code.Value.Absent` and binds `NULL` | `main.roc:156` |
| `==` on a row with an optional field | `\|row\| row == c` inside `same_customer`, for a customer with and without `email` | `(customers.email IS ?2)`, and `IS NOT` for `!=`. The captured customer is one input, because the presence switch reads it whole, so each of its fields is one placeholder (`?1` to `?4`). The translator recognizes the presence switch the compiler gives `==` and prints SQLite's `IS`, which treats `NULL` as a value. Two customers with no `email` are equal, as in Roc, where `customers.email = NULL` would match no row | `main.roc:274` |
| `NUMERIC(p, s)` columns | `.numeric(\|p\| p.price, 10, 2)` | `price NUMERIC(10, 2) NOT NULL` | `main.roc:73` |
| `CHECK` | `.check(\|o\| o.quantity > 0 and o.discount < 1)` | `CHECK ((quantity > 0) AND ...)` | `main.roc:90` |
| Keys | `.primary_key(\|c\| c.id)`, `.references(\|o\| o.customer_id, customers)` | `PRIMARY KEY (id)`, `FOREIGN KEY (customer_id) REFERENCES customers` | `main.roc:86-87` |
| Nullable column | `email ?: Str`, added by migration 003 | `ALTER TABLE customers ADD COLUMN email TEXT` | `main.roc:94` |
| Explicit `NULL` handling | `c.?email ?? "(none)"` | `COALESCE(customers.email, '(none)')` | `main.roc:198` |
| Parameters | `.filter_by(\|band, p\| p.price >= band.low)`, chained | `products.price >= :low` | `main.roc:188-189` |
| Three-way join | `.join(orders, \|c, o\| ..).join(products, \|(_, o), p\| ..)` | two `JOIN .. ON` | `main.roc:209-210` |
| Reused Roc functions | `line_total(o, p)`, `is_bulk(o)` | expanded in place | `main.roc:215`, `main.roc:218` |
| A helper one clause calls twice | `with_tax(p.price)` and `with_tax(p.price * 2)` | two expansions of one row | `main.roc:338` |
| Aggregates | `rows.len()`, `rows.map(f).sum()` over a group | `COUNT(*)`, `SUM(..)` | `main.roc:233-234` |
| Seed rows | `products.insert(seed_products)` | `INSERT` per row, through a derived encoder | `main.roc:423` |
| Refusals | `c.name.count_utf8_bytes()` | `` `count_utf8_bytes` counts bytes, and SQL's `length` counts characters `` | `main.roc:317` |

`check.py` executes the whole script on SQLite with foreign keys on. The two
joined queries also print the rows Roc computes by calling the same functions
over the same seed rows (`main.roc:430-431`). The harness requires them to agree,
so one definition of `line_total` has two executions and a test that they
match.

## How it is built

A clause is a function over the row. The translator reads the root row of
its `Code` graph as a tree (`Graph.to_tree`), and evaluates the tree with
each parameter bound to what it stands for (`Sql.roc:794`). A node the tree
keeps as a definition is evaluated once, where its block defines it:

| Binding | Stands for | A field read off it is |
| --- | --- | --- |
| `Row(Leaf(alias))` | one table's row | the column `alias.field` |
| `Row(Pair(l, r))` | a joined row | nothing; `.0` and `.1` pick a side (`Sql.roc:925`) |
| `Params` | the parameter record | the placeholder `:field` |
| `Group(source)` | a group's rows | nothing; `len` and `map(..).sum()` aggregate it (`Sql.roc:1036`) |
| `Maybe(column)` | a read of an optional field, a column that can be `NULL` | nothing; a `switch` on it is `COALESCE` or `CASE` (`Sql.roc:953`) |
| `Fields(..)` | a record the body built | that field's binding |

A call to one of the application's own functions that two places share, or
that recurses, is a `Call` of another row of the same graph, and is expanded
with that row's parameters bound the same way (`Sql.roc:1085`). A function that
one place calls is already inlined in the description. A helper called twice
expands twice (`main.roc:338`). A function that calls itself is refused with
that reason, because SQL has no recursion to spell it with (`main.roc:345`).
A row passes through as a row, which is why `line_total` works inside a query
unchanged.

The description is a normal form, so two spellings of one computation reach
the translator as one:

| Written | Arrives as | The translator writes |
| --- | --- | --- |
| `o.quantity >= 10` | `Num.I64.is_lte(10, o.quantity)`: an integer literal first | `orders.quantity >= 10`: a comparison whose left operand is the only literal is mirrored back (`Sql.roc:1109`) |
| `p.title != "Gift card"` | `Bool.not(Str.is_eq(..))` | `products.title <> 'Gift card'` |
| `{ title: p.title, price: p.price }` | a record in field-name order | `SELECT products.price AS price, products.title AS title`: result columns, and a step's `CREATE TABLE` columns, come in name order |

A refusal names the construct, but not where it was written: the description
carries no source regions, so a message cannot lead with a `main:227:46`
location. `Code.refuse_at` reports a node at every place in the source it came
from, but it stops the compile, where an `Err` can be tested, so this translator
returns an `Err` instead.

Migrations list their columns as a record (`|c| { id: c.id, name: c.name }`),
so a migration keeps its meaning after the record gains a field. The
record's fields arrive in name order, so the table's columns do too. The row
type's full field list comes from the lambda's parameter type, so
`Sql.schema_gaps` (`Sql.roc:624`) can say which fields no migration creates:

```roc
expect Sql.schema_gaps(migrations.take_first(2)) == ["customers.email is never created"]
```

Parameter and row values cross into SQL through the compiler's derived
`encoder_for`, pointed at `Sql.RowEncoding` (`Sql.roc:1185`). `bind` requires `p`
to have that encoder, so the parameter values are typed by the same record the
filter reads.

## Extensions

`Sql.roc` knows the builtins. An operation of another package's opaque type,
such as `Time.is_lt` (`time/Time.roc`), reaches it as a `Prim` it has no row
for, and a column of that type as an `Opaque` type it has no SQL type for.
`time` cannot gain SQL methods outside its own module, and `Sql.roc` does
not change for it. A third package, `time_sql`, holds the glue.
`select_where` and `Table.create_with` take a list of `Sql.Extension`
values, which name both by the identity the compiler gives them
(`time_sql/TimeSql.roc:19`):

```roc
extension = Sql.extension({
	prims: [
		{ prim: Code.prim(Time.is_lt), render: TimeSql.binary("<") },
		{ prim: Code.prim(Time.is_gt), render: TimeSql.binary(">") },
		{ prim: Code.prim(Time.is_eq), render: TimeSql.binary("=") },
	],
	types: [{ type: Code.type_id(TimeSql.time_proxy), column: "BLOB" }],
})
```

| Node | What the translator does |
| --- | --- |
| `Prim` of a builtin owner (`Num.*`, `Str`, `Bool`, `Try`, `List`) | its own table, by owner and method (`Sql.prim`) |
| any other `Prim` | the extension entry whose `prim` is the node's `id`: the arguments' SQL and the call's evidence go to `render`. No entry: "`Stamp.is_lt` has no SQL form; pass an extension that covers it" |
| `Opaque(name, id, _)` as a column type | the extension entry whose `type` is `id` (`Sql.column_type`). No entry: a `BadSchema` error |
| a captured value of an opaque type | `select_where` takes `Code.Binds(.., Sql.Param)`, so the value arrives as `Encoded` bytes in `Sql.Param`, and binds as a blob |
| a row with a field of an opaque type | `Table.insert_one` takes `Code.Binds(Code({} -> row), Sql.Param)`. Its function builds the row from captured values, so each field is a `?`, and a field of an opaque type binds as the same `Sql.Param` bytes |
| a captured row | `Input` of a record slot is the record's fields, one `?` each, numbered after the placeholders of the slots before it. `Sql.bind_captured` binds the field values in the same order, and an optional field the row does not hold (`Absent`) binds `NULL` |

One encoding serves binds and inserts. `Table.insert` writes through the
derived encoder in `Sql.RowEncoding`, which has no method for the scalars
inside an opaque type (`encode_i128` for `Time`), so a row with a `Time`
field does not type-check there and goes through `insert_one`. The slot
type of a captured field says which fields are opaque, so no translator
step guesses it from the shape of the bytes.

The operator table keys on the owner as well as the method. Before, a
package's `is_lt` was read as SQL's `<` by its name alone.

`Sql.Param` writes a value as bytes that sort as the value does: an integer
is its big-endian bytes with the sign bit flipped, a `Dec` its atto count
the same way, a `Str` its bytes with each zero byte written `0, 255` and `0, 0`
after them, a record its fields in name order. `extensions.roc` checks that
the bytes sort as the values do. A database compares two
blobs byte by byte, so an extension that renders `Time.is_lt` as `<` on a
`BLOB` column agrees with Roc. That is the claim an extension makes, and the
translator cannot check it.

The extensions are an argument of the translator's call. A translator that
returns a `Code.Bound` runs while the compiler runs, so every argument other
than the captures must be fixed then, and a list passed in as a parameter of
the function around the call is refused.

## Findings: what current Roc and reification cannot do ergonomically

Each row was reproduced against this branch's `zig-out/bin/roc`. Rows 1, 2,
3 and 6 are fixed on the branch; the sections below say how. Row 4 was
reproduced again with `roc` at `debug-10710041` and no longer crashes.

| # | Finding | Effect on the DSL | Kind |
| --- | --- | --- | --- |
| 1 | An inline lambda at a `Code` position had its record rows closed before the call related its other arguments | fixed: `join(orders, \|c, o\| ..)` checks, and `filter_by`s chain | reifier bug, fixed |
| 2 | A destructuring pattern in a reified lambda's parameters had no description, including `_` | fixed: `\|((c, o), p)\|` and `\|_, p\|` describe | reifier gap, fixed |
| 3 | A lambda that failed to check at a `Code` position panicked the compiler instead of reporting its type error | fixed: the type error is reported | reifier bug, fixed |
| 4 | `List.max` in a reified body describes, and the translator has no `MAX` for it | refused: "`List.max` has no SQL form" | not a bug, a missing translator row |
| 5 | An unused lambda parameter leaves its type open, and the site is refused as polymorphic | every parameter record field must be read | by design, sharp |
| 6 | A recursive function annotated with a closed tag union in its result panicked post-check | fixed | compiler bug, not reification, fixed |
| 7 | A `where` alias is not visible in nested type blocks, and an unqualified name in a `where` resolves to `Builtin` first | `bind` and `insert` spell the constraint out | language papercut |
| 8 | `roc fmt` doubles a space after `a.Alias :`, so `a.Bindable :  where [..]` is what it writes | `Sql.roc` keeps the formatter's output, so `roc fmt --check` passes | formatter bug |

### 1. Rows closed before sibling arguments are related (fixed)

A staged site closes the open rows of its `f`, because the description is
monomorphic. It used to close them when the site's own frame finished. A call
checks all its arguments first and relates them to the formal slots
afterwards, so in `two(rows, |r| r.id > 0)`, `a` was closed to `{ id }` before
`rows : Tag(Row)` fixed it to the whole row:

```roc
Stage := {}.{
	two : Tag(a), Code(a -> Bool) -> Str
	...
}

Row : { id : I64, name : Str }

staged = Stage.two(rows, |r| r.id > 0)    # was a type mismatch on `rows`
```

A method-call receiver was the exception, because static dispatch relates the
receiver first, which is why the builder once spelled a join
`.join(orders).on(..)`. The same early close made a second `filter_by` fail:
the first lambda closed the parameter record to the fields it read.

Checking now closes no row at a site. The reifier reads each open row tail
at the default that checking recorded for it and seals it there, the way
Monotype seals a row when it compiles a function
(`variableSealsToRowDefault`). A row that a later clause widens is still open
when that clause is checked, so the chain types as it does in ordinary Roc.
`test/cli/StagedSiblingRows.roc` pins a table before the lambda, two tables,
a lambda alone, and a chain whose second clause adds a field to the first
one's parameter record.

### 2. Destructuring parameters (fixed)

```roc
.join(products, |(_, o), p| o.product_id == p.id)
# the condition describes as: Num.I64.is_eq(p0.1.product_id, p1.id)
```

A parameter written as a pattern is one parameter of the row, and each name
its pattern binds is the `Index` or `Field` read it stands for. A lambda
passed to one of the application's functions is a row of its own.
`test/cli/StagedPatternParams.roc` pins the shapes: nested tuples, `_`,
records, a variant, and a lifted lambda.

The example now reads joined rows through patterns: `|((c, o), p)| ..`
(`main.roc:215`).

### 3. A lambda that failed to check (fixed)

```roc
staged = Stage.shape(|(n)| n > 0)     # Stage.shape : Code(U64 -> Bool) -> Str
```

`(n)` is a one-element tuple pattern, so this lambda does not fit
`U64 -> Bool`. Checking replaced it with a runtime error. Reification then
visited the site anyway and tripped `attachCodeReification`'s invariant, so
the panic hid the type error. A poisoned site is now left to its own
diagnostic (`codeSiteWasPoisoned`, `src/check/checked_artifact.zig`), and
`test/cli/StagedPoisonedSite.roc` checks that the mismatch is reported. The
two-`filter_by` case of finding 1 reached the same path; since finding 1's
fix it checks.

### 4. `List.max` in a reified body

`g.rows.map(|r| r.price).max()` inside a reified body once passed `roc check`
and then crashed as `runtime error`. It no longer does. The body describes as
`List.max(List.map(p0, closure r1()))`, and `Sql.roc` refuses it with
"List.max has no SQL form", as it does for any builtin that has no row in
`prim`.

### 6. A recursive function with a closed union in its result (fixed)

No reification involved:

```roc
Shape := [Leaf(List({ name : Str, presence : [Required, Optional] })), Wrap(Shape)]

fields_of : Shape -> Try(List({ name : Str, presence : [Required, Optional] }), [NotLeaf])
fields_of = |shape| match shape {
	Leaf(fields) => Ok(fields)
	Wrap(inner) => fields_of(inner)
}
# panicked: postcheck invariant violated: checked site substitution length
# differed from its scheme's quantified variables
```

A closed union in a result is open in its row, so the annotation quantifies
two row variables. The body closes one, by returning the union `Shape` holds.
An annotated self-reference instantiates the scheme the annotation
pre-declares, a copy disjoint from the body's, so the recursive call recorded
a substitution for two variables. Lowering read it against the body's scheme,
which has one. `evidenceForSite` (`src/postcheck/monotype/lower.zig`) now
derives the substitution from the request whenever the recorded one belongs
to a scheme of another length, which is the path it already took when
nothing was recorded. `test/cli/RecursiveNarrowedAnnotation.roc` covers it,
with polymorphic recursion at `U8` under a call at `Str`.

In a package this panic also hid three ordinary type errors in `Sql.roc`.

## Design limits that are not bugs

| Limit | Why |
| --- | --- |
| A migration's lambdas name the current row type | Adding a field is fine: `schema_gaps` catches a missing migration. Dropping or renaming one makes old migrations stop compiling, because they read a field the record no longer has. A historical migration needs frozen types or string column names |
| A foreign key's target type is not checked | `Table(row)` carries no key type, so `references(\|o\| o.customer_id, customers)` checks the column exists, not that its type matches `customers.id` |
| A captured value needs `select_where` | A clause that reads a value from around itself is refused unless its translator returns a `Code.Bound`. `Sql.select_where` does, so its filter can read a parameter of the function around it, and the value is a numbered `?`. Its format is `Sql.Param`, so a captured value of an opaque type binds as a blob. The other clauses keep the parameter record, which types the parameters by name. Top-level constants still fold into literals |
| No result decoding | The Echo platform has no database driver. `Selected(p, out)` keeps `out`, so a driver can decode rows with `out.parser_for` |
| `NULL` reaches Roc only through optional fields | Non-optional fields are `NOT NULL` columns, and Roc forces `??`, `match` or `is_ok` on the optional ones, so SQL's three-valued logic never decides a predicate. An outer join would reintroduce it |
| `SELECT` columns come in field-name order, not in the order the query wrote them | A Roc record has no field order, so a record the clause builds reaches the translator sorted by name. `{ title: .., price: .. }` selects `price` first. A reader of the result should match columns by name |
| SQLite's `NUMERIC` arithmetic is floating point | The harness rounds to six places. A `Dec` is exact; PostgreSQL would agree exactly |

## The cost

`Sql.roc` is the largest module. The builder with its migrations and the
translator are its two big parts, and they are about the same size. As with
`../glsl/`, nearly all of the translator is fixed cost. Its `op` has one arm per
`Code.Op` variant, and a new SQL function is one row in `builtins`. Nothing in
`main.roc` is SQL-specific except the method names. Its queries use Roc's
operators, its `and` and `or`, its optional fields and its `??`, and each query
is built from functions the application also calls.
