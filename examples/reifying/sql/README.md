# A SQL DSL over reified Roc functions

Row types are plain Roc records. A table is a `Sql.Table(row)` over one, and
every query clause and every migration constraint is a Roc function over that
record. The builder takes the function as a `Code(f)`, so the compiler
describes it, and `Sql.roc` translates the description into SQL. The same
records are the seed data, the arguments of the application's own functions,
and the inputs of its tests.

| File | What it is |
| --- | --- |
| `Sql.roc` | The builder and the translator. `Code.Ir` in, SQL out. |
| `main.roc` | A shop's schema, migrations, seed rows and queries. |
| `check.py` | Runs the printed script on SQLite and compares query results with the ones Roc computes. |
| `expected_output.sql` | What `roc main.roc` prints. |

```
roc examples/reifying/sql/main.roc          # the SQLite script
roc test examples/reifying/sql/main.roc     # 10 expects
python3 examples/reifying/sql/check.py      # run it on SQLite, compare with Roc
```

## What it covers

| Feature | Roc | SQL | Where |
| --- | --- | --- | --- |
| Binary operators | `p.price >= 20 and p.title != "Gift card"` | `(products.price >= 20.0) AND (products.title <> 'Gift card')` | `main.roc:122` |
| `NUMERIC` arithmetic | `p.price * 1.2` over a `Dec` | `products.price * 1.2` | `main.roc:122` |
| `NUMERIC(p, s)` columns | `.numeric(\|p\| p.price, 10, 2)` | `price NUMERIC(10, 2) NOT NULL` | `main.roc:61` |
| `CHECK` | `.check(\|o\| o.quantity > 0 and o.discount < 1)` | `CHECK ((quantity > 0) AND ...)` | `main.roc:78` |
| Keys | `.primary_key(\|c\| c.id)`, `.references(\|o\| o.customer_id, customers)` | `PRIMARY KEY (id)`, `FOREIGN KEY (customer_id) REFERENCES customers` | `main.roc:74` |
| Nullable column | `email ?: Str`, added by migration 003 | `ALTER TABLE customers ADD COLUMN email TEXT` | `main.roc:82` |
| Explicit `NULL` handling | `c.?email ?? "(none)"` | `COALESCE(customers.email, '(none)')` | `main.roc:151` |
| Parameters | `.filter_by(\|band, p\| p.price >= band.low)`, chained | `products.price >= :low` | `main.roc:142` |
| Three-way join | `.join(orders, \|c, o\| ..).join(products, \|(_, o), p\| ..)` | two `JOIN .. ON` | `main.roc:163` |
| Reused Roc functions | `line_total(o, p)`, `is_bulk(o)` | expanded in place | `main.roc:171` |
| Aggregates | `rows.len()`, `rows.map(f).sum()` over a group | `COUNT(*)`, `SUM(..)` | `main.roc:187` |
| Seed rows | `products.insert(seed_products)` | `INSERT` per row, through a derived encoder | `main.roc:291` |
| Refusals with a location | `c.name.count_utf8_bytes()` | `main:225:46: ... counts bytes, and SQL's length counts characters` | `main.roc:225` |

`check.py` executes the whole script on SQLite with foreign keys on. The two
joined queries also print the rows Roc computes by calling the same functions
over the same seed rows (`main.roc:203`). The harness requires them to agree,
so one definition of `line_total` has two executions and a test that they
match.

## How it is built

A clause is a function over the row, and the translator walks its body with
each parameter bound to what it stands for (`Sql.roc:525`):

| Binding | Stands for | A field read off it is |
| --- | --- | --- |
| `Row(Leaf(alias))` | one table's row | the column `alias.field` |
| `Row(Pair(l, r))` | a joined row | nothing; `.0` and `.1` pick a side (`Sql.roc:640`) |
| `Params` | the parameter record | the placeholder `:field` |
| `Group(source)` | a group's rows | nothing; `len` and `map(..).sum()` aggregate it (`Sql.roc:799`) |
| `Fields(..)` | a record the body built | that field's binding |

A call to one of the application's own functions resolves against
`Code.definitions` and is expanded with its arguments bound the same way
(`Sql.roc:829`). A row passes through as a row, which is why `line_total`
works inside a query unchanged.

Migrations list their columns as a record (`|c| { id: c.id, name: c.name }`),
so a migration keeps its meaning after the record gains a field. The row
type's full field list comes from the lambda's parameter type, so
`Sql.schema_gaps` (`Sql.roc:409`) can say which fields no migration creates:

```roc
expect Sql.schema_gaps(migrations.take_first(2)) == ["customers.email is never created"]
```

Parameter and row values cross into SQL through the compiler's derived
`encoder_for`, pointed at `Sql.Encoding` (`Sql.roc:962`). `bind` requires `p`
to have that encoder, so the parameter values are typed by the same record the
filter reads.

## Findings: what current Roc and reification cannot do ergonomically

Each row was reproduced against this branch's `zig-out/bin/roc`. Rows 1, 2,
3 and 6 are fixed on the branch; the sections below say how.

| # | Finding | Effect on the DSL | Kind |
| --- | --- | --- | --- |
| 1 | An inline lambda at a `Code` position had its record rows closed before the call related its other arguments | fixed: `join(orders, \|c, o\| ..)` checks, and `filter_by`s chain | reifier bug, fixed |
| 2 | A destructuring pattern in a reified lambda's parameters had no description, including `_` | fixed: `\|((c, o), p)\|` and `\|_, p\|` describe | reifier gap, fixed |
| 3 | A lambda that failed to check at a `Code` position panicked the compiler instead of reporting its type error | fixed: the type error is reported | reifier bug, fixed |
| 4 | `List.max` in a reified body checks cleanly, then crashes with a bare "runtime error" | no `MAX` aggregate | reifier bug |
| 5 | An unused lambda parameter leaves its type open, and the site is refused as polymorphic | every parameter record field must be read | by design, sharp |
| 6 | A recursive function annotated with a closed tag union in its result panicked post-check | fixed | compiler bug, not reification, fixed |
| 7 | A `where` alias is not visible in nested type blocks, and an unqualified name in a `where` resolves to `Builtin` first | `bind` and `insert` spell the constraint out | language papercut |
| 8 | `roc fmt` mis-indents a `}` after a `match` on a tuple, and doubles a space after `a.Alias :` | hand-fixed in `Sql.roc` | formatter bug |

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

A site now queues its rows, and `groundPendingStagedRows`
(`src/check/Check.zig`) closes them just before the binding that holds them
generalizes: only the extensions that boundary owns, so a row an outer scope
still has to fix stays open for that scope. A site no binding generalizes,
such as one in an `expect`, closes at the end of the module.
`test/cli/StagedSiblingRows.roc` pins a table before the lambda, two tables,
a lambda alone, and a chain whose second clause adds a field to the first
one's parameter record.

### 2. Destructuring parameters (fixed)

```roc
.join(products, |(_, o), p| o.product_id == p.id)
# the condition describes as: |bind#1, p| let o = bind#1.0.1; (o.product_id is_eq p.id)
```

Destructuring in a body already described as `Let`s over `Index` and
`Field`. A parameter written as a pattern now goes by an invented name, and
the same reads (`destructureInto`, `src/check/code_reifier.zig:5744`) wrap the
body (`bindParamPattern`, `wrapDestructures`). A lambda passed to one of the
application's functions is lifted into a row named after the first name its
patterns bind, or `Module.lambda` when they bind none (`|_| ..`).
`test/cli/StagedPatternParams.roc` pins the shapes: nested tuples, `_`,
records, a variant, and a lifted lambda.

The example now reads joined rows through patterns: `|((c, o), p)| ..`
(`main.roc:171`).

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

`g.rows.map(|r| r.price).max()` inside a reified body passes `roc check` and
then crashes as `runtime error`. The same call outside a reified body returns
`Ok(2.5)`.

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
| Captures are refused | A runtime value reaches a query only as a field of the parameter record. That makes parameters typed, which is the point; top-level constants still fold into literals |
| No result decoding | The Echo platform has no database driver. `Selected(p, out)` keeps `out`, so a driver can decode rows with `out.parser_for` |
| `NULL` reaches Roc only through optional fields | Non-optional fields are `NOT NULL` columns, and Roc forces `??`, `match` or `is_ok` on the optional ones, so SQL's three-valued logic never decides a predicate. An outer join would reintroduce it |
| SQLite's `NUMERIC` arithmetic is floating point | The harness rounds to six places. A `Dec` is exact; PostgreSQL would agree exactly |

## The cost

`Sql.roc` is about 1000 lines: 450 of builder and migrations, 450 of
translator, 50 of encoding. As with `../glsl/`, nearly all of the translator is
fixed cost. Its `eval` has one arm per `Code.Ir` variant (`Sql.roc:626`), and a
new SQL function is one row in `call` (`Sql.roc:783`). Nothing in `main.roc` is
SQL-specific except the method names. Its queries use Roc's operators, its
`and` and `or`, its optional fields and its `??`, and each query is built from
functions the application also calls.
