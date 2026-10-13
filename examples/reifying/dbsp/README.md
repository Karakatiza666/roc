# A DBSP circuit over reified Roc functions

DBSP is an incremental view maintenance engine. A query is a circuit of
operators over collections, and the engine keeps its answer current under
insertions and deletions by computing the change, at a cost proportional to the
change rather than to the data. The operators take closures.

Here the closures are Roc functions. A relation is a `Dbsp.Rel(row)`, every
combinator that takes a function takes it as a `Code(f)`, and `Dbsp.roc`
translates each description into a Rust closure for Feldera's `dbsp` crate,
together with the Rust struct of every row type and the `build_circuit` function
that wires it all up. The combinators fix the topology of the circuit. The
reified functions supply the expressions it is made of. This is the case of
section 14.3 of the proposal, and the motivation of section 15.

| File | What it is |
| --- | --- |
| `Dbsp.roc` | The builder and the translator. `Code` graphs in, one Rust source string out. |
| `package.roc` | Exposes `Dbsp`, so that the apps below name this directory as the `dbsp` package. |
| `main.roc` | Four views over sensor readings, two of them calling a helper function, the Rust they become, four refusals, and a pure-Roc reference engine. |
| `expected_output.rs` | What `roc main.roc` prints. |
| `refactored.roc` | The same four views with every lambda parameter and local renamed and the bindings reordered. It prints `expected_output.rs` byte for byte, which its one `expect` checks. |

```
roc examples/reifying/dbsp/main.roc             # the Rust program
roc test examples/reifying/dbsp/main.roc        # 19 expects
roc test examples/reifying/dbsp/refactored.roc  # 1 expect: the same text
```

## Targets, and what is not checked

The output targets the `dbsp` crate of `github.com/feldera/feldera`
(`crates/dbsp`), in the form where `OrdZSet<T>` takes one type parameter and a
weight is an `i64`. The Rust is not compiled here and not compiled in CI. There
was no copy of the crate to check it against, so every name it uses was written
from the crate's documented shape: `RootCircuit`, `add_input_zset`, `ZSetHandle`,
`OutputHandle`, `filter`, `map`, `map_index`, `aggregate_linear`, `join` with a
`(key, left, right)` closure, `Tup2`, `F64`. Two of them carry an assumption the
translator would have to change if it is wrong:

| Assumption | Where it is written |
| --- | --- |
| The closure of `map` over an indexed stream takes `(&key, &value)`. `count` flattens its result to `Tup2(key, n)` rows with it. | `Dbsp.roc:212` |
| `F64` is a `Copy` wrapper with `+ - * /` and `Neg`, and no truncating division or remainder, so `//` and `%` on a float are refused. | `Dbsp.roc:884` |

Pin the crate version in the `Cargo.toml` of whoever compiles the output.

## What it covers

| Feature | Roc | Rust | Where |
| --- | --- | --- | --- |
| Input | `readings = Dbsp.input("readings")`, typed `Dbsp.Rel(Reading)` | `let (readings, readings_handle) = circuit.add_input_zset::<Reading>();` | `main.roc:53` |
| Row type | `Reading := { sensor : Str, celsius : F64 }` | one `pub struct` with the derives `dbsp` needs: `Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, SizeOf, Archive, Serialize, Deserialize` | `Dbsp.roc:451` |
| `F64` column | `celsius : F64` | `F64`, `dbsp`'s wrapper: a bare `f64` is neither `Eq` nor `Ord`, and a row must be both | `Dbsp.roc:475` |
| Filter | `.filter(\|r\| r.celsius > 80.0)` | `.filter(\|row\| row.celsius > F64::new(80.0))` | `main.roc:129` |
| Key | `.key_by(\|r\| r.sensor)` | `.map_index(\|row\| (row.sensor.clone(), row.clone()))` | `main.roc:130` |
| Count per key | `.count()` | `.aggregate_linear(\|_\| 1i64).map(\|(key, n)\| Tup2(key.clone(), *n))` | `Dbsp.roc:212` |
| Tuple pattern | `.filter(\|(_, n)\| n >= 3)` | `.filter(\|row\| row.1 >= 3i64)` | `main.roc:132` |
| Map to a row | `.map(\|(sensor, n)\| Alert.({ sensor, breaches: n }))` | `.map(\|row\| Alert { breaches: row.1, sensor: row.0.clone() })` | `main.roc:133` |
| Join | `.join(sites.key_by(..), \|_sensor, r, s\| ..)` | `.join(&sites.map_index(..), \|_key, left, right\| ..)` | `main.roc:154` |
| Helper called from one place | `breach_line(r, s)`, which calls `excess` | their bodies, written where the join's closure uses them | `main.roc:81` |
| Helper called from two places | `clamp(r.celsius, -40.0, 20.0)` and `clamp(r.celsius, 80.0, 125.0)` | one `fn helper_0(p0: F64, p1: F64, p2: F64) -> F64` before `build_circuit`, and `helper_0(row.celsius, F64::new(-40.0), F64::new(20.0))` at each call | `Dbsp.roc:300` |
| Recursive helper | `power(n, 2)`, where `power` calls itself | `fn helper_1(p0: i64, p1: i64) -> i64`, which calls `helper_1`, and `helper_1(2i64, row.1)` | `Dbsp.roc:300` |
| Shared work | `excess(r, s)` read for two fields | one `let n4 = left.celsius - right.limit;` | `Dbsp.roc:566` |
| Short-circuit | `b.over_by > 5.0 and !b.room.starts_with("test-")` | `row.over_by > F64::new(5.0) && !row.room.starts_with("test-")` | `Dbsp.roc:714` |
| Strings | `starts_with`, `ends_with`, `contains`, `concat`, `is_empty`, `count_utf8_bytes`, `caseless_ascii_equals`, ASCII case | `starts_with`, `ends_with`, `contains`, `format!`, `is_empty`, `.len() as u64`, `eq_ignore_ascii_case`, `to_ascii_lowercase` | `Dbsp.roc:792` |
| `if` | `if a b else c` | `if a { b } else { c }` | `Dbsp.roc:722` |
| Literals | `3`, `80.0`, `"x"` | `3i64`, `F64::new(80.0)`, `"x"` | `Dbsp.roc:756` |
| Owned results | a field read that is a `Str` or a row | `.clone()`; a `String` literal gets `.to_string()` | `Dbsp.roc:633` |
| Unread parameter | `\|_sensor, r, s\|` | `\|_key, left, right\|`, so rustc has nothing to warn about | `Dbsp.roc:377` |
| Refusals | `trim`, a loop, `trim` inside a helper, `Dec` | an `Err` that names the stage and the construct | `main.roc:222` |

The first view, and the Rust it prints:

```rust
let alerts = readings
    .filter(|row| row.celsius > F64::new(80.0))
    .map_index(|row| (row.sensor.clone(), row.clone()))
    .aggregate_linear(|_| 1i64)
    .map(|(key, n)| Tup2(key.clone(), *n))
    .filter(|row| row.1 >= 3i64)
    .map(|row| Alert { breaches: row.1, sensor: row.0.clone() });
```

`bands` and `weighted` call the two helpers, and the program defines them
before `build_circuit`:

```rust
fn helper_0(p0: F64, p1: F64, p2: F64) -> F64 {
    if p0 < p1 { p1 } else { if p2 < p0 { p2 } else { p0 } }
}

fn helper_1(p0: i64, p1: i64) -> i64 {
    if p0 > 0i64 { p1 * helper_1(p0 - 1i64, p1) } else { 1i64 }
}

let bands = readings
    .map(|row| Band { cold: helper_0(row.celsius, F64::new(-40.0), F64::new(20.0)), hot: helper_0(row.celsius, F64::new(80.0), F64::new(125.0)), sensor: row.sensor.clone() });
```

The circuit has one input per name, one handle returned for each, in order of
first use, and then one output handle per view. `alerts` and `breaches` both
read `readings`, and the program declares it once.

## How it is built

A `Rel` holds a `Plan`: the input's name and a stage for each combinator, with
the `Code.Graph` of its function. Nothing runs when a combinator is called.
`Dbsp.circuit` lowers each plan stage by stage (`Dbsp.roc:197`). The stage
reads the root row of its graph as a tree (`Graph.to_tree`) and writes it as the
body of a closure (`Dbsp.roc:566`):

| Tree | Rust |
| --- | --- |
| `Param(k)` | the closure's parameter. A number is read through the reference the closure takes, so it is `*row` |
| `Op` of `Field`, `Index`, `Unwrap` | `.field`, `.0`, and nothing, because a nominal is its backing to Rust |
| `Op` of `Wrap` over a `Record` | a struct literal, `Alert { .. }` |
| `Op` of `Prim` | an operator, a method call, or a refusal (`Dbsp.roc:792`) |
| `Block` with a kept def | `let n4 = ..;`, once, where the tree defines it |
| `Op` of `Switch` on a `Bool` | `if .. { .. } else { .. }` |

The first function that reads an input fixes its row type, since an input has
no type of its own to read. That is why an input is a top-level value with an
annotation: `Dbsp.input` is `Str -> Rel(row)`, and the checker needs the row from
somewhere.

An expression carries a binding level, and a parenthesis is written only where
Rust would read the expression differently without it (`Dbsp.roc:526`). The
normal form puts a literal first in a comparison, as `80.0 < celsius`, and the
translator writes it back as `celsius > 80.0`.

## The helper function

`breach_line` calls `excess`, and the join's closure calls `breach_line`. A
translator for a language with functions might expect a `Call` row for each. It
gets none here. A `Code(f)` parameter reads the `graph` view, which keeps a
function as a row when it recurses or when two places call it, and inlines one
that a single place calls. `breach_line` has one call. `excess` has two, with
the same arguments, and value numbering merges them into one, so the
description of the join's closure is one body with each shared value kept once.

`clamp` has two calls with different arguments, and `power` calls itself, so
both stay rows. Rust has functions and recursion, so `Dbsp.roc` writes each row
that a `Call` reaches as a Rust `fn`, and a `Call` node as a call of it:

| Step | What it does | Where |
| --- | --- | --- |
| Find | `reach` walks the root row's tree for `Call` nodes, and then the rows they name, each row once | `Dbsp.roc:286` |
| Name | `define` gives a row the name of a known helper when both reach the same rows once row ids are left out, and a new `helper_N` otherwise. A second stage, or a second view, that holds the same helper therefore does not define it again | `Dbsp.roc:300` |
| Write | `render_fn` writes the row as `fn helper_N(p0: .., ..) -> ..` with the same expressions as a closure body | `Dbsp.roc:334` |
| Call | `call_helper` writes `helper_N(args)` | `Dbsp.roc:348` |

The functions come after the row structs and before `build_circuit`, in the
order they were first needed. Their names come from the order of definition,
because a row has an `id` and no name. The `id` is local to one description, so
it cannot name a function that two stages share.

Parameters and results:

| Roc type | Rust parameter | Rust call argument |
| --- | --- | --- |
| a number or a `Bool` | by value, `p0: i64` | the value, `row.celsius` |
| a `Str`, a row, a tuple | by reference, `p0: &String` | a closure's parameter as it is, anything else with `&`, and a `String` literal as `&"x".to_string()` |

The result is the `Ty` of the row's `result`, as an owned value, and a body
clones a `String` or a row it returns, as a closure does. A parameter that the
body never reads is written `_p0`. A refusal inside a helper is blamed on the
stage that calls it, like any other. The normal form orders a helper's
parameters and the operands of its comparisons, so the Rust may name them in
another order than the Roc source: `power(base, times)` becomes
`helper_1(p0, p1)` with `p0` the exponent.

A translator with no function form can declare its parameter `Code.Inlined(f)`
instead, which inlines every function that does not call itself, however many
places call it. A `Call` is then left for recursion, and for a function whose
body can still end in a `Return`. `Dbsp.roc` reads the `graph` view, because it
has a function form.

`alerts_by_name` writes the same view as `alerts`, with each lambda replaced by
the function it was a copy of. The two give the same Rust, which `main.roc`
checks:

```roc
expect Dbsp.circuit([Dbsp.view("alerts", alerts_by_name)]) == Dbsp.circuit([Dbsp.view("alerts", alerts)])
```

## A refusal names the stage and the construct

```
view `trimmed`, stage 1 (`filter`): `Str.trim` has no Rust form in this translator
view `looped`, stage 1 (`filter`): a loop has no closure form; `dbsp`'s operators are the loops, ...
view `tidied`, stage 1 (`map`): `Str.trim` has no Rust form in this translator
view `pricey`, stage 1 (`filter`): Dec has no `dbsp` column type; use I64 or F64
```

The description carries no source regions, so the stage stands for the place:
the view, the position of the combinator in its chain, and which one it is.
`Code.refuse_at` reports a node at every place in the source it came from, but
it stops the compile, where an `Err` can be tested, so this translator returns
an `Err` and leaves the choice to the caller.

Translation also refuses what a Rust column cannot hold: an optional field, a
list, a tag union, an anonymous record (declare the row as a nominal), a
nominal over anything but a record, and two row types with one name.

## One definition, three uses

`is_hot`, `is_noisy` and `to_alert` are ordinary Roc functions. `alerts_by_name`
reifies them. `main.roc` calls them directly in `expect`s on sample rows. And
the reference engine at the end of `main.roc` calls them again: a Z-set is a
`List({ row, weight : I64 })`, `step` applies a batch to the per-sensor counts
and returns the alerts that appear and go away, and `from_scratch` recomputes the
view over a whole relation. The `expect` runs three batches, the third a
deletion, and checks that

| What | Is |
| --- | --- |
| the first batch's change | empty |
| the second batch's change | two alerts appearing |
| the third batch's change | one alert going away, and nothing else |
| the three changes added together | `from_scratch` over every reading so far |

A `Code` cannot be called, so the engine calls the functions and not the circuit.
It is the proposal's argument for reification at the size of a test: a query
that is an ordinary function can be called on real values and checked against a
reference, and a DSL predicate was never a function.

## What the translator does not close

| Roc | Rust | The difference |
| --- | --- | --- |
| `+ - *` crash on overflow | panic in a debug build, wrap in a release build | not closed |
| `F64` compares by IEEE equality | `dbsp`'s `F64` is totally ordered, so `NaN == NaN` | not closed |
| `Str.trim` | `str::trim` | the two may strip different characters, so it is refused |

## Status

`roc test examples/reifying/dbsp/main.roc` passes 19 expects and
`roc test examples/reifying/dbsp/refactored.roc` passes one. `roc
examples/reifying/dbsp/main.roc` prints the program. The whole program is a
compile-time constant, so `roc check` reports

```
● unconditional condition
This match value is known at compile time
```

on the driver's `match`, which is the point.
