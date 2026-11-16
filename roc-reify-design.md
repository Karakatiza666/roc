# Code reification in Roc: the design

This article explains the design of code reification. It is for a reader who
knows Roc but has not followed this feature. It covers what the feature does,
the model a translator sees, how the compiler builds that model, and why the
design has the shape it has.

It is not a list of every construct a description covers. That list is the
checklist, `roc-reify-design-checklist.md`. The user guide is
`docs/langref/reifying.md`. The compiler-side rules and invariants are in
`design.md`, sections "Code Reification", "The Runs Bit" and "Reify-Only
Definitions". Where this article and the code disagree, the code, the tests,
design.md and the user guide are correct.

## 1. What reification is

Roc's platforms answer one question about a program: where and how do its
effects run? Nothing in Roc answered the next question: where and how does a
pure computation run? The answer was always "here, as machine code that the
Roc backend wrote".

Some pure computations must run somewhere else. A fragment shader runs on a
GPU. A query predicate runs in a database. An incremental view runs in a
dataflow engine. To send a Roc function there, a library must read the
function. A compiled Roc function is a function pointer, and a function
pointer cannot be read, translated or fused.

Reification gives the library a description of the function in place of the
pointer. The feature is one type and one rule:

| | |
| --- | --- |
| `Code(f)` | a description of a pure Roc function of type `f`, as data |
| The rule | a function that stands where the type says `Code(f)` is described, not compiled |

```roc
area : F64, F64 -> F64
area = |w, h| w * h + 1.0

# Calc.to_expr : Code(f) -> Try(Str, [Unsupported(Str)])
expr = Calc.to_expr(area)   # area is described, not called
```

There is no new syntax. The parameter type is the whole interface, in the
same way that a numeric literal takes its type from the place it stands.

A translator is the function that reads a `Code`. It is ordinary pure Roc. It
runs while the compiler runs, usually during the evaluation of a top-level
constant, and it returns data: GLSL text, a SQL script, a Rust program. The
compiler knows the word reification. It never knows the words shader, query or
Z-set. Each target is a library.

The described function stays an ordinary Roc function. The program can still
call it, test it with `expect` and step through it. The GLSL example runs its
shader on the CPU in a test and compares the result with an interpreter of the
description (`examples/reifying/glsl/`).

### 1.1 Names

The early discussions called the feature staging, and the value a typed
quotation. Both names were dropped. "Staging" already means several other
things in the compiler and in CI, and "quotation" collides with `from_quote`.
The words now are:

| Concept | Name |
| --- | --- |
| The value | `Code(f)` |
| The act of making it | reification, or describing |
| The consumer | a translator |
| The data a translator reads | the description: a `Code.Graph` in the normal form |

A translator has no special module kind. It is an ordinary package. Many
identifiers in the compiler still say `staged` (`stagedCode`,
`StagedCode`, `test/cli/Staged*.roc`); they mean the same thing.

## 2. The model

### 2.1 What a `Code` is

Every `Code` value has these properties:

| Property | Meaning |
| --- | --- |
| Typed | `Code(Person -> Bool)` holds only a function of that type. A type error in the function is an ordinary type error. |
| Pure | `Code(a => b)` is a type error. An effect has no place to happen while the compiler runs. |
| Closed | The description has no free names. Everything the function reads from outside is in the description. |
| Monomorphic | Every type in the description is concrete. A generic function is described at the types its use fixes. |
| Inert | No operation calls a `Code`. It is data. |
| Compile-time only | Only the compiler makes one. A value cannot be annotated with `Code`. |
| Comparable | Two `Code` values are equal when their normal forms and versions are equal, wherever each came from. |

`Code` is an opaque type, so user code cannot build one. A hand-built
description therefore cannot pose as one the compiler wrote. The data types
inside it (`Graph`, `Row`, `Node`, `Op`, `Ty` and the rest) are transparent,
so a translator can `match` on them. All of them are in the `Code` module of
`src/build/roc/Builtin.roc`.

### 2.2 Code places

A `Code` can stand in two places of an annotation: as a parameter of the
outermost function, and as what that function returns. Every other place is
the error `code is not allowed here`: a callback parameter, a record field, a
tuple item, a value annotation.

```roc
is_adult : Code({ age : U8 } -> Bool)   # ERROR! A Code is not allowed here
is_adult = |p| p.age >= 18
```

The fix is to write `is_adult` as an ordinary function and pass it where a
`Code` is expected. A package that wants to ship reusable reified functions
ships ordinary functions.

The checker reads code places from the annotation the user wrote, not from
the solved type. A transparent alias of a `Code`, such as
`MyCode : Code(I32 -> I32)`, is a code place too, and follows the same rule.
`Code.Binds(code, fmt)` (section 6) is an alias that is also a code place.

These forms can stand at a code place:

| Form | Example |
| --- | --- |
| A top-level function of this module or an imported module | `Calc.to_expr(area)` |
| A method declared on a type | `Calc.to_expr(Meters.twice)` |
| A function bound in a block around the call | `double = \|x\| x * 2`, then `Calc.to_expr(double)` |
| A lambda written at the place | `Sql.select_where(events, [], \|e\| e.at < cutoff)` |
| An exact alias of a function | `same = add_one`, then `Calc.to_expr(same)` |

A lambda at a code place takes its parameter types from the call before its
body is checked, the same as a lambda argument of an ordinary function. So a
field read and a method call on a parameter both resolve.

The view is chosen by the parameter type. `Code(f)` gives the `graph` view,
and `Code.Inlined(f)`, `Code.Outlined(f)` and `Code.Lawful(f)` give the
others (section 3.2).

### 2.3 Templates

A function that returns a `Code` is a template. The compiler calls it while
it runs, and does not compile it. It writes each argument of the call into
the lambda the template returns, so one template gives one description per
call.

```roc
add_k : I64 -> Code(I64 -> I64)
add_k = |k| |x| x + k

Calc.to_expr(add_k(5))   # Ok("(p0 + 5)")
Calc.to_expr(add_k(7))   # Ok("(p0 + 7)")
```

Each argument must be fixed at build time: a literal, a name bound to one, an
aggregate of those, or a function. An argument that the program computes when
it runs is the error `template needs a constant`, reported at the argument.

A call is a template call only when the callee's own return type is a `Code`.
A generic function that receives a `Code` and returns it, such as
`pick : Bool, a, a -> a`, is an ordinary call.

### 2.4 Query fragments and instance descriptions

A query fragment is a generic function that holds a code place whose type
names the function's own type variables:

```roc
named_only : Db.Q({ name : Str, ..r }) -> Db.Q({ name : Str, ..r })
named_only = |q| q.filter(|x| x.name != "")
```

The lambda has no single type, so it has no single description. A
description is monomorphic, and an open row has no shape to write. The
design calls such a code place an instance site. It has no description of its
own. Each closing use of the fragment describes the lambda at the types that
use fixes, in the module of the use. `named_only(pets)` describes it at `Pet`,
and `named_only(owners)` describes it again at `Owner`. A use is a call, a
method call, a lookup of the fragment as a value at a fixed type, a constant
that holds the fragment, a fragment that calls a fragment, and a `for` loop
over a type whose `iter` is a fragment.

The checked module builder records these descriptions in an instance table
(`CodeInstanceTable`), keyed by template and instantiation, so equal
instances share one table. Monotype and Boxy read the table in force where
the program runs the fragment. Boxy lowers the fragment once and passes the
table as one hidden argument, as it passes a literal argument: the caller
that fixes the types supplies it. `Code.ty_of` and `Code.type_id` calls (section 5) whose proxy type
names a type variable of the function around them are entries of the same
table.

A refusal inside a fragment can only be found at a use, because that is the
first place a description exists. The report points at the source inside the
fragment and names the use that reached it.

A method that a `where` requirement or a codec derivation selects is
described at the evidence edge that selects it, at that edge's types.
`encoder_for`, `parser_for` and the methods of a format work this way. A
`to_inspect`, `is_eq` or `to_hash` method is also described at each place
that writes a type of its owner, because the compiler calls it with no
written use.

Three forms are refused by name:

| Form | Report | Why |
| --- | --- | --- |
| A fragment whose translator binds captured values and whose chain reads a run-time value outside a lambda | `cannot bind inputs in a generic function` | the chain has no one value to run with while the compiler runs |
| A fragment that the compiler selects from a type alone, through evidence that a node derives from its callable | `cannot reify in a method selected from a type` | no checked evidence node names the method, so no edge describes it |
| A translator that binds inputs at the type variables of `to_inspect`, `is_eq` or `to_hash` | `cannot bind inputs in a method the compiler calls` | its input slots need a written call, and the compiler's own call is not written |

A use inside a function that a block made generic is also refused
(`cannot reify in a local generic function`).

The design of instance descriptions is D1 of
`roc-reify-structural-proposal.md`.

## 3. The description

### 3.1 Graphs, rows and nodes

A description is a graph of functions. Each function is a row.

| Type | What it holds |
| --- | --- |
| `Graph` | `{ root, rows, slots }`. The root row is the function that was passed. `slots` are the types of the input slots (section 6). |
| `Row` | One function: `id`, `params` and `result` (as `Ty`), `nodes`, `body`, `recursive`. |
| `Node` | One operation: `op`, its arguments `args`, its type `ty`, and `speculatable`. |
| `Val` | What a node reads: `Param(k)`, `Node(i)`, `Out({ node, k })`, `Arg({ owner, k })` or `Input(k)`. |
| `Region`, `End` | A body and how it ends: `Value`, `Jump`, `Return`, `Continue`, `Break`, `Branch`. |
| `Tree` | One row as nested expressions, from `Graph.to_tree`. |

There are 24 ops. They group as constants (`Lit`), builtin and primitive calls
(`Prim`), calls of rows (`Call`, `Closure`, `Lambda`), construction (`Record`,
`Tuple`, `List`, `Tag`, `Wrap`), reads (`Field`, `Index`, `Payload`, `Item`,
`OptField`, `Unwrap`), choice (`Switch`, `And`, `Or`), loops (`ForRange`,
`ForList`, `Loop`) and the rest (`Crash`, `Derived`).

For `area = |w, h| w * h + 1.0` the graph has one row with three nodes:

| Index | `op` | `args` | `ty` |
| --- | --- | --- | --- |
| 0 | `Prim` `Num.F64.times` | `Param(0)`, `Param(1)` | `F64` |
| 1 | `Lit(Frac(1, F64))` | none | `F64` |
| 2 | `Prim` `Num.F64.plus` | `Node(0)`, `Node(1)` | `F64` |

The body ends in `Value([Node(2)])`. The names `w` and `h` are gone, and no
source region is in the description.

The description is first order. There is no node that applies an arbitrary
function value. A function passed as a value is a `Closure` of a row, and the
walk resolves every call to a known row or primitive. A call it cannot
resolve refuses the site.

A binding has no node of its own. The node that computes the value is the
binding. A value read more than once stays one node, so shared work stays
shared, and `to_tree` keeps such a node as a `Def`.

`speculatable` says whether a translator may evaluate the node where the
source would not, for example in a target with no short-circuit evaluation.
It is exact: only builtins on the normal form's list are speculatable, and a
package primitive never is.

### 3.2 Views

Different targets want different amounts of structure. A view decides which
functions stay rows.

| View | Parameter type | What stays a row |
| --- | --- | --- |
| `graph` | `Code(f)` | a recursive row, a row called from two or more places, a row a `Closure` names, a row with a `Return` in a loop or a switch arm |
| `inline` | `Code.Inlined(f)` | a recursive row, a row with a `Return` in a loop or a switch arm. Every other call is inlined. |
| `outline` | `Code.Outlined(f)` | the rows of `inline`, and one row for each computation of at least four nodes that occurs at two or more places |
| `lawful` | `Code.Lawful(f)` | the rows of `graph`, after the laws of the builtins (layer L) |

A single-expression target such as a fragment shader reads `inline`. SQL with
common table expressions reads `graph` and keeps each `Call`. A target whose
functions must not change when the author moves code into or out of helpers
reads `outline`: its rows are chosen by the compiler with anti-unification, so
`step(input.a)` and `step(input.b)` call one row. Only `lawful` applies the
laws: a loop that appends to an empty list is `List.map`, a `map` of a `map`
is one `map`, and `len() > 0` is `!is_empty()`.

A row with a `Return` inside a loop or a switch arm is never inlined, because
inlining it would make the caller return the callee's value.

The view rules are in `src/reify/views.zig`, and the laws in
`src/reify/laws.zig`.

### 3.3 The normal form

The description is a normal form. Two ways to write one computation give one
graph. A translator therefore sees fewer forms than the source has, and some
of them are not the forms the author wrote:

| Written | Described as |
| --- | --- |
| `"Hello, ${name}!"` | one n-ary `Prim` `Str.concat` with three arguments |
| `x >= 10`, `x > 10` | `is_lte` and `is_lt` with the operands swapped; there is no `is_gt` or `is_gte` |
| `a != b` | `Bool.not` of `is_eq` |
| `1 + x` | `plus(x, 1)`: a literal comes last in an integer `plus`, `times` or `is_eq` |
| `a and b`, `a or b` | an `And` or `Or` node; each operand after the first is a region, so it short-circuits |
| `t?`, `t ?? 0`, `match t { Ok(v) => .. }` | `Unwrap` of the `Try`, then a `Switch` on `Err` and `Ok` |
| `for`, `while`, tail recursion | `ForRange`, `ForList` or `Loop`, with the carried `var`s as numbered slots |
| `return`, `x?` inside a body | an exiting `Switch` whose arms end in `Return` or a `Jump` to the join |
| derived `==` on a record | `And` of the field comparisons, in field-name order |

A rule of the normal form holds for every `Code` of one `Code.version`. A new
version can add, change or remove a rule. So a translator matches the forms
it knows and refuses the rest by name.

The rules are numbered (`N1` and onward) in `roc-reify-normal-form.md`, and
the plan that produced them is `roc-reify-normalization-plan.md`. The rules
are a rule table plus rebuild passes in `src/reify/` (`rules/table.zig`,
`loops.zig`, `scalar.zig`, `lists.zig`, `ranges.zig`). An offline tool,
`zig build reify-rules` (`src/reify/derive/`), searches for missing rules by
critical pairs and enumeration (`roc-reify-rule-derivation.md`).

The semantics the normal form keeps is called C2: the result equals Roc's
result wherever Roc does not crash or diverge, and a description never
evaluates what Roc would not. Only speculatable nodes move. A `crash` the
author wrote stays. A crash the compiler wrote, such as a literal rejected by
its own conversion, is a `Crash` of kind `rejected_literal`, and rule N13w
drops the tests that only lead to it.

The normal form is checked in several ways: a verifier of each graph
(`src/reify/verify.zig`), a reference evaluator that compares a description
with Roc (`src/reify/eval.zig`), and fuzzers that generate small typed terms,
apply random refactors and assert equal normal forms (`src/reify/fuzz_gen.zig`,
`src/compile/reify_fuzz.zig`).

### 3.4 Types

Every node carries its `Code.Ty`. A `Ty` is one of the scalar types, `Bool`,
`Str`, `ListOf`, `Record`, `Tuple`, `Fn`, `TagUnion`, `Named`, `Recursive` and
`Opaque`.

- A type alias is resolved. It never appears in a `Ty`.
- A transparent nominal is `Named(name, args, backing)`. `args` are the type
  arguments of the use, in the order the declaration lists its variables, and
  `backing` is read at those arguments. An argument that the backing does not
  hold is kept: with `Id(row) := { table : Str, key : Str }`, an
  `Id(Customer)` carries `Customer` in `args`, so a translator knows which
  table it points to.
- An opaque nominal, and a builtin with no shape (`Dict`, `Set`, `Box`,
  `Iter`, the SIMD vectors), is `Opaque(name, id, args)`. It has no backing.
  The `id` is its `Code.TypeId` (section 5).
- A recursive type is a `Named` whose backing holds `Recursive(name)` where it
  reaches back. A translator resolves the name against the innermost enclosing
  `Named`. Roc refuses recursive aliases, so every recursion goes through a
  nominal.
- A tag union lists its variants in name order, each with its payload types.
- A record lists its fields in name order. A record extended by a
  record-backed `:=` nominal (`Labeled(r) := { label : Str, ..r }`) arrives
  with every field, the nominal's fields included.

Types are read by Monotype's rules, so the walk commits nothing to the solved
types. A numeral with no other type defaults to `Dec`, as in compiled code. An
open record or tag row seals to the row default that checking recorded, as
Monotype seals it, so `|r| r.id > 0` describes `r` as `{ id : Dec }`. A
function whose types nothing fixes, such as `|x| x`, is refused as
polymorphic. A default that does not fit its use, as in `|x| x * 2.U8`, is
refused rather than described at a type the program never has.

`Code.ty_of(proxy)` gives the `Ty` of a type without a lambda, for a
translator that only needs a schema.

### 3.5 Tag names and union width

A tag is identified by its name, not by its index in a union. So a value does
not change when it moves to a wider union, and the description has no node
for widening. A value of a narrower union conforms to a wider slot. A tag
`Switch` has one arm per variant of its scrutinee's own union, in name order.

A translator that matches tags by name needs nothing more. A translator that
numbers tags per union, such as a C or GLSL struct, converts where the type
of a child is narrower than the type of its slot. Inside the walk, tag names
are interned ids. Hashes were rejected because a collision would select the
wrong arm without an error. An earlier `Op.Widen` node was removed, because it
carried no meaning for a translator and broke refactor safety. The decision
is `roc-reify-tag-names.md`.

### 3.6 Records, optional fields and defaults

Each field of a `Ty.Record` has a `presence`:

| `presence` | Field | Means |
| --- | --- | --- |
| `Required` | `id : Str` | every value has it |
| `Optional` | `note ?: Str` | a value may not have it |
| `Default(value)` | `stock : I32 ?? 0` | every value has it; `value` is the default as a `Code.Value` |
| `DefaultComputed` | `label : Str ?? made({})` | every value has it, but the type does not carry the default |

A default is `Default(value)` when it is a literal, or a list, record, tuple,
tag or nominal of literals, or the name of a constant that holds one.
Anything else is `DefaultComputed`. The default is part of the type, so two
nominals that differ only in a default are two different `Ty` values. A
schema translator writes `Default(value)` as a column default and refuses
`DefaultComputed` with advice.

A record literal that leaves out a field with `Default(value)` is described
with the default filled in, as the program fills it when it runs. One that
leaves out a `DefaultComputed` field is refused.

An optional field is read with `OptField`, which gives the `Try` the value
sits in. A `Record` node lists the members it sets when its type has an
optional member, so a literal that leaves one out has one form. A record
update and a record pattern rest over an optional field are a `Switch` on its
`OptField`, so the description decides what Roc decides at run time. Derived
equality over an optional field compares the two `Try` values: two records
that both lack the field are equal there.

## 4. Calls, primitives and the cut

### 4.1 What is walked and what is a `Prim`

A description is closed, so the walk follows every call into its callee and
describes the callee as a row. It does this across modules and across
packages. A call in another module is read from that module's published
view, so the graph also reaches a module the described one never imports.
A row has no name. The graph holds every module it reaches under one
numbering.

Some callees are not walked. They are a `Prim`, named and identified, with no
body. One step classifies every definition the walk reaches, the same on the
direct-call, method-call and constant paths (`primitiveOf` in
`src/check/code_reifier.zig`):

| Definition | Described as |
| --- | --- |
| An intrinsic (section 8) | a `Prim`, always |
| A function of the builtin module | a `Prim` under its export name, such as `Str.concat` |
| A constant of the builtin module | its value, folded |
| A function or constant whose type names an opaque (`::`) type of its own module | a `Prim`, such as `Time.is_before` or `Time.epoch` |
| A function in the translator's cut | a `Prim` named by its nominal and item |
| Anything else | walked by its body |

The rule for opaque types follows from opacity. The body of `Time.is_before`
reads the representation that `Time` hides, so a description that walked it
would expose what Roc itself hides from the caller. The test reads only
explicit data: the module's role, the nominal's opaque flag, its declaring
module and the definition's checked type. A function of that module whose
type does not name the type, such as `Time.days_in_week : U8`, is walked like
any other. A walked body that builds a value of an opaque type from its
fields is refused.

A primitive function is a `Prim` over its arguments, and a primitive constant
is a `Prim` with no arguments. One definition has one name and one id
whichever path reaches it, so `Time.is_before(t, c)`, `t.is_before(c)` and
`t < c` give the same node. A package primitive gets no law, no fold and no
speculation. Only builtins have laws, because only they have a reference
evaluator that checks the law.

A builtin that the normal form has a node for is folded into that node:
`Bool.not` is one `Prim` however it is spelled, and `and` and `or` are `And`
and `Or`.

### 4.2 The cut and `code_primitives`

A translator sometimes wants a function by name, even though its body is
readable. A GLSL translator keeps a math library's `lerp` as GLSL's `mix`. A
SQL translator reads the same body. So the cut belongs to the translator, not
to the library. The translator declares it with an item named
`code_primitives` on its type:

```roc
Glsl :: {}.{
    code_primitives = [Code.prim(Vec3.scale), Code.prim(Vec3.plus), Code.prim(Sampler.texture)]

    fragment_330 : Code.Inlined(f) -> Try(Fragment, Error)
}
```

The item has the type `List(Code.PrimId)`. Each entry is `Code.prim` of one
top-level function or constant. The item may also be the name of a constant
of the same module that holds such a list, so several translator types can
share one cut. A constant of another module is not read this way. The older
tuple form is a type error whose hint says to wrap each entry in `Code.prim`.

The cut is explicit data. The checker records which call a code place is an
argument of (`CodeReificationSite.translator`). For a method call it reads
the method from the dispatch plan, never from the method's name. The walk then
reads the cut of the nominal that owns that translator. Two sites with
different cuts share no normal form they do not both build.

The reports for a bad cut are `not a primitive`, `cannot read this cut`,
`primitive listed twice` and `already a primitive`. The last one is for a
builtin, an intrinsic, or a function of an opaque type, which is a `Prim`
already.

The tradeoff of the cut is reach. A dependency's body is part of what a
translator reads. If an upgrade changes the operations of a function that a
described function calls, the translation can change, or the build can stop
at the call with a report that names it. Upgrades are explicit, because
packages are pinned by URL and content hash.

### 4.3 Calls the walk resolves

The walk resolves each call at the place that fixes it:

- A generic callee is described once per instantiation. `id` called at `F32`
  and at `U64` is two rows. The row key is a digest of the types the call
  fixed.
- A function parameter that a call fixes binds to the definition it names.
  `apply_to(double, x)` and `apply_to(triple, x)` are two rows.
- A function chosen by an `if` between known functions becomes a `Switch`
  over the calls.
- A top-level value that computes a function, `doubler = make(2.0)`, is read
  by its definition where the name stands, so `doubler(x)` is a call of the
  lambda inside `make` over the capture `2.0`.
- A top-level constant is folded into the description, as a literal or as the
  computation its definition writes. `x > limit` with `limit = 7.0 * 2.0`
  describes as `x > 7.0 * 2.0`.
- A value that the block around a lambda binds is replayed at the head of the
  lambda's body.
- A function value that is a parameter of the function around the lambda
  has no body until the program runs, and each call can pass a different
  one. A read of it is refused by name ("cannot reify a function
  parameter"). The report says what to write instead: a `Code(f)`
  parameter passed on, a template, or named functions.
- A name that the block around a lambda binds to a call that hands back a
  function, `pred = above(n)`, is that call where the lambda calls the name:
  `pred(x)` is the call `above(n)(x)`, one `Call` of the row that gathers the
  parameters of both lambdas.
- A literal of the author's own type is the call of its conversion
  (`from_numeral`, `from_quote`, `from_interpolation`), over the digits or the
  text the author wrote.

### 4.4 Evidence

A builtin such as `List.sort` or `Dict.get` has a `where` clause. A
translator must know which method answers each requirement at this call. A
`Prim` therefore carries `evidence`: one `Code.Evidence` per requirement, in
the order of the clause, each with the `method`, the type `ty` it is called
on, and a `target`:

| `target` | Means |
| --- | --- |
| `Prim(..)` | a primitive, with its own `evidence` |
| `Row(id)` | a method with a body; row `id` is that body |
| `Derived(method)` | a method the compiler derives for the type |
| `Unreachable` | no value of `ty` can reach the call |

`xs.sort()` over `List(I64)` has the target `Prim(Num.I64.order_relative_to)`.
Over a type that writes its own order, the target is a `Row`. A translator
checks that the order is one its target has before it emits its target's sort.

The walk reads the evidence that the checker recorded. It plans no dispatch.
A call whose evidence the compiler leaves to a later stage is refused. Without
evidence, a translator would have to assume the natural order, which is a
wrong translation with no error.

### 4.5 Derived methods

The six derivable methods are `is_eq`, `to_hash`, `parser_for`,
`encoder_for`, `map` and `map!`. The rule is: who must the result agree with?

- `is_eq` and `to_hash` must agree with Roc. That knowledge is the compiler's,
  so a derived `is_eq` is expanded into the comparisons it performs. A
  derived `to_hash` is expanded where the description reaches far enough, and
  is `Derived` otherwise.
- A codec answers to a format that the translator owns. `parser_for`,
  `encoder_for`, `map` and `to_inspect` stay a `Derived(method, type)` node.
  A translator that owns the format expands it, and every other translator
  refuses it by name.

Through an opaque nominal, a derived `is_eq` stays `Derived`, because
expanding it would describe the hidden representation.

## 5. Identity

### 5.1 Ids, not names

A name is for messages. Two packages can each have a `Time.is_before`, and a
module can declare its own `Bool` with its own `not`. So each `Prim` carries a
`Code.PrimId`, and each `Opaque` type carries a `Code.TypeId`. Both are 128-bit
hashes of the identity the compiler already keys the definition by. They are
made only in `src/reify/identity.zig`:

| Identity | Hashed |
| --- | --- |
| builtin primitive | owner and method (`Str`, `concat`) |
| package primitive | the checked module digest of its module, and the definition |
| builtin nominal | the name its `Ty` spells (`Dict`) |
| declared nominal | the content identity of its module, and the declaration |

A translator gets the same ids from source with three intrinsics of the
`Code` module:

| Call | Gives |
| --- | --- |
| `Code.prim(Time.is_before)` | the `PrimId` of each `Prim` that calls `Time.is_before` |
| `Code.type_id(proxy)` | the `TypeId` of the opaque type of the proxy |
| `Code.ty_of(proxy)` | the `Ty` of the proxy's type |

```roc
time_proxy : Code.Proxy(Time)
time_proxy = Code.proxy()

is_time : Code.Ty -> Bool
is_time = |ty| match ty {
    Opaque(_, id, _) => id == Code.type_id(time_proxy)
    _ => Bool.False
}
```

Roc has no type arguments, so a `Code.Proxy(t)` with an annotation stands for
the type. `Code.prim` does not call or instantiate its argument, so a generic
function with a `where` clause can be named. The compiler computes each id at
publication and stores it as a constant. The three are only ever called;
passing one as a value is `call this function`. `Code.prim` of a local, a
parameter or a computed function is `not a definition`, and `Code.type_id` of
a proxy whose type is not nominal is `not a nominal type`.

An id comes from the module that declares the definition, contents included.
An edit to that module gives new ids. Ids are not meant to be stored across
builds. The glue package and the app are compiled in one build, so
`Code.prim` and the `Prim` nodes always agree.

A `Named` type carries no `TypeId` yet. That is open.

### 5.2 Extending a translator

A translator knows the builtins. It cannot know every package. A glue package
tells a translator what the functions and types of another package mean in
its target. It exists apart from both, because a package cannot add methods to
another package's type, and it cannot change the translator's source.

The translator takes the extensions as ordinary values, keyed by id:

```roc
extension = Sql.extension({
    prims: [
        { prim: Code.prim(Time.is_lt), render: TimeSql.binary("<") },
        { prim: Code.prim(Time.is_eq), render: TimeSql.binary("=") },
    ],
    types: [{ type: Code.type_id(TimeSql.time_proxy), column: "BLOB" }],
})
```

The extension type belongs to the translator. The language gives only the
ids. The translator cannot check what a glue package claims: the SQL above is
correct only because the translator writes a `Time` as bytes that sort as its
nanoseconds do. The design is D6 of `roc-reify-opaque-proposal.md`.

### 5.3 Rows, nodes and equal descriptions

Rows have no names. A row is keyed by its content digest, and recursive
groups are hashed as a unit. Rows that are equal merge. The order of
`row.nodes` comes from the graph alone, so a rename or a reordered binding
keeps every node index. `Code.Inlined.inline_digest` gives each node of the
`inline` view a content digest that also survives helper extraction, for a
translator that needs stable operator ids.

`Code.is_eq` and `Code.to_hash` read the normal form and the version, never
the site. So two places with equal descriptions give equal `Code` values, and
a translator can key a cache with `Code.to_hash` and `Code.version`.

## 6. Captured values

A lambda may read a value that exists only when the program runs:

```roc
before = |cutoff| Sql.select_where(events, [TimeSql.extension], |e| e.at < cutoff)
```

The description is built before `cutoff` exists. A translator that returns a
`Code.Bound(result)` accepts such a lambda. It still runs once, while the
compiler runs, and writes a placeholder for each value it cannot know, such as
a `?` in SQL. In the description, each such value is an input slot,
`Input(k)`. Each call of `before` then gives the program a `Code.Bound` whose
`inputs` holds one `Code.Value` per slot. The translator writes
`Code.bound(code, result)`, and the program adds the inputs.

The rules:

- A slot is a value the description reads whole. A lambda that reads only
  fields of a captured record gets one slot per field path. One that also
  reads the record whole gets one slot for it, and reads its fields as
  `Field` of that slot's `Input` (rule N18e).
- A `Code.Value` follows the slot's type. An optional field the record does
  not hold is `Absent`.
- Where the translator does not return a `Code.Bound`, the read is refused as
  `reified function captures a value`.
- A `var` is never a slot, because its value at the call is not always the
  value the description reads.
- The lowering of the call reads only the slots the walk recorded
  (`CheckedCodeBinding`). It plans nothing.

A value of an opaque type cannot be a structural `Code.Value`, because its
fields belong to its package. A translator that wants such values names a
format with `Code.Binds`:

```roc
select_where : Table(row), List(Extension), Code.Binds(Code(row -> Bool), Param) -> Code.Bound(Try(Str, Error))
```

`Code.Binds(code, fmt)` is a transparent alias of `code` with a phantom
`fmt`, so no existing signature changes. At such a place, the checker adds
the requirement `t.encoder_for : fmt -> (t, List(U8) -> Try(List(U8), []))`
for each captured value read as a name or a field path, and `fmt.default`
once for the site. These are ordinary `where` requirements, generated as
constraints, not a rewrite of solved types. A slot whose type holds an opaque
type arrives as `Encoded(bytes)`, in the translator's own format. A captured
function needs no encoder, because it is described as code. A type the format
cannot encode is the error `cannot bind captured value`, at the read.

The design is section 10.1 of `roc-reify-proposal.md` and D5 of
`roc-reify-opaque-proposal.md`.

## 7. Translators: reading and refusing

### 7.1 What a translator does

A translator is a function from a `Code` to data. It walks `row.nodes` and
`Val`, or a `Tree` from `to_tree`, and emits its target. It matches the ops
and types it knows. For everything else it refuses, by name.

The compiler reifies and the translator validates. The compiler never asks
whether a target can run `Str.split_on`. A construct a target cannot run is
still described, because a named node costs one translator a refusal, while
a compiler refusal would cost every author the construct.

### 7.2 Two ways to refuse

| | Return an `Err` | `Code.refuse_at` |
| --- | --- | --- |
| Written as | `Err(Unsupported(reason))` | `code.refuse_at({ row: row.id, node: index }, reason)` |
| The user sees | what the caller does with the `Err` | a `translation refused` report at every source place of the node |
| Testable with `expect` | yes | no, the compile stops |
| At program run time | the same | a crash with the message |

The description holds no source regions, so a translator cannot branch on
them. The compiler keeps a provenance table from each node to its source
places (`src/reify/provenance.zig`, `CodeProvenanceTable`). `refuse_at` is the
only reader. It names a row and a node index, and the compiler reports the
message at every source place the node came from, with the calls that reached
it. Each view has its own `refuse_at`, because node indexes differ between
views.

```
── ✗ translation refused ────────────────────────────────────── refused.roc:6:12

A translator refused code that this expression built.

root = |x| x.sqrt() + 1.0
           ^^^^^^^^

The translator gave this reason:

    `sqrt` has no operator here
```

When the refused node is a `Prim` that names an intrinsic, directly or
through its evidence, the report adds one line per intrinsic: it has no Roc
body, and a translator binds it by id, as it binds a builtin. The translator
writes nothing for this line. The bit comes from the compiler's own record of
the primitive (`ir.NamedPrim.intrinsic`) through the provenance table. No
rule, digest, numbering or view reads it, and the `Prim` has no field for it.

### 7.3 Reports of the walk

A function the walk cannot describe gives one report, and its site becomes a
`runtime_error` in the checked body. So no later stage meets a site with no
description, and no later stage reports it again. The program still runs, and
crashes only if it reaches that site, like any other Roc compile error.

Each report names its construct. A refusal inside another module's source is
shown in that module's file, followed by the place in the reporting module
that reached it. Every frame prints as `path:line:col`. The report for a type
variable left open names the variable as the annotation wrote it, the place it
stands in, and a fix that follows the cause. The full list of reports is in
`docs/langref/reifying.md`, "Every Report".

## 8. Where reification runs

### 8.1 The stages

Reification is not a stage of its own. It runs inside the publication of the
checked module, after solving and before every post-check stage.

| Stage | What it does with a description |
| --- | --- |
| Checking | types a function at a code place as usual, records a `CodeReificationSite`, and enforces the position rule (`src/check/Check.zig`) |
| Description | walks each site's checked bodies, solved types and dispatch plans, builds the normal form with `src/reify/`, and writes the `Code` into the module's `ConstStore` (`reifyStagedCode`, `src/check/code_reifier.zig`) |
| Lowering | restores the stored node as a constant, or the node the instance table names. It walks no function. |
| Evaluation | runs the translator as any other Roc, usually while it evaluates a top-level constant. `Code.refuse_at` lowers to a crash statement that carries a `Refusal`. |

A translator's result that a top-level value holds is stored in the binary as
a constant. A translator also runs during `roc check`.

### 8.2 Invariants

- The walk is the only stage that reads a function body for a `Code`. It
  consumes solved types and dispatch plans and never infers a missing one. A
  construct with no normal form stops the walk with a named reason. No
  partial description exists.
- A description is a specialization read without lowering. The walk reads
  types by Monotype's rules, and checking commits nothing for it.
- Later stages treat a description as a constant. They never read its rows
  and never rewrite it.
- Backends know nothing of reification.

### 8.3 Caching and `normal_form_version`

A description is part of the checked artifact, so the module cache stores it
and a cache hit replays it. An artifact key hashes the keys of its imports,
and every call the walk follows resolves through an import, so a change to a
callee's module rebuilds the description.

`normal_form_version` in `src/reify/mod.zig` names the rules. It changes
exactly when the rules, the builtin table or the speculatable lists change. A
fingerprint test pins each version, and a recorded entry is never edited, so a
rule change without a version bump fails the test. Every `Code` carries the
version, and `Code.version` returns it, so a translator can key its own cache
with `Code.to_hash` and `Code.version`. A change to the stored layout also
moves the compiler's `CACHE_VERSION` (`src/compile/cache_config.zig`).

The translator's result is not cached between runs of `roc check`. A slow
translator makes both `roc check` and `roc build` slower.

## 9. Intrinsics and reify-only definitions

### 9.1 Intrinsics

Some operations of a target have no meaning in Roc: a search score, a session
value, a database's clock, a GPU texture fetch. Others have a meaning that
nobody has written in Roc yet. Before intrinsics, such a function needed a
Roc body, so its author wrote `crash "runs in the database only"`, and misuse
failed only when the program ran.

An intrinsic is a declaration with a type and no body, outside the builtin
module and outside a platform:

```roc
Text :: {}.{
    is_email : Str -> Bool
}
```

It checks, infers and dispatches like any function. It can be a method and
can have a `where` clause. Nothing says what it computes. Only a translator
gives it a meaning. A bodyless declaration in a platform module stays hosted,
and one in an app or a package is an intrinsic
(`AnnotationOnlyKind.intrinsic`).

At every code place an intrinsic is a `Prim`, whatever the translator's cut
says. A translator binds it by id, the same as a builtin:

```roc
{ prim: Code.prim(Text.is_email), render: TextSql.call("is_email") },
```

A translator sees no difference between the `Prim` of an intrinsic and any
other `Prim`. It has the same fields, and the normal form is the same. An
earlier plan gave `Prim` a field `body : [Roc, Intrinsic]`. It was dropped by
decision: a target binds a primitive by id in either case, and the one place
where the difference helps a user, a refusal, gets it from the compiler
(section 7.2).

An intrinsic must be called in a description. Used as a value
(`xs.map(Text.is_email)`) or named as the function to describe, it is refused,
as a function in the cut is. Listing one in `code_primitives` is
`already a primitive`.

### 9.2 Description-only bodies and the runs bit

An intrinsic is legal in code that is described and never run. The checker
must know which code that is. A body is description-only when it is:

- the body of a lambda written at a code place;
- a function name written as a `Code` argument, or as the callee of a template
  call;
- the whole body of a template, which the reifier walks as code to describe
  at each call.

The checker counts the description-only bodies around the expression it
checks, and records the root of each such subtree.

Generic code needs more. In `inner = |x| x.now()` the method `now` is chosen
only where a use fixes the type of `x`. So each static-dispatch constraint has
a `runs` bit: it is set when some code that runs uses the relation.
Compile-time evaluation counts as running. A constraint created outside every
description-only body runs. An instantiation ANDs each copied constraint's bit
with the bit of the use. Two merged relations OR their bits. The bit is
metadata: unification, type keys and constraint equality do not read it, so it
never changes typing. The over-approximations are declared in design.md, and
each can only set a bit that could be clear, so a reader can only reject more
code, never accept code it must reject.

### 9.3 Reify-only definitions

A top-level definition is reify-only when code of it that runs references an
intrinsic or another reify-only definition. The rule is inferred, never
annotated.

The pass `src/check/reify_only.zig` finds these definitions once, after the
module is checked. It reads only data that checking produced: the checked
bodies minus the description-only subtrees, the lookups, and the dispatch
edges, each with the final `runs` bit of the relation it resolves. The
fixpoint is breadth-first and least. Each marked definition records a
witness, its first reference to an intrinsic or to a definition marked in an
earlier round. So the chain of witnesses ends at an intrinsic and has no
cycle, and a mutually recursive group that reaches no intrinsic stays
unmarked.

A reify-only definition is fine as long as only described code uses it. It is
walked by its body like any helper, and nothing lowers it.

```roc
valid = |s| Text.is_email(s)

described = Calc.count(|s| valid(s))   # fine: the translator reads valid
```

A generic function is reify-only only at a use that fixes its type to one
whose method is an intrinsic. A call of `outer` at a type whose `now` has a
body is fine.

### 9.4 The roots rule

A root is a definition whose code runs whatever references it:

- a platform requirement the app supplies, an entry of the module's provides
  list, and a zero-argument definition the caller records as an evaluated
  root. The checker reads these from the module header, the platform and the
  caller. It never finds a root by its name, such as `main!`;
- a top-level constant, which compile-time evaluation runs;
- a top-level `expect`.

A root is never reify-only. A reference in a root that runs and reaches an
intrinsic or a reify-only definition is the error
`exists only in reified code`, at that reference. The reference is poisoned, so
it lowers to a crash and nothing behind it is lowered. The report prints the
chain from the reference to the intrinsic, one line per witness:

```
── ✗ exists only in reified code ────────────────────────────── main.roc:15:20

This call runs when the program runs, but it reaches an intrinsic, which has no
Roc body.

echo!(Str.inspect(valid("a@b.c")))
                  ^^^^^^^^^^^^^^

valid calls Text.is_email at main.roc:10:13
Text.is_email is an intrinsic at main.roc:7:2

An intrinsic exists only inside a function that a translator describes. Pass
the function where a Code is expected, or give Text.is_email a Roc body.
```

A use as a value has the first line "is used here as a value, but it reaches
an intrinsic". The error behaves as every checking error does: `roc check`
exits 1, a dev run crashes only if it reaches the reference, `roc build`
writes the binary and exits 1, and `roc test` counts an `expect` with the
error under compiler errors.

Two invariants follow, each a debug assertion and `unreachable` in release
builds: Monotype lowering never reaches an intrinsic, and the reifier never
asks for an intrinsic's body.

One case needed a rule in Boxy. Boxy fills a dictionary slot for each
relation of a callee's scheme. A fragment `|q| Db.Q.filter(q, |x| x.t.now())`
has `now` in its scheme, but only the described lambda uses it. At `Clock`,
whose `now` is an intrinsic, the evidence is marked
`description_only_target`, and Boxy gives the slot a crashing value in
place of a worker. No run-time code reads it. The same holds for a slot
whose target is a reify-only definition or a function that returns `Code`,
and for a nominal's `is_eq`, `to_hash` or `to_inspect` override that is an
intrinsic. The checked module flags each such template, and Boxy emits no
worker for it.

### 9.5 Across modules

`ModuleEnv.reify_only_defs` exports each reify-only definition with its
witness and its full chain of frames. An importer appends the exported chain
at an imported reify-only definition. So an app that imports `Lib` and not
`Text` still names `Text.is_email` and its place. The module cache keeps these
tables, and the checking interface hashes them, so an importer is checked
again when a frame it reports changes.

### 9.6 Tools

The declaration is the marker, so every listing is exact. All tools read one
predicate, `ModuleEnv.isIntrinsicDef`.

| Tool | Gives |
| --- | --- |
| `roc check --intrinsics` | after the check, one line per intrinsic of the checked modules, imported packages included: `pa/Text.roc:3:2 Text.is_email : Str -> Bool`, sorted by file and line. The exit code is the one of `roc check`. |
| `roc docs` | the badge `intrinsic: no Roc body` next to the signature |
| The language server | the same badge on hover over an intrinsic or a use of one |
| `ROC_REIFY_ONLY` | in Debug and `-Ddev-diagnostics` compilers only: each definition's requirements with their `runs` bits, and each reify-only definition with its witness |

### 9.7 Giving an intrinsic a body later

Adding a body is a local change. The declaration gains a body and nothing
else changes. Its id stays, because the id is keyed by the declaration, so a
translator's table still finds it. Callers outside code places start to work,
and the reports about it go away.

### 9.8 A known over-approximation

The rule is per definition, not per value. In `doubler = make(2.0)` with
`make = |k| |x| Text.is_close(x, k)`, evaluating the constant only builds a
closure. It never calls the intrinsic. It is still an error, because `make` is
reify-only. Making it exact would need reify-only-ness on function types, as
effects are on `=>`. The fix for the author is to call `make` at the code
place: `Calc.count(|x| make(2.0)(x))`.

The design is `roc-reify-translator-only-proposal.md`. Its plan for a
`Prim.body` field was not adopted (section 9.1).

## 10. Refactor safety

A translator reads the program. So a refactor that keeps the meaning could
still change what a translator emits, and a translator could branch on a name
or a binding order. This is the strongest objection to the design
(`roc-reify-refactor-safety.md`).

The answer is that a translator observes a quotient, not the syntax. Roc
declares a set of meaning-preserving refactors, and the normal form is the same
under each one:

| Refactor | Why the normal form does not change |
| --- | --- |
| rename a local or a parameter | binders are positional |
| reorder independent bindings | node order comes from the graph |
| bind a value once or write it twice | the graph is hash-consed |
| drop a binding nothing reads | dead nodes are removed |
| extract or inline a helper | non-recursive callees are inlined in `inline`; `outline` chooses its own rows |
| `and`, `or` and the `if` they mean | one form |
| `?`, `??`, `return` and the `match` they mean | one form |
| move code, reformat, comment | no regions in the value |
| add or remove an annotation | the solved types are the same |
| method, pipe and operator spellings | one `Prim` |

The full set, with the tiers of guarantee, is section 7 of
`roc-reify-normal-form.md`. Each example ships a `refactored.roc` that must
print the same output.

Some refactors stay outside the set, and they should: `x * 2` to `x + x`,
reassociating a float sum, `len() > 0` to `!is_empty()` outside the `lawful`
view, or a recursion rewritten as a fold. Each changes the operations that run.
Each either changes the output or stops the build at the site, never silently.

Two more facts keep translators honest. A translator cannot read names or
regions, because the description has neither. And the reach across packages is
bounded by explicit choices: the cut, and pinned package versions. The
refactor-safety document proposed a marker for packages that expose their
bodies. The design reads every body outside the cut instead.

## 11. What is refused, and known limits

A function describes when everything it names is fixed by the time checking
ends. Three kinds of thing are never fixed, and they are the only exclusions:

| Excluded | Why |
| --- | --- |
| a function value nothing fixes: a parameter named at the code place, an item of a list | no body stands behind it |
| a type nothing settles: a type variable with no default | the body reads differently at each type |
| a template argument the program computes when it runs | the description is built before the program runs |

Effects are out of scope by design. Captured run-time values are refused
unless the translator binds them. Everything else in pure Roc describes:
recursion, generic functions at the types the program settles, `where`
functions, loops, `?`, early `return`, `var` and `crash`. When Roc gains a
construct, the construct describes if it names fixed things.

Limits that are not part of the rule:

- A lambda parameter has no annotation syntax, so a lambda whose types neither
  the site nor the numeric default fixes needs a named, annotated function.
- A top-level value that computes a function cannot be named as the function
  to describe, because the root needs a lambda whose parameters it can list.
  `|x| doubler(x)` works.
- A custom `from_interpolation` that can leave early with `?`, or that is
  generic in its assembler's item type, is refused.
- The converted value of a literal of the author's own type is not shown. A
  translator sees the conversion call, because the reifier runs before that
  value is computed.
- A primitive used as a value is refused.
- `Named` types carry no `TypeId`.
- A `where` method's argument is not a code place, so an unannotated fragment
  in method form cannot be described.
- A refusal inside a callee is reported at the call in the caller, not at the
  construct inside the callee that stopped the walk.

The checklist lists each unticked box with its reason line.

## 12. Rejected alternatives

Each alternative is in a longer document. In short:

| Alternative | Why not |
| --- | --- |
| Explicit construction, `Code.(f)` | `Code` is opaque so that only the compiler builds one, and the signature already says it (`roc-reify-proposal.md` section 3) |
| Annotating a definition, `is_adult : Code(..)` | a `Code` exists only while the compiler runs; a package ships an ordinary function instead |
| Monads or a free monad | they structure composition, not representation; the builder still holds a function pointer, and Roc has no higher-kinded types |
| Effect rows such as `a -[GPU]-> b` | a row says where a function runs, and a translator needs what it says, as data |
| Tracing, as in JAX | needs a value that is symbolic at run time while it passes for the real type; Roc is static and monomorphic |
| A compiler that knows each domain | not general, and every diagnostic would be in the compiler instead of in the library |
| Reifying effectful functions | the normal form would gain ordering semantics, and the platform boundary would move (`roc-reify-proposal.md` 7.8) |
| A fold, where the translator owns the description | information flows only upward, whole-body analysis needs data again, and the vocabulary is large (`roc-reify-fold-alternative.md`) |
| A second backend, a primitive-cut dataflow graph, code as run-time data, translatability in the type, a variable-free description | each picks one pipeline point for every target; the trade-offs are in `roc-reify-whole-design-alternatives.md` |
| Describing once with an open row in `Ty` | derived `==`, record update and scalarization have no meaning over an unknown row (`roc-reify-structural-proposal.md`) |
| Describing in Monotype per specialization | lowering walks no function, and the checked bodies are not kept there |
| Primitives listed explicitly in the opaque type's module | a package that lists nothing would have no primitives, so every use would be refused (`roc-reify-opaque-proposal.md`) |
| Package-declared laws | a wrong law gives a wrong description with no error, and no reference evaluator checks it |
| Evidence as extra `Prim` arguments | changes the arity of every constrained builtin, and a target would be a primitive used as a value |
| No evidence | a translator would assume the natural order and translate wrongly without an error |
| A run-time handle to a captured opaque value, or `Wrap` of its backing | the first needs an existential type; the second breaks the package's abstraction |
| A builtin encoding format for captures | the translator would decode a format it does not own |
| An `Op.Widen` node, or tag ids by hash | `Widen` means nothing to a translator; a hash collision selects the wrong arm (`roc-reify-tag-names.md`) |
| A `Prim.body : [Roc, Intrinsic]` field | a target binds by id in both cases; the refusal report gets the fact from the compiler |
| A marker for packages that expose their bodies | replaced by the translator's cut and pinned versions |

## 13. Prior art

The closest systems, briefly:

- C# expression trees chose the same trigger in 2007: a lambda at a parameter
  of type `Expression<T>` becomes a tree.
- F# reflected definitions reify whole named functions.
- Julia's GPUCompiler hands a library a typed, monomorphic IR.
- Swift's `#Predicate` macro serves the same database use case by syntax.
- Scala 3, MetaOCaml and Template Haskell offer full multi-stage programming
  with splices, which this design does not have.
- Dhall and Unison normalize and hash code, but not for translation.

What appears to be new is the combination: ordinary, inferred, pure functions,
monomorphized by rule, given to a library as a canonical graph that is
guaranteed identical across a published set of refactors. Roc can offer it
because it has complete type inference, purity in its types, and strict
semantics whose one observable order can be stated as a rule. The comparison is `roc-reify-prior-art-comparison.md`, and a survey
of ideas from less common languages is `roc-reify-prior-art-survey.md`.

## 14. Examples and tests

| Example | What it shows |
| --- | --- |
| `examples/reifying/hello/` | a translator of about 60 lines; both ways to refuse |
| `examples/reifying/glsl/` | a GLSL 330 fragment shader; the `inline` view, `to_tree`, the cut, and a CPU interpreter of the description |
| `examples/reifying/sql/` | SQL for a schema, migrations and queries; the `graph` view, captured values bound with `Code.Binds`, and the glue package `time_sql` |
| `examples/reifying/dbsp/` | incremental views as Roc closures, and a Rust circuit out |
| `examples/reifying/shaders-without-reifying/` | the control experiment: the same shader written as a library DSL |
| `examples/reifying/surreal/` | a pointer to the SurrealDB ORM, which moved to its own repository, `roc-reify-surrealdb`; it uses fragments, intrinsics and `Code.ty_of` |

The tests come in layers: unit tests of the normal form in `src/reify/`, walk
tests in `src/compile/test/code_reifier_test.zig`, staging cases from checker
to translator in `src/eval/test/eval_staging_tests.zig`, CLI fixtures
`test/cli/Staged*.roc` and `test/cli/Intrinsic*.roc`, the fuzzers, and the
examples.

The developer diagnostics `ROC_REIFY_INSTANCES` (each closing use and its
instance table), `ROC_REIFY_ONLY` (runs bits and witnesses) and
`ROC_REIFY_OUTLINE_STATS` are read only by Debug and `-Ddev-diagnostics`
compilers.

## 15. Document map

| Document | Role |
| --- | --- |
| `docs/reifying-overview.md` | a short overview for the community |
| `docs/langref/reifying.md` | the user guide, with every report |
| `roc-reify-design-checklist.md` | the checklist of constructs and features, with the reason line of each refusal |
| `design.md` "Code Reification", "The Runs Bit", "Reify-Only Definitions" | the compiler's rules and invariants |
| `roc-reify-proposal.md` | the original proposal: motivation, syntax options, criticisms, use cases |
| `roc-reify-normal-form.md`, `roc-reify-normalization-plan.md`, `roc-reify-rule-derivation.md` | the normal form, its plan, and the rule tool |
| `roc-reify-opaque-proposal.md` | primitives of opaque types, ids, evidence, captured opaque values |
| `roc-reify-structural-proposal.md` | instance descriptions, record presence and defaults, `Named` arguments, `Code.ty_of` |
| `roc-reify-translator-only-proposal.md` | intrinsics and reify-only definitions |
| `roc-reify-tag-names.md`, `roc-reify-refactor-safety.md` | tags by name, and the refactor objection |
| `roc-reify-fold-alternative.md`, `roc-reify-whole-design-alternatives.md`, `roc-reify-prior-art-*.md` | alternatives and prior art |

The proposals record plans. Several details changed in the implementation,
and this article follows the implementation.
