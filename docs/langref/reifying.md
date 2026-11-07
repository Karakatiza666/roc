# Reifying Functions

A _translator_ is a Roc function that runs while the compiler runs. It reads a description of another Roc function and returns something else: GLSL text, a SQL script, a query plan. The described function stays an ordinary Roc function. You can still call it, test it with `expect`, and step through it.

The description has the type `Code(f)`, where `f` is the type of the function it describes. _Reifying_ a function is making this description of it.

This page is for two readers. If you use a translator, read [How a Function Becomes a Code](#how-a-function-becomes-a-code), [Refusals](#refusals) and [Every Report](#every-report). If you write a translator, read all of it. Start with the [hello example](https://github.com/roc-lang/roc/blob/main/examples/reifying/hello/README.md). It is a translator of about 60 lines.

For a short overview of the feature, with the examples and its limits, read [the overview](../reifying-overview.md).

The rationale and the design alternatives are in [roc-reify-proposal.md](https://github.com/roc-lang/roc/blob/main/roc-reify-proposal.md).

## What a Code Is

A `Code(f)` is a value that holds one function's description. These facts hold for every `Code`:

| Fact | Meaning |
| --- | --- |
| It is typed | `Code(Person -> Bool)` holds only a function of that type. A type error in the function is an ordinary type error at the ordinary place. |
| It is pure | `Code(a => b)` is a type error. An effectful function cannot be reified, because an effect has nowhere to happen while the compiler runs. |
| It is closed | The description has no scope. Everything the function reads from outside is written into the description. |
| It is inert | There is no way to call a `Code`. It is data. |
| It exists only while the compiler runs | You cannot build one by hand, and you cannot annotate a value with `Code`. A `Code` is a parameter of a function, or the return type of a [template](#templates). Only the outermost function of an annotation takes one. A type alias of a `Code`, such as `MyCode : Code(I32 -> I32)`, is a `Code` and follows the same rule. A callback that takes a `Code`, or a record field of a function type that does, is an error, and so is a `Code` behind a type alias used anywhere else. |
| It has equality | Two `Code` values are equal when their descriptions are equal, wherever each came from. `Code.version` says which version of the rules built it. |

```roc
is_adult : Code({ age : U8 } -> Bool)   # ERROR! A Code is not allowed here
is_adult = |p| p.age >= 18
```

Write `is_adult` as an ordinary function and pass it where a `Code` is expected. A package that wants to ship reusable reified functions ships ordinary functions.

## How a Function Becomes a Code

A function is reified when it stands where the type says `Code`. There is no other syntax:

```roc
area : F64, F64 -> F64
area = |w, h| w * h + 1.0

import Calc

# Calc.to_expr : Code(f) -> Try(Str, [Unsupported(Str)])
expr = Calc.to_expr(area)   # area is described, not called
```

The compiler checks `area` against the function type inside `Code(f)`. Then it describes `area` and passes the description to `to_expr`. This is the same idea as [numeric literals](numbers#number-literals) that take their type from the place they stand.

These forms can stand where a `Code` is expected:

| Form | Example |
| --- | --- |
| A top-level function of this module or of an imported module | `Calc.to_expr(area)` |
| A method declared on a type | `Calc.to_expr(Meters.twice)`, with `twice` declared in the body of `Meters` |
| A function bound in a block | A `double` that the block around the call defines. See [`test/cli/StagedCodeLetBound.roc`](https://github.com/roc-lang/roc/blob/main/test/cli/StagedCodeLetBound.roc). |
| A lambda written at the place, when the call around it fixes its types | Every clause in the SQL example |
| A function chosen by an `if` between known functions | `g = if up inc else dbl`. The call becomes a `Switch`. |

These forms are refused. Most of them are a function that is only known when the program runs, so no body stands behind it:

| Form | Report |
| --- | --- |
| A function parameter of the surrounding function, named at the `Code` place itself | `cannot reify this function` |
| A function read from a list | `cannot reify this expression` |
| An [intrinsic](#intrinsics) used as a value, as in `xs.map(Text.is_email)`, or named as the function to describe | `cannot reify this expression` |
| A function that performs an effect | `reified function performs an effect` |
| A lambda that reads a parameter or a `var` of the function around it, with no call that returns a `Code.Bound` in the chain of calls that holds it (see [Captured Values](#captured-values)) | `reified function captures a value` |

A top-level value that computes a function, as in `doubler = make(2.0)`, isn't refused when a described function uses it. The description reads the definition where the name stands, so `doubler(x)` is a call of the lambda inside `make` with `2.0` as its captured value. Naming such a value as the function to describe, as in `Calc.to_expr(doubler)`, is refused. Write `|x| doubler(x)` there instead.

A lambda written at the place takes its parameter types from the call before the compiler checks its body, the same as a lambda you pass to an ordinary function. So when `Link` is a nominal type with a field `id` and a method `id`, and a call takes a `Code({ c : Link } -> Bool)`, the lambda `|o| o.c.id == 1 and o.c.id() == 1` reads the field `id` and calls the method `id`. A method call on a receiver whose type isn't known yet can't give the lambda its types, and the report says to annotate the receiver.

A function parameter that a call fixes is not refused. In `apply_all = |xs, f| xs.map(|x| f(x))`, the call `apply_all(xs, |x| x * 3)` fixes `f`, so the description names that lambda inside the lambda that `List.map` receives. `xs.map(f)` also describes.

Numbers default as they do in a compiled function. `Calc.to_expr(|x| x * 2)` and `Calc.to_expr(|x| x > 0)` describe at `Dec`. An unannotated helper describes at the type that each use gives it: `triple = |x| x * 3` is `Dec` at a free site, and `U8` when a `U8 -> U8` function calls it. This holds for a helper that a lambda written at the site calls, and for a helper that another unannotated helper calls.

An open record row or an open tag row seals the way a compiled function seals it. In `|r| r.id > 0`, `r` is `{ id : Dec }`.

A default has to fit how the number is used. In `|x| x * 2.U8`, `x` would default to `Dec`, but there's no `Dec` multiplication that takes a `U8`, so the lambda is refused rather than described at a type the program never had. Name and annotate it, `double : U8 -> U8`, and it describes at `U8`.

A function whose types are still not fixed is refused as polymorphic, for example `|x| x`. Give the function a type annotation. A lambda parameter has no annotation syntax, so name the function and annotate it:

```roc
double : I64 -> I64
double = |x| x * 2

Calc.to_expr(double)
```

### Query Fragments

A _query fragment_ is a generic function with a `Code` place whose type names the function's own type variables:

```roc
named_only : Db.Q({ name : Str, ..r }) -> Db.Q({ name : Str, ..r })
named_only = |q| q.filter(|x| x.name != "")
```

The lambda has no single type, so the fragment has no description of its own. Instead, each _use_ that fixes `r` describes the lambda at the type it fixes. `named_only(pets)` with `pets : Db.Q(Pet)` describes the lambda at `Pet`, and the translator sees every field of `Pet`. `named_only(owners)` describes it again, at `Owner`.

These are all uses:

| Use | Example |
| --- | --- |
| A call | `named_only(pets)` |
| A method call, or a call of a method by its type's name | `pets.only_named()`, `Db.Q.only_named(pets)` |
| A function value at a fixed type | `as_value : Db.Q(Pet) -> Db.Q(Pet)` and `as_value = named_only` |
| Another name for the fragment | `for_pets = named_only`, then `for_pets(pets)` or `xs.map(for_pets)` |
| A constant that holds the fragment | `ops = { f: named_only }`, or an unannotated `pair = (named_only, adults)` in a package, used at `Pet` in the app |
| A fragment that calls a fragment | `card = \|q\| named_only(q).filter(\|x\| x.id != "")`, used at `Owner` |
| A `for` loop over a type whose `iter` is a fragment | `for line in rows { .. }` |
| A use inside a top-level `expect` | `expect named_only(pets).show() != ""` |

A fragment in another package works the same way, and so does a method of a `::` type. A fragment that no use fixes is never described, and that's not an error.

[`Code.ty_of`](#type-descriptions) and [`Code.type_id`](#identities) in a generic function follow the same rule: a call whose proxy type names the function's type variables is computed at each use.

A refusal inside a fragment can only be found at a use, because that's the first place a description exists. The report points at the source inside the fragment, and then names the use that reached it, also when the fragment is in another package. This is that report, shortened:

```
── ✗ cannot reify this type ───────────────────────────────── pa/Frag.roc:13:27

shifted = |n| Stamp.n_of(Stamp.{ n }) + 1
                         ^^^^^^^^^^^

The reified function reaches it from the site at main.roc:15:15:

Stdout.line!(Frag.recent(pets).show())
             ^^^^^^^^^^^
```

So `roc check` of the package alone doesn't give this report, unless one of the package's own `expect`s uses the fragment. `roc check` of an app that uses it does.

A function that the platform requires can be a fragment. The platform calls it at the type its requirement names, and an open row in that type, as in `show : [A, ..] -> Str`, is closed as the program closes it when it is built. That call is a use of the app, so the app's `roc check` describes the function there. A `where` clause on such an open row can't be closed this way, and is refused with `cannot reify at an open platform requirement`.

Three forms are refused:

| Form | Report |
| --- | --- |
| A fragment whose translator binds captured values (it returns a `Code.Bound`) and whose chain reads a run-time value outside a lambda, as in `pick = \|row, least\| Stage.render(\|x\| x.n > least, row)` | `cannot bind inputs in a generic function` |
| A fragment that a `where` requirement selects, as in `tidy_twice : b -> b where [b.tidy : b -> b]` | `cannot reify through a where requirement` |
| A `to_inspect`, `is_eq`, `to_hash`, `encoder_for` or `parser_for` method that is a fragment, or that uses one at its type's variables | `cannot reify in a method the compiler calls` |

A translator that binds inputs can be in a generic function. When the type of the call that returns the `Code.Bound` names the function's type variables, each use that fixes them runs the chain at its own types and binds the inputs there, so each use has its own slots:

```roc
pick : I64 -> Code.Bound(Rendered({ n : I64, ..r }))
pick = |least| Stage.render(|x| x.n > least)
```

Here `pick(1)` at `Rendered({ n : I64, m : I64 })` and `pick(2)` at `Rendered({ n : I64 })` each get one slot, which holds `least`. A use through a method call, a package's generic function used from the app, and a function the platform requires work the same way. The chain must read a run-time value only in a lambda at a `Code` place: a chain that takes `row` as an argument, as in the first row of the table, has no one value to run with while the compiler runs. A `where` requirement picks its method only when the program is built for one type, after the descriptions exist. Call the method on its type directly instead, as in `Wrap.tidy(w)`.

The compiler calls the methods in the last row itself: `Str.inspect` calls `to_inspect`, and `==`, hashing, encoding and parsing of a record or a list that holds the type call the others. No use in the program fixes their types, so the compiler refuses the place at the method. Put it in a function that the program calls by name.

## The Views

A description is a graph of functions, called _rows_. The translator says which view of the graph it wants with the type of its parameter.

| View | Parameter | Read with | A call of a helper in the same package |
| --- | --- | --- | --- |
| `graph` | `Code(f)` | `code.graph()` | A helper called from one place is inlined there. A helper called from two or more places is a row of its own, and each call is a `Call` node. A helper that holds a `return` inside a loop or inside an arm is a row of its own too. |
| `inline` | `Code.Inlined(f)` | `code.inline()` | Inlined at every call, however many there are. A function that calls itself stays a row. A helper that holds a `return` inside a loop or inside a `match` or `if` arm also stays a row, and each call is a `Call` node. |
| `outline` | `Code.Outlined(f)` | `code.outline()` | As in `inline`. Then each computation of at least four operations that occurs at two or more places becomes one row, and each place is a `Call` node. Where the places differ in a value, the value is an argument of the call, so `step(input.a)` and `step(input.b)` call one row. The compiler chooses these rows, so a refactor of the source does not change them. |
| `lawful` | `Code.Lawful(f)` | `code.graph()` | As in `graph`. The compiler also uses the laws of the builtins: a loop that appends to an empty list is `List.map` or `List.keep_if`, a `List.fold` with a known function is its loop, a `map` of a `map` is one `map`, `iter().map(f).collect()` is `List.map`, and `len() > 0` is `!is_empty()`. Only this view uses these laws. |
| `to_tree` | any | `graph.to_tree(row.id)` | Not a view of the graph. It turns one row into nested expressions. |

For a helper `helper` that `twice = |x| helper(x) + helper(x + 1)` calls two times:

| View | Rows | Nodes in the root row |
| --- | --- | --- |
| `graph` | 2: the root and `helper` | 5 |
| `inline` | 1 | 6 |

A translator for a target with no function form, such as one expression, reads the `inline` view. A translator for a target with functions, such as SQL with common table expressions, reads the `graph` view and keeps each `Call`.

A translator for a target with functions whose output must not change when the author moves code into or out of helpers reads the `outline` view. Its rows are not the author's helpers.

A builtin is a `Prim` whose body isn't read. So is an [intrinsic](#intrinsics), a function or constant of an [opaque type](types#opaque-nominal-types), and so is any function in the translator's _cut_: the functions the translator reads by name.

A function or a top-level constant of an opaque type is one that the module declaring the type defines, and whose type names the type anywhere: `Time.is_before : Time, Time -> Bool`, `Time.from_nanos : I128 -> Time`, `Time.epoch : Time`, or `Cal.parse : Str -> Cal.Time` in a module `Cal` that declares `Cal.Time`. Its body reads the representation the type hides, so the description names it instead: `Time.is_before(t, c)`, `t.is_before(c)` and `t < c` each arrive as a `Prim`, and `Time.epoch` arrives as a `Prim` with no arguments. A function of that module whose type doesn't name the type, such as `Time.days_in_week : U8`, is read by its body like any other.

A translator declares its cut with an item named `code_primitives` on its type. It is a list, and each entry is `Code.prim` of one function or constant:

```roc
Glsl :: {}.{
    code_primitives = [Code.prim(Vec3.scale), Code.prim(Vec3.plus), Code.prim(Sampler.texture)]

    fragment_330 : Code.Inlined(f) -> Try(Fragment, Error)
    # ...
}
```

The item can also be the name of a constant in the same module that holds such a list, which lets several types that take a `Code` share one cut: `code_primitives = Glsl.cut`, with `cut : List(Code.PrimId)` defined once. A constant from another module isn't read this way, so a module that wants its own cut writes the list.

A call of `Glsl.Vec3.scale` then reaches the translator as a `Prim` with the owner `Glsl.Vec3` and the method `scale`, whether it's written `Glsl.Vec3.scale(v, k)` or `v.scale(k)`, and the GLSL example maps it to `*`. A constant in the cut arrives as a `Prim` with no arguments. Every other function the described function calls is read by its body, in this package or in any package it depends on.

A builtin, an intrinsic, or a function or constant of an opaque type, is a `Prim` already, so listing it in `code_primitives` is a compile error ("already a primitive"). The cut is for functions whose bodies a translator could read but chooses not to.

The item has the type `List(Code.PrimId)`, so the older tuple form `(Vec3.scale, Vec3.plus)` is a type error, and its hint says to wrap each entry in `Code.prim`. A generic function with a `where` clause, such as `max_by : List(a), (a -> k) -> Try(a, [Empty]) where [k.is_lt : k, k -> Bool]`, can be in the cut, because `Code.prim` names the definition and does not use it at a type.

The cut belongs to the translator rather than to the library, because the target decides it: a GLSL translator keeps a math library's `lerp` as GLSL's `mix`, while a SQL translator reads its body. The tradeoff is that a dependency's body is part of what a translator reads. If an upgrade changes the operations of a function that a described function calls, the translation can change, or the build can stop at the call. Upgrades are explicit, because packages are pinned by URL and content hash, and the report names the call.

## Reading a Graph

The description is made of plain records and tag unions. All of them are in the `Code` type in `Builtin.roc`, and `roc docs --builtins` lists them.

| Type | What it holds |
| --- | --- |
| `Graph` | `{ root, rows }`. `root_row()` is the function you passed. `row(id)` gives another row. |
| `Row` | One function: `id`, `params` and `result` (as `Ty`), `nodes`, `body`, and `recursive`. |
| `Node` | One operation: `op`, the values it reads in `args`, its type `ty`, and `speculatable`. |
| `Val` | What a node reads: `Param(k)`, `Node(index)`, `Out({ node, k })` for a node with several outputs, or `Arg({ owner, k })` for a parameter of a loop body or a join. |
| `Region`, `End` | A body, a switch arm, or a loop body: its `nodes` and how it ends (`Value`, `Return`, `Break`, `Continue`, `Jump`, `Branch`). |
| `Ty` | The type of a node: `F64`, `Str`, `ListOf(..)`, `Record(..)`, `TagUnion(..)`, `Named(name, args, backing)`, `Opaque(name, id, args)` and more. `name()` spells a type for an error message. A `Named` is written with its module and its type arguments, for example `Builtin.Try(I64, Str)`. Each field of a `Record` says whether it's there (see [Record Fields](#record-fields)). |

A `Named` carries the type arguments of its nominal type, in the order the declaration writes its type variables, and its backing at those arguments. It carries an argument that the backing doesn't hold, too. With `Id(row) := { table : Str, key : Str }` in a module `Store`, an `Id(Customer)` is `Named("Store.Id", [customer], Record(..))`, where `customer` is the `Ty` of `Customer`. So a translator reads the row type from `args`, and a captured `Id(Customer)` holds only its table and its key, whatever fields `Customer` has.

A `Val` names a node by its index in `row.nodes`. A node reads only nodes before it. The order of `nodes` comes from the graph alone, so a rename or a reordered binding in the source does not change it.

### One Graph, Walked

```roc
area : F64, F64 -> F64
area = |w, h| w * h + 1.0
```

The graph has one row, `{ id: 0, params: [F64, F64], result: F64, recursive: False }`. These are its nodes:

| Index | `op` | `args` | `ty` |
| --- | --- | --- | --- |
| 0 | `Prim({ owner: "Num.F64", method: "times", id, evidence: [] })` | `Param(0)`, `Param(1)` | `F64` |
| 1 | `Lit(Frac(1, F64))` | none | `F64` |
| 2 | `Prim({ owner: "Num.F64", method: "plus", id, evidence: [] })` | `Node(0)`, `Node(1)` | `F64` |

The body is `{ nodes: [0, 1, 2], end: Value([Node(2)]) }`. The names `w` and `h` are gone. A parameter is `Param(0)` or `Param(1)`.

`graph.to_tree(0)` gives the same row as nested expressions. This is the tree, shortened:

```roc
Block({
    defs: [],
    end: Value([
        Op({ op: Prim({ owner: "Num.F64", method: "plus", .. }), ty: F64, args: [
            Op({ op: Prim({ owner: "Num.F64", method: "times", .. }), ty: F64, args: [Param(0), Param(1)] }),
            Op({ op: Lit(Frac(1, F64)), ty: F64, args: [] }),
        ] }),
    ]),
})
```

A value that is read one time is written where it is read. A value that is read more than once stays a `def` and is read as `Def(index)`, so shared work stays shared. For `|x| { y = x * x; y + y }`, the tree has the def `{ id: 0, value: Op(times, [Param(0), Param(0)]) }` and ends in `Op(plus, [Def(0), Def(0)])`.

### The Nodes

There are 24 ops. This table groups them by what they stand for.

| Group | Ops | Stand for |
| --- | --- | --- |
| Constants | `Lit` | A literal, with its type. A literal of a type with its own `from_numeral` reaches the conversion as a `Numeral` literal: the `Num.Numeral` the compiler built from the digits you wrote. You read it through `Num.Numeral`'s functions, or convert it with a `from_numeral` such as `Dec.from_numeral`. |
| Builtin calls | `Prim` | A builtin, an intrinsic, a function of an opaque type, or a function in the translator's `code_primitives`. `id` identifies it exactly; `Code.prim(f)` gives the same id for `f`. `owner` and `method` are apart, as in `Num.F32` and `sin`, or `Time` and `is_before`, and are for messages: two packages can each have a `Time.is_before`. `evidence` says which method answers each `where` requirement of the function at this call (see [Evidence](#evidence)). Read the type from the node. |
| Function calls | `Call`, `Closure`, `Lambda` | A call of another row, a function value, and a function value written where it is built (`inline` view). |
| Building data | `Record`, `Tuple`, `List`, `Tag`, `Wrap` | `Wrap` puts a value in a nominal type, by name. |
| Reading data | `Field`, `Index`, `Payload`, `Item`, `OptField`, `Unwrap` | A record field, a tuple index, a tag payload, a list item, an optional field, the backing of a nominal. |
| Choosing | `Switch`, `And`, `Or` | `if`, `match`, `?`, `??`, `and`, `or`. |
| Looping | `ForRange`, `ForList`, `Loop` | `for`, `while` and tail recursion. State is in numbered slots. |
| Other | `Crash`, `Derived` | `crash`, and a compiler-derived method such as `parser_for`. A translator that owns the target format expands `Derived`. Every other translator refuses it by name. |

### Evidence

A `Prim` of a function with a `where` clause, such as `List.sort` or `Dict.get`, holds one `Code.Evidence` in `evidence` for each requirement, in the order the clause lists them. An alias such as `item.Sort` counts as the methods it stands for. Each entry has the required `method`, the type `ty` it is called on here, and a `target`:

| `target` | Means |
| --- | --- |
| `Prim(..)` | A builtin, an intrinsic, a function of an opaque type, or a function in the cut, with its own `evidence`. |
| `Row(id)` | A method with a body, such as an order a type writes. Row `id` of the graph is the body. |
| `Derived(method)` | A method the compiler writes for the type. |
| `Unreachable` | No value of `ty` can reach the call. |

`xs.sort()` with `xs : List(I64)` has the `evidence` `[{ method: "order_relative_to", ty: I64, target: Prim({ owner: "Num.I64", method: "order_relative_to", .. }) }]`. With a type that writes its own `order_relative_to`, the target is a `Row`. Before you translate `List.sort` to the sort of your target, make sure that the order is one your target has. A `==` that the compiler derives for a record that holds a `List` also has evidence: `{ m: xs } == { m: ys }` with `xs : List(U16)` gives `List.is_eq` with the target `Prim(Num.U16.is_eq)` for `is_eq @ U16`. A call whose evidence the compiler leaves to a later stage is refused.

### Record Fields

Each field of a `Record` type has a `name`, a `ty` and a `presence`, which says whether a value of the type has the field:

| `presence` | Field | Means |
| --- | --- | --- |
| `Required` | `id : Str` | Every value has it. |
| `Optional` | `note ?: Str` | A value may not have it. A translator that writes a struct needs a form for a missing field, or refuses the type by name. A [captured value](#captured-values) that doesn't have it holds `Absent` for it. |
| `Default(value)` | `stock : I32 ?? 0` | Every value has it, because the default fills it in. `value` is the default, as a [`Code.Value`](#captured-values). |
| `DefaultComputed` | `label : Str ?? made({})` | Every value has it, but the type doesn't carry the default. |

A record whose other fields come from a [nominal record](records#what-can-extend-a-record) arrives with every field. With `Labeled(r) := { label : Str, ..r }` and `Point := { x : F64, y : F64 }`, a `Labeled(Point)` is `Named("Labeled", [Named("Point", [], ..)], Record(..))` with the fields `label`, `x` and `y`.

A default is `Default(value)` when it's a literal, or a list, record, tuple, tag or nominal of literals, or the name of a constant that holds one. Anything else is `DefaultComputed`: a call, a constant of an [opaque type](types#opaque-nominal-types), or a record that leaves out an optional field or a field whose own default is computed. This type comes from a package's module:

```roc
base_stock : I32
base_stock = 7

made : {} -> Str
made = |_| "made"

Med := { id : Str, stock : I32 ?? 0, tags : List(Str) ?? [], kind : Med.Kind ?? Tablet, again : I32 ?? base_stock, label : Str ?? made({}), note ?: Str }.{
    Kind := [Tablet, Syrup]
}
```

A translator that reads `Med` gets these fields:

| Field | `presence` |
| --- | --- |
| `again` | `Default(Int(7))` |
| `id` | `Required` |
| `kind` | `Default(Wrap(Tag("Tablet", [])))` |
| `label` | `DefaultComputed` |
| `note` | `Optional` |
| `stock` | `Default(Int(0))` |
| `tags` | `Default(List([]))` |

The default is part of the type, so two nominal types that differ only in a default are two different `Ty` values. A translator for a schema can write `Default(value)` as the column's default, and refuse `DefaultComputed` with advice.

A record literal in the described function can leave out a field with a default, as it can anywhere in Roc. The description fills in the field with the default's literal, so the translator sees the same value the program builds when it runs:

```roc
Kind := [Tablet, Syrup]
Inner := { a : I64, b : Str ?? "b" }
Med := { id : Str, stock : I32 ?? 0, tags : List(Str) ?? ["x"], kind : Kind ?? Tablet, inner : Inner ?? { a: 1 }, ratio : F32 ?? 0.5 }

make_med : Str -> Med
make_med = |s| { id: s }   # described as { id: s, stock: 0, tags: ["x"], kind: Tablet, inner: { a: 1, b: "b" }, ratio: 0.5 }
```

A field whose default is `DefaultComputed` can't be filled in this way, so leaving it out gives `cannot reify this expression`. Write the field in the literal instead:

```roc
Labelled := { id : Str, label : Str ?? Str.concat("a", "b") }

size : Code(Str -> Labelled) -> U64
size = |code| code.graph().root_row().nodes.len()

size(|s| { id: s })               # ERROR! label's default is computed
size(|s| { id: s, label: "c" })   # This is fine.
```

## What Arrives

The description is a normal form. Two ways to write one computation arrive as one graph. This is useful, and it also means that some forms are not the ones you wrote. These rows come from running the compiler on each expression, with `x : I64`:

| You write | The translator receives | What to do |
| --- | --- | --- |
| `"Hello, ${name}!"` | One `Prim` `Str.concat` with 3 args: `Str.concat('Hello, ', p0, '!')` | Read `concat` as n-ary. Interpolation and nested `concat` calls are one node. |
| `x >= 10` | `Num.I64.is_lte(10, p0)` | There is no `is_gte`. `is_gt` and `is_gte` become `is_lt` and `is_lte` with the operands swapped. |
| `x > 10` | `Num.I64.is_lt(10, p0)` | The same rule. |
| `a > b` | `Num.I64.is_lt(p1, p0)` | The same rule. |
| `if x >= 10 "big" else "small"` | A `Switch` on `Num.I64.is_lt(p0, 10)`. The `False` arm is `'big'`. | Over integers, a `Switch` never tests `is_lte`. The test is `is_lt` with the two arms swapped. Over floats the test stays `is_lte`. |
| `!(a <= b)` | `Num.I64.is_lt(p1, p0)` | The same rule, over integers. |
| `a != b` | `Bool.not(Str.is_eq(p0, p1))` | `!=` is `Bool.not` of `is_eq`. |
| `1 + x` | `Num.I64.plus(p0, 1)` | In an integer `plus` or `times`, or an `is_eq` over integers or `Str`, a literal comes last and two parameters are in parameter order. `x == 10` and `10 == x` are one node. |
| `a and b` | An `And` node. The first operand is in `args`. Each other operand is a region. | `And` is not a `Prim`. |
| `a == b` with `a, b : { city : Str, zip ?: Str }` | `And` of `Str.is_eq` over the `city` fields and a `Switch` on `OptField("zip")` of `a`. Each arm is a `Switch` on `OptField("zip")` of `b`. Two `Ok` arms compare the values, two `Err` arms are `True`, and the other arms are `False`. | Two records that don't have the field are equal there, as they are when the program runs. The SQL translator writes each `Switch` as a test of `IS NOT NULL`. When `b` is a captured value, it is one input slot, and its `city` is `Field(Input(k), "city")`. |
| `t?`, `t ?? 0`, `match t { Ok(v) => .. }` | `Unwrap` of the `Try`, then a `Switch` with the arms `Err` and `Ok`. A payload is read with `Payload("Ok", 0)`. | A `Try` is a nominal type, so it has `Unwrap`. |
| `Ok(v + 1)` | A `Tag("Ok")` inside a `Wrap("Builtin.Try")` | `Wrap` names the nominal. |
| `1.0` as an `F64` | `Lit(Frac(1, F64))` | `to_str` prints `1`. Add the `.0` yourself if the target needs it. |

Each row is a rule of the normal form, so it holds for every `Code` of one `Code.version`. A new version can add, change or remove a rule, so a translator matches the forms it knows and refuses the rest by name. The docs of `Code.Op` in `Builtin.roc` list the same rows. The args of a `Prim` are in the parameter order of the builtin, except for a chain of `Str.concat`, `List.concat`, `plus_wrap`, `times_wrap`, `bitwise_and`, `bitwise_or` or `bitwise_xor`, which is one `Prim` with every operand. The full list of rules is in [roc-reify-normal-form.md](https://github.com/roc-lang/roc/blob/main/roc-reify-normal-form.md).

## Identities

A name is for messages. To know exactly which function or type a node names, compare its id:

| Call | Gives | Equals |
| --- | --- | --- |
| `Code.prim(Time.is_before)` | a `Code.PrimId` | the `id` of each `Prim` node that calls `Time.is_before` |
| `Code.type_id(time_proxy)` | a `Code.TypeId` | the id in each `Opaque("Time", id, [])` type |

The argument of `Code.prim` is the name of a top-level or imported function or constant, such as `Code.prim(Time.is_before)` or `Code.prim(Str.concat)`. A local value, a parameter or a computed function has no identity, so `Code.prim` of one gives `not a definition`. So does a method that a type outside the builtins derives with `is_eq : _`, such as `Code.prim(Point.is_eq)`: a call of it compares the backing, and no `Prim` names it.

`Code.prim` doesn't call or use its argument, so a `where` clause of the function asks nothing at that place. Its result is a constant that the compiler computes. `Code.prim`, `Code.type_id` and `Code.ty_of` are only ever called: passing one as a value, as in `proxies.map(Code.ty_of)`, gives `call this function`.

`Code.type_id` takes a `Code.Proxy(t)`, a value that stands for the type `t`. Roc has no type arguments, so you make a proxy with `Code.proxy()` and an annotation that names the type:

```roc
time_proxy : Code.Proxy(Time)
time_proxy = Code.proxy()

is_time : Code.Ty -> Bool
is_time = |ty| match ty {
    Opaque(_, id, _) => id == Code.type_id(time_proxy)
    _ => Bool.False
}
```

Only a nominal type has an identity, so `Code.type_id` of a proxy whose type is a record, a tag union, a function type or a type variable gives `not a nominal type`. A builtin opaque type is named as the owner of its functions, such as `Dict` and `Box`.

### Type Descriptions

`Code.ty_of` takes a proxy too, and gives the `Code.Ty` of its type: the same `Ty` that the `result` of `|x| x` at that type has. It works for any type that a description has a form for, such as `Code.ty_of(owner_proxy)` with `owner_proxy : Code.Proxy(Owner)`, a record or `List(Owner)`. A translator that only needs a type, such as one that writes a table's schema, needs no lambda to get it.

### Proxies in Generic Functions

A proxy can name a type variable of the function around it. Then `Code.type_id` and `Code.ty_of` are computed at each use of the function, at the type that use fixes, just as a [query fragment](#query-fragments) is described at each use:

```roc
Tbl(row) := { name : Str, ty : Code.Ty, id : Code.TypeId }.{
    table : Str -> Tbl(row)
    table = |name| {
        proxy : Code.Proxy(row)
        proxy = Code.proxy()
        Tbl.({ name, ty: Code.ty_of(proxy), id: Code.type_id(proxy) })
    }
}

owners : Tbl(Owner)
owners = Tbl.table("owner")   # ty and id are those of Owner
```

The type has to be fixed by the time the compiler computes the call. A `Code.ty_of` call, or a use of the function around it, that leaves a type variable open gives `type not fixed`. A `Code.type_id` call or use that leaves the proxy open, or fixes it to a type without an identity, gives `not a nominal type`. For a use, the report points at the call inside the function and names the use that reached it. In a method the compiler calls itself, such as `to_inspect`, no use fixes the types, so it gives `cannot reify in a method the compiler calls`.

## Extending a Translator

A translator knows the builtins, but it can't know the types of every package. A _glue package_ is a package that tells a translator what the functions and types of another package are in its target. It has to exist apart from both: a package can't add methods to a type of another package, and it can't change the translator's source.

The translator takes the extensions as ordinary values, keyed by id. This is the glue package between a `time` package with an opaque `Time` and the SQL example's translator:

```roc
import sql.Sql
import time.Time

TimeSql :: {}.{
    time_proxy : Code.Proxy(Time)
    time_proxy = Code.proxy()

    extension : Sql.Extension
    extension = Sql.extension({
        prims: [
            { prim: Code.prim(Time.is_lt), render: TimeSql.binary("<") },
            { prim: Code.prim(Time.is_gt), render: TimeSql.binary(">") },
            { prim: Code.prim(Time.is_eq), render: TimeSql.binary("=") },
        ],
        types: [{ type: Code.type_id(TimeSql.time_proxy), column: "BLOB" }],
    })

    binary : Str -> ({ args : List(Str), evidence : List(Code.Evidence) } -> Try(Str, Str))
    binary = |op| |call| match call.args {
        [a, b] => Ok("(${a} ${op} ${b})")
        _ => Err("`${op}` takes two operands")
    }
}
```

The app passes it where it calls the translator, as in `Sql.select_where(events, [TimeSql.extension], |e| e.at < cutoff)`. The translator looks up the `id` of each `Prim` node in its extensions, and the id of each `Opaque` type in a column. It refuses a `Prim` that no extension covers, by name, with `Code.refuse_at` or an `Err`.

The extension type belongs to the translator, so the language doesn't define one. What the language gives is the ids, which is why a translator keys its table by `id` and never by `owner` and `method`. A name can repeat: two packages can each have a `Time.is_lt`, and a module can declare its own `Bool` with its own `not`. Ids can't repeat, so a translator that compares ids never takes one for the other. The SQL example keeps its own builtins in an extension too, keyed by `Code.prim(Bool.not)` and the rest, so one lookup by `id` serves both.

An id comes from the module that declares the function or type, contents included, so an edit to `Time`'s module gives it new ids. The glue package and the app are compiled in the same build, so `Code.prim` and the `Prim` nodes always agree. An id isn't meant to be stored across builds.

The tradeoff is that the translator can't check what a glue package claims. `TimeSql` says that `<` on a `BLOB` column computes what `Time.is_lt` computes. That holds because the translator's format writes a `Time` as bytes that sort as its nanoseconds do, and if it didn't hold, the SQL would quietly compute something else.

## Refusals

A translator can refuse a function it has no form for. There are two ways.

| | Return an `Err` | `Code.refuse_at` |
| --- | --- | --- |
| Written as | `Err(Unsupported(reason))` | `code.refuse_at({ row: row.id, node: index }, reason)` |
| What the user sees | Whatever the caller does with the `Err` | A `translation refused` report. It is at every source line the node came from, with the calls that reached it. Each call shows its place as `path:line:col`, and a call in another module names the file of that module. |
| Source line | None. The description has no source regions. | Yes. The compiler keeps a table from each node to its source, and `refuse_at` is the one reader. |
| Test with `expect` | Yes | No. The compile stops. |
| When the translator runs at program run time | The same | Crashes with the message. There is no report. |

`refuse_at` takes the index of a node of `row.nodes`. A translator that wants this must walk `row.nodes` and `Val`, and not only a `Tree`, so that it keeps the index. The hello example does this. It has both ways: `to_expr` returns an `Err`, and `to_expr_or_stop` calls `refuse_at`. The report for `root = |x| x.sqrt() + 1.0` is:

```
── ✗ translation refused ────────────────────────────────────── refused.roc:6:12

A translator refused code that this expression built.

root = |x| x.sqrt() + 1.0
           ^^^^^^^^

The translator gave this reason:

    `sqrt` has no operator here
```

`Code.Inlined` has its own `refuse_at` for nodes of the `inline` view, `Code.Outlined` has one for nodes of the `outline` view, and `Code.Lawful` has one for nodes of the `lawful` view.

Use an `Err` when you want a test, or when the caller can recover. Use `refuse_at` when the user must fix the source.

## What Is Refused and Why

A function describes when everything it names is fixed by the time checking ends. Only three kinds of thing are never fixed. They are the only exclusions:

| Excluded | Why | Report |
| --- | --- | --- |
| A function value that nothing fixes: a parameter, or an item of a list | There is no body to read. | `cannot reify this function`, `cannot reify this expression` |
| A type that nothing settles: a type variable with no default | The body reads differently at each type, so there is no one body. | `cannot reify a polymorphic function` |
| A `Code` that is not fixed at build time: a template argument computed when the program runs | A description is built before the program runs. | `template needs a constant` |

Effects are refused for the same reason, and so are captured run-time values, unless the translator binds them (see [Captured Values](#captured-values)). A function can read a top-level value, a value the block around the site binds, and any named function. Each is written into the description. Everything else in pure Roc describes: recursion, generic functions at the types the program settles, `where` functions, loops, `?`, early `return`, `var`, and `crash`.

A function that is refused gives one report. The place where it stands then holds a compile error, so no later step reports it again.

This is a rule and not a list of supported syntax. If you know the rule, you can predict every refusal. When Roc gains a construct, the construct describes if it names fixed things.

> Note that the compiler reifies, and the translator validates. The compiler never asks whether a target can run `Str.split_on`. A GPU translator answers that in its own Roc, with one of the refusals above.

Some limits exist today and are not part of the rule:

| Limit | Effect |
| --- | --- |
| A lambda parameter has no annotation syntax | A lambda whose types neither the site nor the numeric default fixes needs a named, annotated function. `\|x\| x * 2` describes at `Dec`. For `U8`, write `double : U8 -> U8`. |
| A tag union whose row has no default to seal it | Refused by name. |
| An [opaque type](types#opaque-nominal-types) from a `::` declaration | A call of one of the type's functions, written `Time.is_before(t, c)`, `t.is_before(c)` or `t < c`, arrives as a `Prim` named by the type and the function, and so does a constant of the type, such as `Time.epoch` or a top-level `cutoff = Time.from_nanos(5)`. A value you read from a parameter or a field arrives with the type's name and no fields. A captured value of the type is refused unless the translator names a format with `Code.Binds` (see [Captured Values](#captured-values)). A function of the type used as a value (`xs.map(Time.to_nanos)`) is refused. Two types with the same name from different packages arrive with the same name and two different type ids. |

## Captured Values

A lambda can read a value from around itself that only exists when the program runs, such as `cutoff` here:

```roc
before = |cutoff| Sql.select_where(events, [TimeSql.extension], |e| e.at < cutoff)
```

Here `[TimeSql.extension]` is an [extension](#extending-a-translator) that says what `<` on a `Time` is in SQL.

A translator that returns a `Code.Bound(result)` accepts such a lambda. The translator still runs once, while the compiler runs, and emits a placeholder for each value it can't know yet, such as a `?` in SQL. In the description, each such value is an `Input(k)` node, called an _input slot_. Each call of `before` then gives the program a `Code.Bound` whose `inputs()` holds one `Code.Value` per slot, in slot order. The translator writes `Code.bound(code, result)`, and the program adds the inputs.

The call that takes the lambda doesn't have to return the `Code.Bound` itself. A builder can keep its own type and pass the lambda on, and the first call of the chain that returns a `Code.Bound` receives it:

```roc
cheaper_than = |limit| Query.from(meds).filter(|m| m.price < limit).ready()
```

Here `filter` returns a `Query`, and `ready` returns a `Code.Bound`. The whole chain, up to `ready`, runs once while the compiler runs, and each call of `cheaper_than` gives its own inputs. Because the chain runs in `roc check`, a translator's refusal in any call of it is a compile error at the node it refused, also when the chain is in a branch. So is a crash in a translator of the chain. A call passes the lambda on when it takes it, or a call that passed it on, as an argument or as the receiver. A name stops the chain (`q = base.filter(..)` and then `q.ready()`), and so do an `if`, a `match`, a record, a tuple, a list and a tag. The report of a lambda whose chain stops says which of these stopped it. To branch, write the whole chain, up to the call that returns the `Code.Bound`, in each branch. One chain can hold many lambdas that capture values. Their slots come one lambda after another, in the order the lambdas are written, and each lambda's own slots are in slot order. A name that two lambdas read is two slots. `code.first_slot()` tells a builder where its lambda's slots start, so a translator can number its placeholders across the whole chain. Two descriptions that differ only in `first_slot` are still equal.

A call at the end of the chain often has no lambda of its own, so it has no `Code` to call `Code.bound` on. It writes `Code.Bound.of(result)` instead:

```roc
ready : Query(row) -> Code.Bound(Try(Prepared(row), Error))
ready = |query| Code.Bound.of(query.prepare())
```

The two give the same value. What makes a call receive the inputs is the `Code.Bound` type it returns, not the function that builds the value. If the program builds a `Code.Bound` while it runs, outside such a chain, its `inputs()` is empty.

The result can hold a function that the translator makes, such as a `read` function that decodes rows of the statement it emitted. The function can use the values the translator computed. It can't use a value that only exists when the program runs: an argument of the call that the program computes at run time stops the call from running while the compiler runs, so the compiler refuses to bind the lambda. The same is true for an argument of each call in the chain, such as `n` in `.limit(n)`. Read such a value in a lambda at a `Code` place instead, as in `.limit(|_| n)`, and it is an input slot. Because the result holds a function, the compiler doesn't reuse it after you edit the module, and runs the chain again.

A slot is a value the description reads whole. A lambda that reads only fields of a captured record, as `|o| o.quantity >= limits.min and o.quantity <= limits.max` does, gets one slot per field it reads, here `limits.min` and `limits.max`. A lambda that reads the record whole also gets one slot for it, and reads its fields as `Field` of that slot's `Input`. `|c| c.address == place`, with `zip ?: Str` in the address, reads `place` whole, because the `Switch` on its optional field reads the whole record. It gets one slot, and the `city` comparison reads `Field(Input(0), "city")`. A list and a tag union are always read whole. A translator that binds a record input field by field, as the SQL translator does, writes a placeholder for each field. One that binds the record as one value, as the SurrealDB translator does, writes `$_1.city`.

A `Code.Value` follows the slot's type: an integer is an `Int`, a `Str` is a `Str`, a record is a `Record` of its fields' values, and a nominal value is a `Wrap` of its backing's value.

An [optional field](records#optional-fields) is the one place where the type doesn't say what a value holds. Its value in the `Record` is the field's own value when the record has the field, and `Absent` when it doesn't:

```roc
Customer : { id : I64, name : Str, country : Str, email ?: Str }

insert_customer : Customer -> Try(Sql.Statement, Sql.Error)
insert_customer = |c| Sql.bind_captured(customers.insert_one(|{}| c))
```

The slot is the whole row `c`. The translator writes the same statement for every customer, `INSERT INTO customers (country, email, id, name) VALUES (?1, ?2, ?3, ?4)`. A customer with an email gives `Record([Str("GB"), Str("ada@example.com"), Int(1), Str("Ada")])`, and one without gives `Absent` in the place of the email, which the SQL translator binds as `NULL`. Each call gives its own answer, because only the program knows which records have the field. The `Code.Ty` of the slot says which fields are `Optional`, so a translator knows where an `Absent` can be before the program runs.

That doesn't work for a value of an [opaque type](types#opaque-nominal-types), because its fields belong to the package that declares it. A translator that wants such values names a _format_ with `Code.Binds`:

```roc
select_where : Table(row), List(Extension), Code.Binds(Code(row -> Bool), Param) -> Code.Bound(Try(Str, Error))
```

`Code.Binds(code, fmt)` is the `Code` it wraps, so any view goes inside it, as in `Code.Binds(Code.Lawful(f), fmt)`. A `Code` written without `Binds` still receives captured values of every other type, but refuses one of an opaque type.

At a `Code.Binds` place, every captured value the lambda reads, written as a name or a field path of one (`cutoff`, `order.at`, `pair.0`), needs an encoder in the format:

```roc
encoder_for : fmt -> (t, List(U8) -> Try(List(U8), []))
```

A captured function is the one exception: it needs no encoder, because the compiler describes it as code, as at a `Code(f)` place. A record that holds a function is a value, so it needs an encoder, and no format has one for the function. The format also needs `default : () -> fmt`, because the program builds the format value itself. A slot whose type holds an opaque type arrives as `Encoded(bytes)`: the bytes that the type's `encoder_for` wrote, in the translator's own format. A slot of any other type arrives as the `Code.Value` of its type, as above.

| Captured value | At `Code(f)` | At `Code.Binds(Code(f), fmt)` |
| --- | --- | --- |
| `n : I64`, read as `n` | `Int(n)` | `Int(n)`, and `I64` must have an encoder in `fmt` |
| `cutoff : Time` (opaque), read as `cutoff` | refused | `Encoded(bytes)` |
| `order : { at : Time, id : I64 }`, read as `order.at` | refused | `Encoded(bytes)` for `order.at` |
| the same, read whole (`o == order`) and as `order.at` | refused | one `Encoded(bytes)` for `order`, and `order.at` is `Field` of its `Input` |
| the same, read as `{ at, .. } = order` and then `at` | refused | refused: read it as `order.at` |
| `earlier : Time, Time -> Bool`, read as `earlier` | described as code | described as code, and it needs no encoder |

The encoder is the type's own `encoder_for`, the same method a JSON encoder uses. A builtin type and a record or tag union of encodable types already have one. A [nominal type](types#nominal-types) gets one with `encoder_for : _`, or with one you write from the format's methods. A value whose type the format can't encode is a compile error at the place the lambda reads it, also when a generic function captures it and a call fixes its type. The error names the type and the format:

```
── ✗ cannot bind captured value ─────────────────────────────── typing.roc:47:47

This translator cannot bind a captured value of type F32: its format, Fmt,
cannot encode it.

float = |limit| Stage.render(|x| x.to_f32() < limit).value()
                                              ^^^^^

Encoding this value needs the method encode_f32 of Fmt, which it does not have.
```

That's by design: a translator package gives its format a method for each kind of value its target accepts, and leaves out the rest. A format with no `encode_f32` costs nothing until a lambda captures a float. The error type is `[]` because the program has no place to report a failed encoding at the call, so a format whose encoder can fail is a type error too.

Why bytes, and not the value itself? A `Code.Value` has to be one type for every translator, and the program can't hand over a value whose type the translator can't name. Bytes in a format the translator owns, such as its own bind encoding, are something it already knows how to read.

## Templates

A function that returns a `Code` is a _template_. The compiler calls it while it runs, and does not compile it. Each argument of a call must be fixed at that time: a literal, a name bound to one, an aggregate of those, or a function. The compiler writes each argument into the description that the call makes.

```roc
add_k : I64 -> Code(I64 -> I64)
add_k = |k| |x| x + k

Calc.to_expr(add_k(5))   # Ok("(p0 + 5)")
Calc.to_expr(add_k(7))   # Ok("(p0 + 7)")
```

A function that only passes a `Code` on is not a template. If `pick : Bool, a, a -> a` returns one of two `Code` values it receives, a call of `pick` is an ordinary call.

One template gives as many descriptions as it has calls. The `5` is a literal in the description by the time the translator reads it.

An argument that is only known when the program runs gives `template needs a constant`:

```roc
runtime = |n| Calc.to_expr(add_k(n))   # ERROR! n is computed when the program runs
```

## Intrinsics

An _intrinsic_ is a declaration with a type and no body, outside a platform:

```roc
Text :: {}.{
	is_email : Str -> Bool
}
```

An intrinsic checks and dispatches like any function. You can call it, write it as a method, and give it a `where` clause. The difference is that nothing says what it does. Only a translator gives it a meaning.

### What a Translator Sees

At every `Code` place, an intrinsic is a `Prim`. A translator binds it by `id`, the same as it binds a builtin. The extension table of [Extending a Translator](#extending-a-translator) takes one more line:

```roc
{ prim: Code.prim(Text.is_email), render: TextSql.call("is_email") },
```

`TextSql.call` is an illustration, as `TimeSql.binary` is. Like `binary`, it returns a function from `{ args, evidence }` to a `Try(Str, Str)`, which is the `render` type of the extension.

An intrinsic needs no entry in `code_primitives`. Listing one there gives `already a primitive`. A translator can't tell an intrinsic's `Prim` from a builtin's. Its `owner` and `method` are for messages, and its `evidence` works as it does for any `Prim`.

### Where an Intrinsic Can Be Used

An intrinsic can be used inside a function that a translator describes:

- a lambda written at a `Code` place;
- a [template](#templates);
- a function passed as a `Code`.

A function that calls an intrinsic can be described too. This is fine:

```roc
Calc := {}.{
	count : Code(Str -> Bool) -> U64
	count = |code| code.graph().rows().len()
}

valid = |s| Text.is_email(s)

described = Calc.count(|s| valid(s))   # fine: the translator reads valid
```

In a description, an intrinsic must be called. It can't be used as a value. At a `Code` place, `|xs| xs.map(Text.is_email)` gives `cannot reify this expression`. So does `Calc.count(Text.is_email)`, where the intrinsic is the function to describe. An intrinsic has no body to read. Write `|s| Text.is_email(s)` instead.

A description inlines `valid`. The graph of `|s| valid(s)` has one row, and its only node is `Text.is_email(p0)`.

### Code That Exists Only in Reified Code

A function whose run-time code reaches an intrinsic _exists only in reified code_. That includes a function that calls such a function, and so on. Such a function is fine as long as no code that runs reaches it. If the program runs it, nothing can say what the intrinsic computes. By design, the compiler finds this at compile time and not at run time, so you see a report instead of a crash.

The report is given where code that runs makes the reference. There are three kinds of such place:

- an entry point: a `main!` or other function that the app provides or the platform requires;
- a top-level constant, which the compiler evaluates while it runs;
- an `expect`.

Each function in between is on the chain that the report prints. In an entry point:

```roc
main! = |_args| {
	echo!(Str.inspect(valid("a@b.c")))   # ERROR! valid reaches Text.is_email
	Ok({})
}
```

The report is:

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

A top-level constant that reaches an intrinsic is the same error, because the compiler evaluates the constant and a translator isn't involved:

```roc
verdict = valid("a@b.c")   # ERROR! this runs while the compiler runs
```

An `expect` runs too, so this is the same error:

```roc
expect valid("a@b.c")   # ERROR! an expect runs
```

`roc test` does not run an `expect` with this error. It counts the `expect` under `compiler errors`, and exits with code 1. An `expect` that only describes code runs normally, as in `expect Calc.count(|s| valid(s)) == 1`.

Like other compile errors in Roc, this one doesn't stop a dev run. `roc check` prints the report and exits with code 1. `roc file.roc` prints the report and then runs the program:

- If the program doesn't reach the place, it runs normally. The exit code is still 1, because of the error.
- If the program reaches the place, it stops with `Roc application crashed with this message: runtime error`. The exit code is 1.

`roc build` prints the report, writes the binary, and exits with code 1. The binary behaves as a dev run does. It exits with code 0 if it doesn't reach the place, and with code 1 if it does.

A use as a value gives the same report with a different first line. In `args.map(Text.is_email)` at an entry point, the report says that `Text.is_email` is used here as a value, but it reaches an intrinsic.

### Generic Functions

A generic function reaches an intrinsic only where a use fixes its type to one whose method is an intrinsic. The chain says which method it dispatched on, and on which type:

```roc
Clock := { n : U64 }.{
	now : Clock -> Bool
}

inner = |x| x.now()

outer = |t| inner(t)
```

Inside a lambda at a `Code` place, `outer(t)` is described. At run time, `outer(clock)` with `clock : Clock` is an error, and the chain reads `outer calls now on a Clock`. A call of `outer` at a type whose `now` has a body is fine, because it never reaches an intrinsic.

### A Known Limit

A top-level constant that holds a function is an error when evaluating its definition reaches an intrinsic, even if evaluating it calls nothing:

```roc
make = |k| |x| Text.is_close(x, k)

doubler = make(2.0)   # ERROR! make reaches Text.is_close
```

Evaluating `make(2.0)` only builds a closure. It doesn't call `Text.is_close`. The compiler still treats `make` as code that exists only in reified code, and it doesn't check whether the call inside runs. To avoid the error, call `make` where you use it, at the `Code` place. Here `Calc.count` takes a `Code(F64 -> Bool)`:

```roc
Calc.count(|x| make(2.0)(x))   # fine
```

The description is the same as for `|x| Text.is_close(x, 2.0)`. It has one row, and its only node is `Text.is_close(p0, 2)`.

### Listing Intrinsics

`roc check --intrinsics` checks as `roc check` does, and then prints one line for each intrinsic in the modules it checked, including modules of imported packages. The exit code is the same as for `roc check`. Each line has the file, the line and column of the declaration, the module and name, and the type as you wrote it:

```
pa/Text.roc:3:2 Text.is_email : Str -> Bool
```

The lines are sorted by file and then by line. A hosted declaration of a platform isn't an intrinsic, so it isn't listed.

`roc docs` puts the badge `intrinsic: no Roc body` next to the signature of each intrinsic. The editor shows the same badge when you hover over an intrinsic, or over a use of one.

### Giving an Intrinsic a Body Later

You can add a body to an intrinsic at any time. The change is local: the declaration gains a body, and nothing else changes. Its `id` stays the same, so a translator's table still finds it. Callers outside a `Code` place start to work, and reports about it go away.

## Every Report

These are all the reports that reifying gives. Each one is a compile error at the place it names. Like other compile errors in Roc, the program still runs, and crashes if it reaches that place.

| Report | Given for |
| --- | --- |
| `cannot reify this expression` | An expression a description has no form for, such as a function read from a list, an [intrinsic](#intrinsics) used as a value in a description, or a record literal that leaves out a field whose default is computed. The report names the form. |
| `cannot reify this type` | A type a description has no form for, such as a value of an opaque type built from its fields. The report names the type. |
| `cannot reify a polymorphic function` | A function whose types the place doesn't fix. |
| `cannot reify this function` | A function with no body behind its name, such as a parameter of the surrounding function named at the `Code` place. |
| `cannot reach this definition` | A name whose body the compiler can't read where it stands. |
| `reified function captures a value` | A lambda that reads a run-time value, with no call that returns a `Code.Bound` in the chain of calls that holds it. The report says what stopped the chain: an `if` or a `match`, a name, a record, a tuple, a list or a tag, or the end of the chain. |
| `cannot bind this captured value` | A captured value that a translator returning a `Code.Bound` still can't receive: one of an opaque type with no `Code.Binds` format, one read other than as a name or a field path, or one whose chain takes a run-time value outside a lambda, as in `.limit(n)`. |
| `cannot bind captured value` | A captured value at a `Code.Binds` place whose type the format can't encode. |
| `reified function performs an effect` | A function, or a `Code.ty_of` type, with an effect. |
| `cannot reify a code value` | A function that reads a value built from `Code`: a description, a value computed from one, an id, or a `Code.ty_of` type. |
| `template needs a constant` | A template argument that's only known when the program runs. |
| `cannot normalize this function` | A function whose normal form reaches a bound the language sets. |
| `code is not allowed here` | A `Code` anywhere but a parameter of the outermost function of an annotation, or the result of a template. |
| `cannot bind inputs in a generic function` | A [query fragment](#query-fragments) whose translator binds inputs and whose chain reads a run-time value outside a lambda at a `Code` place. |
| `cannot reify through a where requirement` | A query fragment that a `where` requirement selects. |
| `cannot reify in a local generic function` | A use of a query fragment inside a function that a block made generic. |
| `cannot reify in a method the compiler calls` | A query fragment, `Code.ty_of` or `Code.type_id` at the type variables of `to_inspect`, `is_eq`, `to_hash`, `encoder_for` or `parser_for`. |
| `cannot reify at an open platform requirement` | A function the platform requires, at a type that leaves a type variable open with a constraint, when the function holds a `Code` place at its own type variables. |
| `not a primitive` | A `code_primitives` entry that isn't `Code.prim` of a top-level function or constant. |
| `cannot read this cut` | A `code_primitives` item that isn't a list of `Code.prim` entries, or the name of a constant of the same module that is one. |
| `primitive listed twice` | One function in a `code_primitives` list two times. |
| `already a primitive` | A builtin, an intrinsic, or a function or constant of an opaque type, in `code_primitives`. |
| `not a definition` | `Code.prim` of something that isn't a top-level or imported function or constant. |
| `call this function` | `Code.prim`, `Code.type_id` or `Code.ty_of` used as a value. |
| `not a nominal type` | `Code.type_id` of a proxy whose type isn't a nominal type. |
| `type not fixed` | `Code.ty_of` of a proxy whose type has a type variable that nothing fixes. |
| `exists only in reified code` | A call or a use, in code that runs, of an [intrinsic](#intrinsics) or of a function that reaches one. |
| `translation refused` | A translator that called `refuse_at`. The reason is the translator's own. |

A refusal in another module's source, such as inside a package function that a described function calls, is shown in that module's file, followed by the place in your module that reached it.

## Performance

A `Code` exists only during the build. The description is built one time for each place that names a function. Two places with equal descriptions give equal `Code` values. A translator that caches what it wrote can use `Code.to_hash` and `Code.version` as the key.

A translator that runs while a top-level value is evaluated has its result stored in the binary as a [constant](compile-time). A translator also runs during `roc check`, and the result is not cached between runs. A slow translator makes both slower.

## Examples

| Example | What it shows |
| --- | --- |
| [`examples/reifying/hello`](https://github.com/roc-lang/roc/tree/main/examples/reifying/hello) | A translator of about 60 lines. An arithmetic function in, an expression out. Both ways to refuse. |
| [`examples/reifying/glsl`](https://github.com/roc-lang/roc/tree/main/examples/reifying/glsl) | A GLSL 330 fragment shader written as a Roc function. The `inline` view and `to_tree`. A CPU interpreter of the same description. |
| [`examples/reifying/sql`](https://github.com/roc-lang/roc/tree/main/examples/reifying/sql) | Query clauses and migrations as Roc functions, and SQL out. The `graph` view with `Call` expansion. A captured opaque `Time` bound with `Code.Binds`, and the glue package `time_sql` as an extension. |
| [`examples/reifying/dbsp`](https://github.com/roc-lang/roc/tree/main/examples/reifying/dbsp) | Incremental views as Roc closures, and a Rust circuit out. |
