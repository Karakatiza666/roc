# Reifying Functions

A _translator_ is a Roc function that runs while the compiler runs. It reads a description of another Roc function and returns something else: GLSL text, a SQL script, a query plan. The described function stays an ordinary Roc function. You can still call it, test it with `expect`, and step through it.

The description has the type `Code(f)`, where `f` is the type of the function it describes. _Reifying_ a function is making this description of it.

This page is for two readers. If you use a translator, read [How a Function Becomes a Code](#how-a-function-becomes-a-code) and [Refusals](#refusals). If you write a translator, read all of it. Start with the [hello example](https://github.com/roc-lang/roc/blob/main/examples/reifying/hello/README.md). It is a translator of about 60 lines.

The rationale and the design alternatives are in [roc-reify-proposal.md](https://github.com/roc-lang/roc/blob/main/roc-reify-proposal.md).

## What a Code Is

A `Code(f)` is a value that holds one function's description. These facts hold for every `Code`:

| Fact | Meaning |
| --- | --- |
| It is typed | `Code(Person -> Bool)` holds only a function of that type. A type error in the function is an ordinary type error at the ordinary place. |
| It is pure | `Code(a => b)` is a type error. An effectful function cannot be reified, because an effect has nowhere to happen while the compiler runs. |
| It is closed | The description has no scope. Everything the function reads from outside is written into the description. |
| It is inert | There is no way to call a `Code`. It is data. |
| It exists only while the compiler runs | You cannot build one by hand, and you cannot annotate a value with `Code`. A `Code` is a function parameter, or the return type of a [template](#templates). |
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
| A method declared on a type | `Calc.to_expr(Meters.twice)` |
| A function bound in a block | `add` in the block of `in_block` in the hello example |
| A lambda written at the place, when the call around it fixes its types | Every clause in the SQL example |
| A function chosen by an `if` between known functions | `g = if up inc else dbl`. The call becomes a `Switch`. |

These forms are refused. Most of them are a function that is only known when the program runs, so no body stands behind it:

| Form | Report |
| --- | --- |
| A function parameter of the surrounding function, named at the `Code` place itself | `cannot reify this function` |
| A function read from a list | `cannot reify this expression` |
| A top-level value that computes a function, as in `doubler = make(2.0)` | `cannot reify this expression` |
| A function that performs an effect | `reified function performs an effect` |
| A lambda that reads a parameter or a `var` of the function around it | `reified function captures a value` |

A function parameter that a call fixes is not refused. In `apply_all = |xs, f| xs.map(|x| f(x))`, the call `apply_all(xs, |x| x * 3)` fixes `f`, so the description names that lambda inside the lambda that `List.map` receives. `xs.map(f)` also describes.

Numbers default as they do in a compiled function. `Calc.to_expr(|x| x * 2)` and `Calc.to_expr(|x| x > 0)` describe at `Dec`. An unannotated helper describes at the type that each use gives it: `triple = |x| x * 3` is `Dec` at a free site, and `U8` when a `U8 -> U8` function calls it.

A function whose types are still not fixed is refused as polymorphic, for example `|x| x`. Give the function a type annotation. A lambda parameter has no annotation syntax, so name the function and annotate it:

```roc
double : I64 -> I64
double = |x| x * 2

Calc.to_expr(double)
```

## The Views

A description is a graph of functions, called _rows_. The translator says which view of the graph it wants with the type of its parameter.

| View | Parameter | Read with | A call of a helper in the same package |
| --- | --- | --- | --- |
| `graph` | `Code(f)` | `code.graph()` | A helper called from one place is inlined there. A helper called from two or more places is a row of its own, and each call is a `Call` node. |
| `inline` | `Code.Inlined(f)` | `code.inline()` | Inlined at every call, however many there are. Only a function that calls itself stays a row. |
| `to_tree` | either | `graph.to_tree(row.id)` | Not a view of the graph. It turns one row into nested expressions. |

For a helper `helper` that `twice = |x| helper(x) + helper(x + 1)` calls two times:

| View | Rows | Nodes in the root row |
| --- | --- | --- |
| `graph` | 2: the root and `helper` | 5 |
| `inline` | 1 | 6 |

A translator for a target with no function form, such as one expression, reads the `inline` view. A translator for a target with functions, such as SQL with common table expressions, reads the `graph` view and keeps each `Call`.

A function of another package, and a builtin, is a `Prim` whose body is not read. A translator maps it by name. The GLSL example maps `Glsl.Vec3.scale` to `*` in this way.

## Reading a Graph

The description is made of plain records and tag unions. All of them are in the `Code` type in `Builtin.roc`, and `roc docs --builtins` lists them.

| Type | What it holds |
| --- | --- |
| `Graph` | `{ root, rows }`. `root_row()` is the function you passed. `row(id)` gives another row. |
| `Row` | One function: `id`, `params` and `result` (as `Ty`), `nodes`, `body`, and `recursive`. |
| `Node` | One operation: `op`, the values it reads in `args`, its type `ty`, and `speculatable`. |
| `Val` | What a node reads: `Param(k)`, `Node(index)`, `Out({ node, k })` for a node with several outputs, or `Arg({ owner, k })` for a parameter of a loop body or a join. |
| `Region`, `End` | A body, a switch arm, or a loop body: its `nodes` and how it ends (`Value`, `Return`, `Break`, `Continue`, `Jump`, `Branch`). |
| `Ty` | The type of a node: `F64`, `Str`, `ListOf(..)`, `Record(..)`, `TagUnion(..)`, `Named(name, backing)` and more. `name()` spells a type for an error message. A `Named` is written with its module and without type arguments, for example `Builtin.Try`. |

A `Val` names a node by its index in `row.nodes`. A node reads only nodes before it. The order of `nodes` comes from the graph alone, so a rename or a reordered binding in the source does not change it.

### One Graph, Walked

```roc
area : F64, F64 -> F64
area = |w, h| w * h + 1.0
```

The graph has one row, `{ id: 0, params: [F64, F64], result: F64, recursive: False }`. These are its nodes:

| Index | `op` | `args` | `ty` |
| --- | --- | --- | --- |
| 0 | `Prim({ owner: "Num.F64", method: "times" })` | `Param(0)`, `Param(1)` | `F64` |
| 1 | `Lit(Frac(1, F64))` | none | `F64` |
| 2 | `Prim({ owner: "Num.F64", method: "plus" })` | `Node(0)`, `Node(1)` | `F64` |

The body is `{ nodes: [0, 1, 2], end: Value([Node(2)]) }`. The names `w` and `h` are gone. A parameter is `Param(0)` or `Param(1)`.

`graph.to_tree(0)` gives the same row as nested expressions. This is the tree, shortened:

```roc
Block({
    defs: [],
    end: Value([
        Op({ op: Prim({ owner: "Num.F64", method: "plus" }), ty: F64, args: [
            Op({ op: Prim({ owner: "Num.F64", method: "times" }), ty: F64, args: [Param(0), Param(1)] }),
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
| Constants | `Lit` | A literal, with its type. |
| Builtin calls | `Prim` | A builtin, or a function of another package. `owner` and `method` are apart, as in `Num.F32` and `sin`. Key your table by `method` and read the type from the node. |
| Function calls | `Call`, `Closure`, `Lambda` | A call of another row, a function value, and a function value written where it is built (`inline` view). |
| Building data | `Record`, `Tuple`, `List`, `Tag`, `Wrap` | `Wrap` puts a value in a nominal type, by name. |
| Reading data | `Field`, `Index`, `Payload`, `Item`, `OptField`, `Unwrap` | A record field, a tuple index, a tag payload, a list item, an optional field, the backing of a nominal. |
| Choosing | `Switch`, `And`, `Or` | `if`, `match`, `?`, `??`, `and`, `or`. |
| Looping | `ForRange`, `ForList`, `Loop` | `for`, `while` and tail recursion. State is in numbered slots. |
| Other | `Crash`, `Derived` | `crash`, and a compiler-derived method such as `parser_for`. A translator that owns the target format expands `Derived`. Every other translator refuses it by name. |

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
| `t?`, `t ?? 0`, `match t { Ok(v) => .. }` | `Unwrap` of the `Try`, then a `Switch` with the arms `Err` and `Ok`. A payload is read with `Payload("Ok", 0)`. | A `Try` is a nominal type, so it has `Unwrap`. |
| `Ok(v + 1)` | A `Tag("Ok")` inside a `Wrap("Builtin.Try")` | `Wrap` names the nominal. |
| `1.0` as an `F64` | `Lit(Frac(1, F64))` | `to_str` prints `1`. Add the `.0` yourself if the target needs it. |

Each row is a rule of the normal form, so it holds for every `Code` of one `Code.version`. A new version can add, change or remove a rule, so a translator matches the forms it knows and refuses the rest by name. The docs of `Code.Op` in `Builtin.roc` list the same rows. The args of a `Prim` are in the parameter order of the builtin, except for a chain of `Str.concat`, `List.concat`, `plus_wrap`, `times_wrap`, `bitwise_and`, `bitwise_or` or `bitwise_xor`, which is one `Prim` with every operand. The full list of rules is in [roc-reify-normal-form.md](https://github.com/roc-lang/roc/blob/main/roc-reify-normal-form.md).

## Refusals

A translator can refuse a function it has no form for. There are two ways.

| | Return an `Err` | `Code.refuse_at` |
| --- | --- | --- |
| Written as | `Err(Unsupported(reason))` | `code.refuse_at({ row: row.id, node: index }, reason)` |
| What the user sees | Whatever the caller does with the `Err` | A `translation refused` report. It is at every source line the node came from, with the calls that reached it. |
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

`Code.Inlined` has its own `refuse_at` for nodes of the `inline` view.

Use an `Err` when you want a test, or when the caller can recover. Use `refuse_at` when the user must fix the source.

## What Is Refused and Why

A function describes when everything it names is fixed by the time checking ends. Only three kinds of thing are never fixed. They are the only exclusions:

| Excluded | Why | Report |
| --- | --- | --- |
| A function value that nothing fixes: a parameter, or an item of a list | There is no body to read. | `cannot reify this function`, `cannot reify this expression` |
| A type that nothing settles: a type variable, or an open row | The body reads differently at each type, so there is no one body. | `cannot reify a polymorphic function` |
| A `Code` that is not fixed at build time: a template argument computed when the program runs | A description is built before the program runs. | `template needs a constant` |

Effects and captured run-time values are refused for the same reason. A function can read a top-level value, a value the block around the site binds, and any named function. Each is written into the description. Everything else in pure Roc describes: recursion, generic functions at the types the program settles, `where` functions, loops, `?`, early `return`, `var`, `crash`, and opaque types.

This is a rule and not a list of supported syntax. If you know the rule, you can predict every refusal. When Roc gains a construct, the construct describes if it names fixed things.

> Note that the compiler reifies, and the translator validates. The compiler never asks whether a target can run `Str.split_on`. A GPU translator answers that in its own Roc, with one of the refusals above.

Some limits exist today and are not part of the rule:

| Limit | Effect |
| --- | --- |
| A function of another package is a `Prim` and its body is not read | A translator cannot read a helper library. It maps it by name. |
| A lambda parameter has no annotation syntax | A lambda whose types neither the site nor the numeric default fixes needs a named, annotated function. `\|x\| x * 2` describes at `Dec`. For `U8`, write `double : U8 -> U8`. |
| A tag union that the checker left open, a record update over a record with an optional field, a `.?` path, and a record pattern that binds its rest | Refused by name. |

## Templates

A function that returns a `Code` is a _template_. The compiler calls it while it runs, and does not compile it. Each argument of a call must be fixed at that time: a literal, a name bound to one, an aggregate of those, or a function. The compiler writes each argument into the description that the call makes.

```roc
add_k : I64 -> Code(I64 -> I64)
add_k = |k| |x| x + k

Calc.to_expr(add_k(5))   # Ok("(p0 + 5)")
Calc.to_expr(add_k(7))   # Ok("(p0 + 7)")
```

One template gives as many descriptions as it has calls. The `5` is a literal in the description by the time the translator reads it.

An argument that is only known when the program runs gives `template needs a constant`:

```roc
runtime = |n| Calc.to_expr(add_k(n))   # ERROR! n is computed when the program runs
```

## Performance

A `Code` exists only during the build. The description is built one time for each place that names a function. Two places with equal descriptions give equal `Code` values. A translator that caches what it wrote can use `Code.to_hash` and `Code.version` as the key.

A translator that runs while a top-level value is evaluated has its result stored in the binary as a [constant](compile-time). A translator also runs during `roc check`, and the result is not cached between runs. A slow translator makes both slower.

## Examples

| Example | What it shows |
| --- | --- |
| [`examples/reifying/hello`](https://github.com/roc-lang/roc/tree/main/examples/reifying/hello) | A translator of about 60 lines. An arithmetic function in, an expression out. Both ways to refuse. |
| [`examples/reifying/glsl`](https://github.com/roc-lang/roc/tree/main/examples/reifying/glsl) | A GLSL 330 fragment shader written as a Roc function. The `inline` view and `to_tree`. A CPU interpreter of the same description. |
| [`examples/reifying/sql`](https://github.com/roc-lang/roc/tree/main/examples/reifying/sql) | Query clauses and migrations as Roc functions, and SQL out. The `graph` view with `Call` expansion. |
| [`examples/reifying/dbsp`](https://github.com/roc-lang/roc/tree/main/examples/reifying/dbsp) | Incremental views as Roc closures, and a Rust circuit out. |
