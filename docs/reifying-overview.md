# Code Reification: An Overview

This page is for Roc community members who have not followed the work. It explains what the feature does, how it works, and where it stops. The `reify` branch holds a working prototype. Nothing here is on `main` yet.

The user guide is [langref/reifying.md](langref/reifying.md). The full design is in [../roc-reify-design.md](../roc-reify-design.md) and [../design.md](../design.md) (section "Code Reification").

## 1. Overview

### The problem

Roc has no way to say where a pure computation runs. A shader, a database predicate, and an incremental view each need a pure Roc function to run somewhere else. Today the function reaches any other tool as a function pointer. A tool cannot read a function pointer, translate it, or fuse it with another one.

The usual answer is a DSL built with static dispatch. A DSL works, but its values are not the real thing. A DSL shader is an `Expr`, not an `F32`. You cannot call it, test it with `expect`, or step through it. Bindings do not survive. The GLSL example shows one binding that becomes four texture fetches in a DSL.

### The idea

A function that stands where a type says `Code(f)` is not called. The compiler describes it. The description is a plain Roc value of the type `Code.Graph`. A function that takes a `Code(f)` is a translator. A translator is ordinary Roc code that runs while the compiler runs. It reads the description and returns something else: GLSL text, SQL text, a Rust program. Or it refuses, and the compiler reports the refusal at the source line that the user wrote.

The described function stays an ordinary Roc function. You can still call it and test it.

### A tiny example

This translator is from [../examples/reifying/hello/Calc.roc](../examples/reifying/hello/Calc.roc):

```roc
to_expr : Code(f) -> Try(Str, [Unsupported(Str)])
to_expr = |code| {
	row = code.graph().root_row()
	text = Calc.root_text(row)
	match text {
		Ok(expr) => Ok(expr)
		Err({ why, .. }) => Err(Unsupported(why))
	}
}
```

This is the call site, from [../examples/reifying/hello/main.roc](../examples/reifying/hello/main.roc):

```roc
area : F64, F64 -> F64
area = |w, h| w * h + 1.0

expect Calc.to_expr(area) == Ok("((p0 * p1) + 1)")
```

`area` is an ordinary function. It stands where `to_expr` expects a `Code(f)`, so the compiler describes it. A lambda written at the place also works, for example `Calc.to_expr(|x| x * 2)`.

### What users get

| You get | How |
| --- | --- |
| Translators written in plain Roc | GLSL, SQL, and Rust for the `dbsp` crate are examples. A translator is a library function. The compiler does not know the words shader or SQL. |
| Source that is also a function | The code you hand to a translator is the code you can call and test. |
| Compile-time errors at your code | A translator calls `Code.refuse_at`. The compiler reports the reason at every source line the node came from, with the calls that reached it. |
| The same output after a refactor | A rename, a reordered binding, or an extracted helper gives the same description, so the same output. |
| Ordinary typing | A type error in the described function is an ordinary type error at the ordinary place. |

### The boundaries

| Boundary | Meaning |
| --- | --- |
| Pure functions only | An effectful function, `dbg`, and a hosted function are refused. |
| Only what the compiler can fix | A function is described when everything it names is known while the compiler runs. A function value that only the running program knows has no body to read, so it is refused. A value that only the running program knows is refused too, unless the translator returns a `Code.Bound` (see [Captured run-time values](#captured-run-time-values)). |
| A translator checks its own target | The compiler never asks if a GPU can run `Str.split_on`. The translator answers that and refuses. |

The full list of refusals is in [section 4](#4-status-and-limits).

## 2. How it works

### Two views of a description

A description is a graph of functions. Each function is a _row_. The translator picks a view with the type of its parameter.

| View | Parameter | Read with | A call of a helper |
| --- | --- | --- | --- |
| graph | `Code(f)` | `code.graph()` | A helper called from one place is inlined. A helper called from two or more places, a recursive helper, or a helper that holds a `return` in a loop or an arm is a row. Each call is a `Call` node. |
| inline | `Code.Inlined(f)` | `code.inline()` | Every call is inlined. A recursive helper, or a helper that holds a `return` in a loop or an arm, stays a row. |

A target with no function form, like one GLSL expression, reads the inline view. A target with functions, like SQL with common table expressions, reads the graph view.

The rules for the two views are in [../src/reify/views.zig:1](../src/reify/views.zig).

### The shape of `Code.Graph`

All the types are in the `Code` module of `Builtin.roc` (lines 23625 to 24212). `roc docs --builtins` lists them.

| Type | What it holds | Line in `Builtin.roc` |
| --- | --- | --- |
| `Graph` | `{ root, rows, slots }`. The rows that a site reaches, root first, and the types of the root's input slots. | [24078](../src/build/roc/Builtin.roc) |
| `Row` | One function: `id`, `params`, `result`, `nodes`, `body`, `recursive`. | [24055](../src/build/roc/Builtin.roc) |
| `Node` | `{ op, args, ty, speculatable }`. | [24019](../src/build/roc/Builtin.roc) |
| `Op` | What a node does. There are 24 ops: `Lit`, `Prim`, `Call`, `Closure`, `Switch`, `ForList`, and others. | [23959](../src/build/roc/Builtin.roc) |
| `Val` | What a node reads: `Param(k)`, `Node(i)`, `Out({ node, k })`, `Arg({ owner, k })`, `Input(k)`. | [23846](../src/build/roc/Builtin.roc) |
| `Region`, `End` | A body, a switch arm, or a loop body, and how it ends: `Value`, `Jump`, `Return`, `Continue`, `Break`, `Branch`. | [23879](../src/build/roc/Builtin.roc), [23896](../src/build/roc/Builtin.roc) |
| `Ty` | The type of a node: `F64`, `Str`, `ListOf(..)`, `Record(..)`, `TagUnion(..)`, `Named(name, backing)`, and more. | [23632](../src/build/roc/Builtin.roc) |
| `Tree` | One row as nested expressions. | [24137](../src/build/roc/Builtin.roc) |

A node does not carry a name or a source place. A parameter is `Param(0)`, not `w`. The order of `nodes` comes from the graph alone.

A function of another package, and a builtin, is a `Prim`. The body is not read. A translator maps it by name. The GLSL example maps `Glsl.Vec3.scale` to `*`.

A `Record` node holds the names of the fields it sets. They are every field of the type, unless the type marks a field `Optional` and the record leaves it unset (`{ a: v, b: _ }`). A translator reads the names, and the type says which fields may be absent.

### How a translator walks a graph

`Graph.to_tree(id)` turns one row into nested expressions ([../src/build/roc/Builtin.roc:24107](../src/build/roc/Builtin.roc)). A value that is read one time is written where it is read. A value that is read more than once stays a `Def`, so shared work stays shared.

The GLSL translator, the SQL translator, and the DBSP translator all use `to_tree`. A translator that wants to refuse with `refuse_at` must keep the index of a node, so it walks `row.nodes` and `Val` as the hello example does.

The description is a normal form. Some forms are not the ones you wrote. For example, `x >= 10` over integers arrives as `is_lte(10, x)`, and `"a${x}b"` arrives as one n-ary `concat`. Each form is a rule of the normal form, so it holds for every `Code` of one version. The table is in the docs of `Code.Op` ([../src/build/roc/Builtin.roc:23935](../src/build/roc/Builtin.roc)).

### Captured run-time values

A lambda can read a value that exists only when the program runs, such as a parameter of the function around it. The translator receives such a value as an input slot when its declared return type is `Code.Bound(a)`. The rules are in section 10.1 of [../roc-reify-proposal.md](../roc-reify-proposal.md), and N18 of [../roc-reify-normal-form.md](../roc-reify-normal-form.md).

| Item | Rule |
| --- | --- |
| A slot | A run-time name with the `Field`, `Index` and `Unwrap` reads of it. `order.price` is one slot. The description reads it as `Input(k)`. |
| Slot types | `Graph.slots`, in the order in which the root first reads each slot. |
| The translator | Runs once, while the compiler runs, and returns `Code.bound(code, value)`. It emits one placeholder for each slot, for example `?1` in SQL. |
| The program | Reads `bound.value()` and `bound.inputs()`: one `Code.Value` for each slot, built where the program reads the call. |
| Refused | A `var`, a read in a row other than the root, a slot type that holds a function, an opaque type or an optional field, a call with two such sites, a call whose other arguments are not fixed while the compiler runs, and a translator result that holds a function. |

The SQL example binds a captured value as a `?` parameter (`orders_of_at_least` in [../examples/reifying/sql/main.roc](../examples/reifying/sql/main.roc)).

### Refusal, and where errors point

A translator has two ways to refuse.

| | Return an `Err` | `Code.refuse_at` |
| --- | --- | --- |
| Written as | `Err(Unsupported(reason))` | `code.refuse_at({ row: row.id, node: index }, reason)` |
| What the user sees | What the caller does with the `Err` | A `translation refused` report at every source line the node came from |
| Test with `expect` | Yes | No. The build stops. |

The description holds no source places. The compiler keeps a separate table from each node to the expressions it came from. `refuse_at` is the only reader of that table. The report lists the calls that reached the node. A call in the same module shows its line and column. A call in another module names the module.

At run time, `refuse_at` is an ordinary crash with the message.

### How types are fixed at the call site

A described function is read the way the compiler reads a compiled one. There is no special typing rule.

| Case | What happens |
| --- | --- |
| The `Code(f)` type | `f` gives the types of the root. A generic root such as `twin : a -> (a, a)` named at `Code(Str -> (Str, Str))` has `a` at `Str`. |
| A generic helper | It is described once for each type its call fixes. `id` called at `F32` and at `U64` is two rows. |
| An unannotated helper | It is described at the type each use gives it. A lambda written at the site can call one, and a helper can call another generic helper. |
| A number with no other type | It takes the ordinary default. `\|x\| x * 2` describes at `Dec`. |
| A default that does not fit | The function is refused with the reason. `\|x\| x * 2.U8` is refused, because `Dec` has no `*` that takes a `U8`. |
| An open record row or tag row | It seals to its row default, as in a compiled function. `\|r\| r.id > 0` has `r` as `{ id : Dec }`. |
| A type that nothing fixes | The function is refused as polymorphic. `same = \|x\| x` is an example. |

Checking commits nothing for a described function. The walk that builds the description does the sealing, in the same way as the later compiler stage that lowers a function.

### Caching and versioning

| Item | Rule |
| --- | --- |
| `Code.version` | The version of the normal form. It is 9 today ([../src/reify/mod.zig:36](../src/reify/mod.zig)). |
| When the version changes | When the rules, the builtin table, or the speculatable lists change. A fingerprint test pins this. |
| `==` and `to_hash` on a `Code` | They read the normal form and the version. They ignore the site key. Two sites with the same normal form are equal. |
| A translator cache | Use `Code.version` and `Code.to_hash` as the key. |
| The build cache | A module that changes is described again. The key of a module includes the keys of its imports. |

### How it fits the compiler

| Stage | What it does |
| --- | --- |
| Checking | Types the function as usual. Records a site for each function at a `Code` position. Rejects a `Code` in a wrong place, for example in a record field or a callback parameter ([../src/check/Check.zig:21149](../src/check/Check.zig)). |
| Description | Walks the checked bodies and builds the normal form with [../src/reify](../src/reify). Stores the result as a constant. A refused site gives one report and becomes a compile error ([../src/check/code_reifier.zig](../src/check/code_reifier.zig)). |
| Compile-time evaluation | Runs the translator as ordinary Roc. `refuse_at` becomes a crash that carries the site, row and node. The compiler reports it at the source places of the node. |
| Lowering | Restores the stored constant. It never walks a function. |

## 3. Examples

All four are in [../examples/reifying](../examples/reifying). Each one has a README.

| Example | What it shows | Size |
| --- | --- | --- |
| [hello](../examples/reifying/hello/README.md) | The smallest translator: an arithmetic function in, an expression out. Both ways to refuse: an `Err` (`to_expr`), and `refuse_at` (`to_expr_or_stop`, run on `refused.roc` with `roc check`). | `Calc.roc` has 63 lines. 3 `expect`s. |
| [glsl](../examples/reifying/glsl/README.md) | A GLSL 330 fragment shader written as a Roc function. It reads the inline view and uses `to_tree`. `Interp.roc` runs the same description on the CPU, and `main.roc` compares the two. A refactored copy gives the same text. | 8 `expect`s in `main.roc`. |
| [sql](../examples/reifying/sql/README.md) | A schema, migrations, and queries as Roc functions, and a SQLite script out. It reads the graph view and expands each `Call`. `check.py` runs the script on SQLite. | 12 `expect`s in `main.roc`. |
| [dbsp](../examples/reifying/dbsp/README.md) | Incremental views as Roc closures, and a Rust circuit for the `dbsp` crate out. Helpers that two places call become Rust functions. | 19 `expect`s in `main.roc`. |

The control experiment is [shaders-without-reifying](../examples/reifying/shaders-without-reifying/README.md). It writes the GLSL shader as a library DSL, so you can compare the two.

Notes on accuracy:

| Note | Detail |
| --- | --- |
| The DBSP Rust output is not compiled | No test compiles it against the real `dbsp` crate. Every name in it comes from the documented shape of the crate. The README lists two assumptions. |
| The SQL output is run on SQLite | `check.py` does this. The CLI test suite does not run `check.py`. |
| The CLI suite | It runs `hello`, `glsl`, and `dbsp` on `main.roc`. For `sql`, it runs `refactored.roc` only ([../src/cli/test/parallel_cli_runner.zig:3422](../src/cli/test/parallel_cli_runner.zig)). |
| A stale text in the SQL README | Finding 1 there says that a function `groundPendingStagedRows` closes rows. That function is gone. A row now seals to its default when the description is built. The result of the example is the same. |

## 4. Status and limits

### Status

| Part | State |
| --- | --- |
| Where | The `reify` branch. Not merged into `main`. |
| What works | Pure Roc as listed in [../roc-reify-design.md](../roc-reify-design.md): literals, operators, calls (helpers, generic, recursive, other modules), lambdas, templates, `if` and `match`, loops, early `return` and `?`, `var`, `crash`, top-level constants, nominal types, derived methods, and captured run-time values for a translator that returns a `Code.Bound`. |
| Tests | 118 staging cases in [../src/eval/test/eval_staging_tests.zig](../src/eval/test/eval_staging_tests.zig). 181 reifier tests in [../src/compile/test/code_reifier_test.zig](../src/compile/test/code_reifier_test.zig). 49 fixtures `test/cli/Staged*.roc`. 161 normal-form tests in [../src/reify](../src/reify). Fuzzers in `src/reify/fuzz_gen.zig` and `test/fuzzing/fuzz-reify.zig`. |
| Node identities | `Code.Inlined.inline_digest` names a node of the `inline` view by its content (milestone M8). |
| Not done | The translator cannot yet declare which functions of another package it reads (`code_primitives`, milestone M13 of [../roc-reify-normalization-plan.md](../roc-reify-normalization-plan.md)). |

### What is refused today

A refusal names the construct. The rule is that the function must name only things that the compiler can fix.

| Refused | Reason |
| --- | --- |
| A function value that nothing fixes: an item of a list, a `var` that holds a function | There is no body to read. A function chosen by an `if` between known functions is described. |
| A lambda that reads a parameter, a binder, or a `var` of the function around it, where the translator does not return a `Code.Bound` | The value exists only when the program runs. A value that the block binds, or a top-level value, is described. The report names the opt-in. |
| A captured `var`, a captured value read in a row other than the root, a captured function value, a captured value of an opaque type, a captured record with an optional field | The program supplies a slot's value at the call, as one `Code.Value`. These have no such value. |
| A call that binds the slots of two sites, a call whose other arguments are not fixed while the compiler runs, a call whose result type it does not fix, a translator result that holds a function | The call must be a compile-time root of its own. |
| A site that names a top-level value which computes a function, like `Calc.to_expr(doubler)` with `doubler = make(2.0)` | The site's root must be a lambda with parameters that the walk can list. A use of `doubler` inside a described function is described. Write `\|x\| doubler(x)` at the site. |
| A computed top-level value of another package | The body belongs to that package, and the walk does not read it. A value written as data is folded. |
| The body of a function of another package | It is a `Prim`. The translator maps it by name. |
| An effect, `dbg`, a hosted function | Out of scope by design. |
| A type variable that nothing fixes and no default seals | The body reads differently at each type. |
| A numeric default that does not fit its use | For example `\|x\| x * 2.U8`. |
| A template argument that is computed when the program runs | A description is built before the program runs. |
| A custom `from_interpolation` of your own type that returns early with `?`, or is generic in the item type of its assembler | The walk runs the first stage where the literal stands, and a `?` can leave the row it is walked in. |
| An interpolated literal of your own type as a template argument | The checker binds every interpolated value to a name, so the argument is not a constant. |
| Derived `is_eq` on a function | Roc has no equality on functions. |

The list with the exact reason lines is in the section "What the remaining unticked boxes cost" of [../roc-reify-design.md](../roc-reify-design.md).

### Open questions

| Question | Where it is discussed |
| --- | --- |
| What does a crash mean in a target such as a GPU or a database? `Node.speculatable` gives a translator a part of the answer. | [../roc-reify-proposal.md](../roc-reify-proposal.md), section 13 |
| How should a translator refuse a `Dec` that its target cannot run? The refusal exists, but its quality is open. | [../roc-reify-proposal.md](../roc-reify-proposal.md), section 13 |
| Should a translator declare its own set of primitives (`code_primitives`)? Decided, not built. | [../roc-reify-normal-form.md](../roc-reify-normal-form.md), section 12 |
| Should the normal form ever carry a node for the application of an expression? | [../roc-reify-proposal.md](../roc-reify-proposal.md), section 13 |
| How do translators that hand values to a native engine encode them? | [../roc-reify-proposal.md](../roc-reify-proposal.md), section 13 |
| What is the cost for editor latency? A translator runs in `roc check`. | [../roc-reify-proposal.md](../roc-reify-proposal.md), section 13 |
| Should the graph view stay if no translator needs it? | [../roc-reify-normal-form.md](../roc-reify-normal-form.md), section 12 |
| Is the normal form public API forever? | [../roc-reify-proposal.md](../roc-reify-proposal.md), section 7.6 |

## 5. References

| Document | What is in it |
| --- | --- |
| [../design.md](../design.md), section "Code Reification" | The compiler stages, the invariants, and the rewrite rules of the checker. |
| [../roc-reify-design.md](../roc-reify-design.md) | The checklist of what a description covers, with the reason line of each refusal. |
| [../roc-reify-proposal.md](../roc-reify-proposal.md) | The proposal: rationale, alternatives, prior art, open questions. |
| [../roc-reify-normal-form.md](../roc-reify-normal-form.md) | The rules of the normal form. |
| [../roc-reify-normalization-plan.md](../roc-reify-normalization-plan.md) | The milestones of the normal form. |
| [../roc-reify-rule-derivation.md](../roc-reify-rule-derivation.md) | The offline tool that derives the rules. |
| [../roc-reify-refactor-safety.md](../roc-reify-refactor-safety.md) | Which refactors keep the output. |
| [../roc-reify-tag-names.md](../roc-reify-tag-names.md) | Why a tag is identified by its name. |
| [../roc-reify-prior-art-survey.md](../roc-reify-prior-art-survey.md), [../roc-reify-prior-art-comparison.md](../roc-reify-prior-art-comparison.md) | Other languages that reify code. |
| [../roc-reify-fold-alternative.md](../roc-reify-fold-alternative.md), [../roc-reify-whole-design-alternatives.md](../roc-reify-whole-design-alternatives.md) | Designs that were considered. |
| [langref/reifying.md](langref/reifying.md) | The user guide. |

The `Code` module in [../src/build/roc/Builtin.roc](../src/build/roc/Builtin.roc):

| Item | Lines |
| --- | --- |
| The `Code` type and its docs | 23601 to 23625 |
| `Ty` | 23632 |
| `Val`, `Key`, `End`, `Region` | 23846, 23863, 23879, 23896 |
| `Op` | 23959 |
| `Node`, `Row`, `Graph` | 24019, 24055, 24078 |
| `Graph.to_tree` and `Tree` | 24107, 24137 |
| `Code.Inlined` | 24157 |
| `Code.graph`, `version`, `is_eq`, `to_hash`, `refuse_at` | 24184, 24190, 24196, 24200, 24210 |

Key source files:

| File | Role |
| --- | --- |
| [../src/check/Check.zig](../src/check/Check.zig) | Code positions (`stagedCode` at line 27442, `rejectMisplacedStagedCode` at 21149) and sites. |
| [../src/check/code_reifier.zig](../src/check/code_reifier.zig) | The walk that describes a function. |
| [../src/check/checked_artifact.zig](../src/check/checked_artifact.zig) | `reifyStagedCode` (line 38310) and the provenance table. |
| [../src/reify/mod.zig](../src/reify/mod.zig) | The normal-form version, line 36. |
| [../src/reify/views.zig](../src/reify/views.zig) | The two views. |
| [../src/reify/provenance.zig](../src/reify/provenance.zig) | The table from nodes to source places. |
| [../src/check/report.zig](../src/check/report.zig) | The reports, including `translation refused`. |
