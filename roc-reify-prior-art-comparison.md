# Reification in Roc compared with industry peers

In Roc, a function passed where the parameter type says `Code(f)` is described,
not called. The description is a `Code.Graph` in a canonical normal form. A
translator, written in ordinary Roc, reads it at compile time and emits SQL, a
shader or another target, or refuses with `Code.refuse_at`.

```roc
area : F64, F64 -> F64
area = |w, h| w * h + 1.0

expr = Calc.to_expr(area)   # Calc.to_expr : Code(f) -> ..., so area is described
```

This note compares that design (`roc-reify-design.md`) with systems that ship
today. Where this note and the design disagree, the design is correct.

**TL;DR**

Bottom line: on most design properties Roc matches or improves on the
strongest peer, and no known system offers them all together for ordinary
inferred pure functions. Certain peers stay ahead on maturity, optimization
depth, run-time and generic code, or generating code back.

- Roc uses C#'s trigger (the parameter type decides), but the description is
  built at compile time, closed, and typed with inferred, monomorphic types.
  Purity is in the type.
- The description is a declared normal form, so a translator handles fewer
  shapes and its output survives a published set of refactors. The price is
  that the translator no longer sees how the user wrote the code. Julia's
  typed IR is the closest peer, but it promises neither a fixed form nor
  stability under refactors.
- A refusal is reported at the user's source line, even though the
  translator never sees source positions.
- Stability across compiler versions trails StableHLO today, but should
  improve with the language. Roc aims to stay a minimal, stable language with
  few but powerful features, and the normal form only has to cover that
  language. After a stable release,
  changes to `Code.version` should therefore be rare. This is an expectation
  from the language's goals, not a published promise like StableHLO's.

---

## 1. Comparison summary

| System | Monomorphic \* | Still an ordinary function | What the consumer reads | Normalized for the consumer | Survives refactors | Stable across compiler versions |
|---|---|---|---|---|---|---|
| C# LINQ `Expression<T>` | **yes**, at the use | **yes**, alongside a compiled delegate | syntax tree with parameter names, and closures captured as object references | **no**: the tree is the syntax | **no**: EF Core caches and translates by tree shape | **yes**, a public API since 2007 |
| F# quotations | **can be generic** | **yes** | syntax tree, and the attribute exposes bodies of named functions | **no** | **no** | **yes** |
| Scala 3 quotes and macros | **can be generic** | **yes** (`inline`) | typed syntax (TASTy) | **no** | **no** | **yes**: TASTy is a versioned format |
| Typed Template Haskell | **can be generic** | **no** | **nothing**: typed code is opaque | **not applicable** | **not applicable** | **no** |
| Julia typed IR, CUDA.jl | **yes** | **yes** | SSA after inference and optimization | **partly**: as a side effect of optimization | **partly**: names and helpers vanish | **no**: internal, changes between releases |
| Rust GPU backends | **yes** | **yes** | MIR | **internal** compiler passes | **partly**, as for Julia | **no**: `stable_mir` is not finished |
| JAX (jaxpr, StableHLO) | **yes**, per shape | **yes** | dataflow equations | **partly**: helpers inlined, but equations stay in execution order | **partly** | StableHLO: **yes**, with a published window |
| PyTorch `torch.compile` / `export` | **yes**, per shape | **yes** | FX graph, node names from source variables | **partly** | **partly** | `export`: **aiming at it** |
| Numba, Triton | **yes** | **yes** | internal IR | **internal** | **internal** | **no** |
| Scala LMS / Delite | **yes** | **no**: code is written against `Rep[T]` | a graph, hash-consed, ordered by dependencies | **yes**, by construction | **mostly** | **internal** |
| Dhall | **not needed** | **not applicable** | alpha-beta normal form, hashed | **yes**, as a guarantee | **yes** | **yes** |
| Unison | **not needed** | **yes** | name-free, hashed syntax trees | **names only** | names and moves only | **yes**, by hash |
| Lean 4 | **can be generic** | **yes** | elaborated `Expr` | **no**: only equality is decided by normalization | **no**: the syntax is fragile | **no** |
| Agda reflection | **can be generic** | **yes** | the `Term` data type, from `quoteTerm` or a `TC` macro | **on request**: `normalise` and `reduce` in `TC` | **partly**: variables are nameless, but helpers and structure show | **no**: reflection changes between releases |
| Idris 2 elaborator reflection | **can express generic terms** | **yes** | `TTImp`, from `quote` in `Elab` | **no**: no such operation in `Language.Reflection` | **no**: keeps names and source positions | **no**: `TTImp` changes between releases |
| MetaOCaml | **can be generic** | **no**: code is written in brackets | **nothing**: typed `'a code` is a black box | **not applicable** | **not applicable** | **no**: each release targets one OCaml version |
| **Roc** | **yes**, and a generic fragment is described per use | **yes** | a `Code.Graph` in one of four views | **yes**: declared, numbered rules | **yes**, for a published refactor set, tested | **versioned**: `Code.version` names the rules |

\* Monomorphism: both kinds accept generic source code. They differ in what reaches the
consumer.
- **yes**: the system fixes the types first, so the consumer reads
only concrete types, one description per use or call.
- **can be generic**: the
code reaches the consumer as written. When the quoted code is generic, the
consumer reads type variables and must handle them itself, for example by
emitting generic target code or by refusing.

---

## 2. The peers

| System | Mechanism | Why it is here |
|---|---|---|
| C# LINQ | the target type `Expression<T>` turns a lambda into a tree | same trigger as Roc, since 2007 |
| F# | quotations and `[<ReflectedDefinition>]` | reifies named functions, as Roc does |
| Scala 3 | `Expr[T]` quotes, splices, TASTy | typed quotation with a versioned format |
| Typed Template Haskell | `Code m a` | typed quotation that cannot be inspected |
| Julia, Numba, Triton, Rust GPU | typed compiler IR handed to a GPU backend | what a GPU library receives |
| JAX, PyTorch | tracing to a graph | the dominant industrial approach |
| Scala LMS | staging over `Rep[T]` | canonical graphs by construction |
| Dhall, Unison | normalization and hashing | refactor invariance as a guarantee |
| Lean 4 | elaborator metaprogramming | inspection of fully elaborated terms |
| Agda | `quoteTerm`, `unquote`, `TC` macros | reflection in a dependently typed language, with normalization on request |
| Idris 2 | elaborator reflection, `Elab`, `TTImp` | building and checking terms through the elaborator |
| MetaOCaml | brackets `.< >.`, escapes `.~`, `'a code` | typed code generation that deliberately cannot be inspected |

### 2.1 C# LINQ expression trees

```csharp
Expression<Func<Person, bool>> e = p => p.Age >= 18;   // a tree
Func<Person, bool> f = p => p.Age >= 18;               // a delegate
```

The same lambda becomes a tree or a delegate depending on the target type. The
tree is built at run time, keeps names, and holds closures as object
references. A provider such as EF Core walks the raw tree, and every
"could not be translated" message comes from the provider.

**Takeaway:** the trigger is proven. The tree is syntax, so providers must
handle every surface shape.

### 2.2 F# quotations and reflected definitions

```fsharp
[<ReflectedDefinition>]
let area w h = w * h + 1.0
```

The attribute makes a named function's body available as a quotation, much as
Roc describes the rows a function calls. The quotation is taken before
inlining and is not monomorphized, so a consumer specializes it itself.

**Takeaway:** the closest relative in what gets reified, with more work left
to the consumer.

### 2.3 Scala 3 quotes and macros

```scala
def square(x: Expr[Int])(using Quotes): Expr[Int] = '{ $x * $x }
```

Quotes are typed, can be generic, and can be spliced back into code. Macros
run at compile time, and TASTy is a versioned format.

**Takeaway:** full typed multi-stage programming, which Roc does not attempt.

### 2.4 Typed Template Haskell and Lean 4

Typed TH's `Code m a` is typed but opaque. To inspect it, a program must drop
to untyped TH. Lean 4 metaprograms read elaborated `Expr` terms, and decide
definitional equality by normalization, but the syntax they inspect still
changes with how the user wrote it.

**Takeaway:** typed quotation and normalized equality exist, but not as a
stable input for a translator.

### 2.5 Julia (CUDA.jl), Numba, Triton, Rust GPU backends

```julia
@cuda kernel(a)   # compiles kernel for the argument types, via typed IR
```

CUDA.jl compiles a Julia function per call signature by reading the compiler's
typed IR after inference and optimization. Names and helpers are gone, so many
surface differences vanish. That IR is internal and changes between releases.
Numba and Triton work the same way with their own internal IR. rust-gpu and
rust-cuda do it ahead of time on MIR, which is also unstable: the `stable_mir`
effort is not finished.

**Takeaway:** the strongest peer for what a library receives, and the closest
one to a normalized input, but with no promise about its shape.

### 2.6 JAX and PyTorch

```python
jax.make_jaxpr(lambda x: x * 2 + 1)(1.0)
```

JAX traces a pure Python function into equations. Helpers are inlined and
Python syntax is gone, but equations appear in execution order, so reordering
independent lines reorders the jaxpr. StableHLO, the format below it, has a
published multi-year compatibility window. `torch.compile` traces bytecode
into an FX graph and falls back to eager execution at a graph break.

**Takeaway:** tracing is cheap and reaches run-time control flow, but what it
keeps is not documented as a contract.

### 2.7 Scala LMS / Delite

User code is written against `Rep[T]`, and running it builds a hash-consed
graph ordered by dependencies.

**Takeaway:** the closest structural relative of Roc's normal form, reached by
writing code in a staged style rather than by describing ordinary code.

### 2.8 Dhall and Unison

Dhall reduces every expression to an alpha-beta normal form and hashes it, so
two equal programs have one hash. Unison stores name-free, hashed syntax
trees, so renames and moves change nothing.

**Takeaway:** refactor invariance as a guarantee, used for identity and
caching, not as input for a translator.

---

## 3. Where the combination stands out

Each row names the single peer with the strongest design for that property.

| Property | Best peer | What the peer does | What Roc does |
|---|---|---|---|
| Trigger | C# LINQ | the target type decides | better: the same trigger, and the description is built at compile time, closed and typed |
| Normalization | Julia typed IR | normalizes as a side effect of inference and optimization, with no promise about the result | different: a declared, versioned normal form. The source shape is gone, but the peer can also hand out unoptimized IR |
| Refactor invariance | Julia typed IR | absorbs many edits, but its shape depends on inlining heuristics, settings and version | better: a published refactor set leaves the description identical, and fuzzers test it |
| Monomorphization | Julia | specializes per call signature | better: specializes at the types each use fixes, as the peer does, and refuses by name when types are not fixed |
| Purity | JAX | requires pure functions, cannot check | better: purity is in the type, so the compiler checks it |
| Error locality | Scala 3 macros | `report.error(msg, expr)` reports at the position of `expr` | equivalent: reports at source positions, as the peer does. One report covers every source place of a node, and the translator never sees regions |
| Captured values | C# LINQ | closures held as object references | different: numbered input slots, bound per call |
| Reach | F# reflected definitions | exposes bodies of attributed functions | better: walks every body without an attribute, down to a translator-decided subset of primitives |

### 3.1 The trigger, against C# LINQ

C# chose the trigger in 2007: a lambda at an `Expression<T>` parameter becomes
a tree. Roc uses the same rule with `Code(f)`, but the value differs. Roc's
description is built at compile time, has no names or source
regions, is closed (everything the function reads is inside), and is typed
with concrete types on every node. A C# tree keeps names, captures closures by
reference, and is translated by its shape, which is why EF Core translations
break on refactors.

### 3.2 Normalization, against Julia's typed IR

The strongest peer here is Julia. CUDA.jl reads typed IR after inference,
inlining and optimization, so names and small helpers are already gone. This
step removes many surface differences, but nothing declares which ones, and the IR
changes between releases. C# is the opposite case. A provider gets the raw
tree and must handle every way the user could write the same thing.

Roc's description is a normal form with numbered rules (design 3.3,
`roc-reify-normal-form.md`). A translator gains these properties:

| Gain | How |
|---|---|
| fewer shapes to handle | one spelling per operation: `x > 10` and `10 < x` are one node, `a != b` is `not` of `is_eq`, `?`, `??` and their `match` are one `Switch`, `for`, `while` and tail recursion are one of three loop forms |
| output that survives refactors | renames, reordered independent bindings, binding once or writing twice, dead bindings, extracting or inlining a helper, and spelling changes leave the graph identical (design 10, section 3.3) |
| equality and caching | `Code.is_eq` and `Code.to_hash` read the normal form and its version, so a translator can key a cache on them, wherever the description came from (design 5.3) |
| a choice of structure | four views decide which helpers stay rows, so a shader reads everything inlined and SQL keeps shared calls (design 3.2) |

The normal form also costs or hides these:

| Cost | Detail |
|---|---|
| the source shape is gone | a translator cannot tell `x > 10` from `10 < x`, whether code sat in a helper or inline, or a constant's name from its folded value. Target output cannot mirror the author's layout or names |
| the choice of forms is fixed | the compiler, not the translator, picks the canonical spelling. A translator that wants another form rebuilds it. A new `Code.version` may change rules, so a translator must refuse forms it does not know (design 3.3) |
| error locations are indirect | after merging and inlining, one node can stand for several source places. A translator's refusal is reported at all of them, with the calls that reached it (design 7.2). A walk refusal inside a callee is reported at the call (design 11) |
| some values arrive late | a literal of the author's own type arrives as its conversion call, not the converted value (design 11) |
| crash order is not kept | the rule C2 promises Roc's result only where Roc neither crashes nor diverges, so two failures may happen in another order (`roc-reify-normal-form.md` 1.1) |

Compared with Julia, Roc gives up optimization depth to get a contract. Julia
also hides the source shape, and goes further, but its result has no promised
form. Roc stops
at rewrites that preserve meaning (section 4), and promises which refactors
leave the graph unchanged. Section 3.3 looks at that promise in detail.

### 3.3 Refactor invariance, against Julia's typed IR

Roc publishes a set of refactors that leave the description identical, in
every view (`roc-reify-normal-form.md` 7, "tier A",
`roc-reify-refactor-safety.md` 4.1, design 10). A named rule absorbs each
refactor:

| Refactor | Why the description does not change |
|---|---|
| rename a local, parameter or helper | binders are positional, and rows have no names (N2, N8, design 5.3) |
| reorder independent bindings, `var` declarations or top-level definitions | node order comes from the graph, and rows are keyed by content (N4, N9, N8) |
| reorder the fields of a record literal | fields follow the type's order, by name (N9, design 3.4) |
| bind a value once or write it twice, or drop an unused binding | hash-consing and dead-node removal (N5, N6) |
| extract a helper used from one place, or inline it | the walk inlines it (normal form 5.1) |
| move a helper to another module or package | every body is walked, wherever it lives (N8, design 4.1) |
| name a constant computed from literals, or write its value | the constant is folded (N13, design 4.3) |
| `x.f(y)`, `f(x, y)`, `x \|> f(y)`, and an operator and its method | one `Prim` (N1) |
| `?`, `??`, `return` and the `match` they mean, or `for`, `while` and tail recursion | one `Switch`, or one of three loop forms (N1, N7, N11, N12) |
| add or remove an annotation that keeps the solved types | types come from the checker |

One case has a weaker guarantee. In the `graph` view, extracting a helper that replaces two
or more copies over different arguments changes which work sits behind a
call ("tier B"). The `inline` and `outline` views absorb it. Edits outside the
set, such as `x * 2` to `x + x`, change the output or stop the build at the
site (normal form 7.1).

Julia's IR absorbs many of the same edits as a side effect. It is SSA after
inference, where each value is numbered by its position. With
`optimize=true`, "additional optimizations, such as inlining, are also applied". But four
things decide its shape, and none is a promise to a consumer:

| What changes the IR | Effect on a consumer such as CUDA.jl |
|---|---|
| inlining by a cost model | the inliner charges a call a fixed cost and adds a penalty for dynamic dispatch. The docs call the model "extremely simple" and the penalty "a mere heuristic". Whether an extracted helper is inlined depends on its cost, so the same refactor can give a call or an inlined body |
| optimization settings | `optimize=false` and `optimize=true` give different IR for the same code |
| the Julia version | the IR is documented under "Documentation of Julia's Internals". GPUCompiler.jl, which CUDA.jl builds on, ships releases such as "Make things work on Julia 1.13" |
| statement order | in Julia's SSA IR "order is semantically significant", and statements are numbered by position. The docs do not describe a canonical order for independent statements |

So Julia's typed IR is an implementation detail that a consumer must track. Roc's set is part of the design, tested by fuzzers that apply
random refactors and compare normal forms, and pinned by `Code.version`.

Julia does better in two ways. Its optimizer goes further than Roc's rules,
so it may absorb edits that Roc leaves outside its set, though nothing says
which. And a consumer can ask for code before or after optimization. A Roc
translator always gets a normal form and never sees the source shape.

### 3.4 Monomorphization, against Julia

Julia specializes per call signature, and code whose types cannot be inferred
falls back to dynamic dispatch, which on a GPU fails deep in inlined code.
Roc infers principal types, and a description is read at the types its use
fixes (design 2.1). A generic query fragment is described again at each
closing use, through an instance table (design 2.4). Where types are not
fixed, as in `|x| x`, the site is refused at compile time with a named report
(design 3.4). There is no dynamic fallback.

### 3.5 Purity, against JAX

JAX requires pure functions but cannot check purity: a side effect runs once
at trace time and disappears. In Roc, `Code(a => b)` is a type error (design
2.1). This type rule lets the normal form reorder, sink and drop work. Its only
semantic promise, C2, is that the result matches Roc wherever Roc neither
crashes nor diverges, and that nothing that can fail is evaluated where Roc
would not (design 3.3). Each node carries a `speculatable` flag, so a
translator knows what it may evaluate early.

### 3.6 Error locality, against Scala 3 macros

A Scala 3 macro calls `report.error(msg, expr)` or
`report.errorAndAbort(msg, expr)`, which report "at the position of `expr`".
Overloads take an explicit `Position` instead. A Roc translator cannot see
positions at all, so it cannot branch on them. It calls `refuse_at` with a row and node, and the compiler reports at
every source place that node came from, with the calls that reached it,
through a provenance table (design 7.2). A translator can also return an
`Err`, which an `expect` can test.

### 3.7 Captured values, against C# LINQ

C# captures closure variables as object references, which a provider must
evaluate. Roc makes each captured value an input slot, `Input(k)`. The
translator runs once and writes a placeholder, and each call supplies the
values (design 6). A captured opaque value is encoded in the translator's
own format through `Code.Binds`.

### 3.8 Reach, against F# reflected definitions

F# exposes the body of a function that carries the attribute. Roc walks every
body the described function reaches, across modules and packages (design
4.1). The translator owns the cut: it names the functions it wants as `Prim`s
in `code_primitives`. Functions over an opaque type stay `Prim`s, so a
description never exposes what Roc hides. Every `Prim` and opaque type carries
a 128-bit id, so a translator recognizes a function by that id rather than by
its name, and a glue package can map another package's functions to a target
without either package knowing about the other (design 5).

---

## 4. Where the peers are ahead

| Area | Best peer | What the peer has | Roc today |
|---|---|---|---|
| Maturity | C# LINQ | shipped since 2007, with many providers | implemented on a branch and unreleased. Tests check the confluence of the simplify phase, but no proof exists |
| Optimization depth | Julia | translators get fully optimized IR | only meaning-preserving rewrites, and each translator optimizes for its target. Builtin laws apply only in the `lawful` view |
| Stability across compiler versions | StableHLO | a published multi-year compatibility window | a new `Code.version` may add, change or remove rules, and ids are not meant to be stored across builds. Because Roc aims to stay a minimal, stable language, such changes should be rare after a stable release |
| Run-time and higher-order code | JAX | traces through arbitrary closures and unrolls Python loops | every function must be fixed at compile time, and a function value that nothing fixes is refused |
| Generic code | Scala 3 | a quote can be generic in `T`, and a macro works with that one generic form | generic code works, but each use is described separately at its own types (design 2.4). A translator sees only instances, never the generic form. Three generic forms are refused (see below) |
| Generating code back | Scala 3 | splices a quote back into code | no splice: a translator returns ordinary Roc values, including closures built from existing functions (a query runner that binds inputs and calls the platform), but not new code that the compiler checks and optimizes. A gradient derived from a description stays data to interpret, not a function to call (`roc-reify-proposal.md` 12) |

The three generic forms Roc refuses:

- **Binding captured values.** A generic fragment whose translator binds
  captured run-time values with `Code.Binds`, such as a reusable filter with a
  run-time parameter.
- **A fragment reached through a `where` requirement.** A method that is
  itself a fragment, called through a requirement such as
  `tidy_twice : b -> b where [b.tidy : b -> b]`. Calling `Wrap.tidy(w)`
  directly works. Scala 3 has the same limit: an abstract inline method called
  through its abstract type fails with "cannot inline".
- **Methods the compiler calls itself.** A fragment inside `to_inspect`,
  `is_eq`, `to_hash`, `encoder_for` or `parser_for`.

The normal form also stops short of Julia on purpose. It does not unroll
loops (except over a list of known length), fuse loops outside `lawful`, or
reassociate float sums (`roc-reify-normal-form.md` 7.2). Refactors such as
`x * 2` to `x + x` stay outside the refactor set and change the output.

The design also lists its own open limits (design 11):

- `Named` types carry no `TypeId`.
- A refusal inside a callee is reported at the call, not inside the callee.
- A lambda whose types nothing fixes needs a named, annotated function.
- The reify-only rule over-approximates per definition (design 9.8).
- A translator's result is not cached between runs of `roc check` (design 8.3).

---

## 5. Where this leaves the design

| Combination | Who reaches it |
|---|---|
| typed, monomorphic reification that keeps functions callable | Julia, the Rust GPU backends and LINQ, in part |
| a normalized input for a translator | Julia, as a side effect, with no contract |
| canonical graphs | LMS, but only for code written against `Rep[T]` |
| normal forms with guaranteed invariance | Dhall and Unison, but not for translation |
| all of these, for ordinary inferred pure functions | no known system |

Roc can offer the combination because it has complete type inference, purity
in its types, and one declared semantic rule (C2) that lets the normal form
reorder and drop work. The cost is the list in section 4: no run-time tracing,
no splice, no deep optimization, and a format that is versioned rather than
frozen.

---

## 6. Other ways to get a description

Other mechanisms also turn code into data. They expose less than full
syntax, and Roc users can use some of them today.

| Mechanism | What it turns into data | Against Roc reification |
|---|---|---|
| Deep embedding: a DSL as a data type | programs written in the DSL | Roc can do this today: operators are methods, so a nominal `Expr` that implements `plus` and `times` builds a tree. The control experiment `examples/reifying/shaders-without-reifying/` shows the costs. The function is over `Expr`, so it cannot run on the CPU or be tested with `expect`. A `let` leaves no trace, so shared work is repeated. `and`, `or` and `if` need invented names. Reification removes the second copy: the author writes one ordinary function |
| Final tagless: operations as an interface over a result type | nothing, because each interpretation is an instance | needs abstraction over a type constructor, which Roc lacks (design 12). An interpretation that wants to analyze a whole body has to build a tree, which brings back the deep embedding |
| Free monads, freer effects | effectful instructions | design 12 rejected them: they structure composition, not representation, the builder still holds a function pointer, and Roc has no higher-kinded types. Roc keeps effects at the platform boundary, and `Code` covers pure code only |
| Generic representations | the structure of a data type | Roc derives codecs (`encoder_for`, `parser_for`) and equality, and `Code.ty_of` gives a translator the `Ty` of a type without a function (design 3.4, 4.5). A schema translator needs no more than this |
| Type witnesses (`TypeRep`) | a type's identity | `Code.type_id` and `Code.Proxy` play this role, as 128-bit ids keyed by the declaration (design 5.1) |
| Defunctionalization | function values, as constructors plus an interpreter | the description is already first order: a function value is a `Closure` of a known row, and every call resolves to a row or a primitive (design 3.1). Reification does this for the author |

Where a DSL is the better tool:

- **Effectful workflows.** A durable workflow that waits on a timer, retries
  an API call or sends an email needs its effects in the description. `Code`
  describes only pure functions, and effects are out of scope by design
  (design 11, 12). A DSL of steps can hold them.
- **Computations built at run time.** A query that a user assembles in a UI
  does not exist when the compiler runs, and `Code` refuses anything not
  fixed by then (design 11). A DSL value can be built at run time.
- **No compiler support.** A DSL is an ordinary library and works on any
  compiler.

---

## 7. Is reification the cleanest approach for Roc?

For Roc's goal, running a pure function somewhere else, it is a good fit, with
known costs.

| Approach | Fit for Roc |
|---|---|
| Run-time reflection | poor: Roc cannot reflect on a function, which compiles to a function pointer (design 1). Reflection would also let any code observe syntax, which makes every refactor unsafe (`roc-reify-refactor-safety.md` 1) |
| Quotation with splices (Scala 3, MetaOCaml) | strong for generating code, but it brings a two-level language, hygiene and cross-stage persistence (`roc-reify-proposal.md` 8). Roc defers splices, and the design names this its most significant omission (`roc-reify-proposal.md` 12) |
| A deep-embedded DSL | works today, but the costs in section 6 make it less ergonomic |
| Reification at code places | no new syntax, one function that runs and is described, purity by type, and translators that are ordinary, testable Roc |

Why reification fits:

- **It avoids the extensional limit.** A pure language cannot recover a
  function's source from the function value. Roc describes the function
  where the type says `Code`, before it becomes a value, as quotation does,
  but without quote syntax.
- **Purity makes the normal form possible.** Reordering, sharing and dropping
  work are sound only because `Code(a => b)` is a type error (design 2.1, C2).
- **Inference supplies the types a target needs.** Users write lambdas
  without type annotations, yet each use still fixes concrete types: a shader
  translator reads `F32` where the user wrote a plain number literal. When
  nothing fixes a type, the compiler names the error instead of guessing or
  falling back to dynamic code (design 2.1, 3.4).
- **Observation is limited to the normal form.** A translator sees no names
  and no regions, so it cannot depend on how the code was written (design 10).
- **The compiler stays domain-free.** It knows the word reification, not
  shader or query, and every target-specific diagnostic is in a library
  (design 1, 7.1).

What it costs:

- **A large public contract.** The normal form's rules, views and version are
  API, and changing them affects every translator (design 3.3, 8.3).
- **Compiler machinery.** Instance tables for generic fragments, the runs bit,
  reify-only definitions and provenance all exist for this feature (design
  2.4, 9).
- **No splice.** A translator returns Roc values: target text, data, or
  closures that compose existing functions, such as one that binds inputs and
  calls the platform. It cannot return new Roc code for the compiler to check
  and optimize, so a translator that derives code, such as a gradient, hands
  back data the program interprets. The design calls this its most significant
  omission (`roc-reify-proposal.md` 12). The compiler also does not check the
  target text a translator emits. The translator or the target checks it.
- **The source shape is gone** (section 3.2).

A common wish list for reflection in a pure language has six features.
Reification in Roc meets five:

- ✅ **Typed representations.** Every node of a description carries its type.
- ✅ **Pure inspection.** A translator is ordinary pure Roc code.
- ✅ **Explicit opt-in.** The `Code(f)` parameter type is the trigger,
  visible in the signature.
- ✅ **No unstable compiler internals as API.** The normal form is a
  versioned format (`Code.version`), not the compiler's IR.
- ✅ **Hygiene** - no accidental name clashes. Holds by construction:
  nothing is spliced back, and a description has no names to capture.
- ❌ **Generated code checked before it runs.** That belongs to a splice.
  Roc has none, so the translator or the target checks what is emitted.

---

## Sources

- C# expression trees: [Microsoft Learn, Expression trees](https://learn.microsoft.com/en-us/dotnet/csharp/advanced-topics/expression-trees/)
- F# code quotations: [Microsoft Learn, Code Quotations](https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/code-quotations)
- Scala 3 macros and TASTy: [Scala 3 guide, Macros](https://docs.scala-lang.org/scala3/guides/macros/macros.html)
- Scala 3 error reporting in macros: [Scala 3 API, `Quotes.reflectModule.reportModule`](https://scala-lang.org/api/3.x/scala/quoted/Quotes$reflectModule$reportModule.html)
- Typed Template Haskell: [GHC proposal 195, Code type](https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0195-code-texp.rst)
- Julia GPU compilation: [CUDA.jl documentation](https://cuda.juliagpu.org/stable/)
- Julia `@code_typed` and its `optimize` flag: [Julia manual, InteractiveUtils](https://docs.julialang.org/en/v1/stdlib/InteractiveUtils/)
- Julia inlining cost model: [Julia developer docs, Inference](https://docs.julialang.org/en/v1/devdocs/inference/)
- Julia SSA IR and statement order: [Julia developer docs, SSA-form IR](https://docs.julialang.org/en/v1/devdocs/ssair/)
- GPUCompiler.jl v1.5.1, "Make things work on Julia 1.13": [Zenodo record 15496915](https://zenodo.org/records/15496915)
- Rust stable MIR: [Rust project goals, stable MIR](https://github.com/rust-lang/project-stable-mir)
- JAX jaxprs: [JAX documentation, Understanding jaxprs](https://docs.jax.dev/en/latest/jaxpr.html)
- Scala 3 inline methods, rules for overriding: [Scala 3 reference, Inline](https://docs.scala-lang.org/scala3/reference/metaprogramming/inline.html)
- StableHLO compatibility: [openxla/stablehlo, compatibility](https://github.com/openxla/stablehlo/blob/main/docs/compatibility.md)
- PyTorch `torch.export`: [PyTorch documentation, torch.export](https://pytorch.org/docs/stable/export.html)
- Tiark Rompf, Martin Odersky, "Lightweight Modular Staging", GPCE 2010
- Dhall semantic integrity checks: [dhall-lang standard](https://github.com/dhall-lang/dhall-lang/blob/master/standard/README.md)
- Unison: [unison-lang.org, the big idea](https://www.unison-lang.org/docs/the-big-idea/)
- Agda reflection: [Agda documentation, Reflection](https://agda.readthedocs.io/en/latest/language/reflection.html)
- Agda 2.6.3 breaking reflection changes: [Agda 2.6.3 changelog on Hackage](https://hackage.haskell.org/package/Agda-2.6.3/changelog)
- Idris 2 elaborator reflection: [Idris 2 base library, `Language.Reflection` source](https://www.idris-lang.org/Idris2/base/source/Language.Reflection.html)
- Idris 2 `TTImp` binders: [Idris 2 base library, `Language.Reflection.TTImp` source](https://www.idris-lang.org/Idris2/base/source/Language.Reflection.TTImp.html)
- Idris 2 reflection changes between releases: [Idris 2 CHANGELOG](https://github.com/idris-lang/Idris2/blob/main/CHANGELOG.md)
- MetaOCaml, including polymorphic code and cross-stage persistence: [Oleg Kiselyov, BER MetaOCaml](https://okmij.org/ftp/ML/MetaOCaml.html)
