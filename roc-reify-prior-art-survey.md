# Reification: ideas from niche and experimental languages

A survey of how less mainstream languages move a computation into a form
another compiler can read, and which of their ideas could work within Roc's
constraints. It is separate from `roc-reify-proposal.md` section 8, which covers
the closest prior art (C#, F#, Julia, Swift macros, Scala 3). Each idea here
addresses a specific open problem of that proposal or of its checklist,
`roc-reify-design.md`.

Roc's constraints, which decide every verdict below:

| Constraint | Consequence |
|---|---|
| No higher-kinded types | no `Rep[_]`, no category class `k a b` |
| No macros, one syntax for a function | nothing rewrites source before checking |
| Static dispatch with `where` clauses | the only mechanism for ad hoc polymorphism |
| Structural records and tags, row polymorphism | a record of symbolic values is an ordinary record |
| Pure functions, syntactic purity, platform-owned effects | no effect handlers to reinterpret a body |
| Monomorphization, lambda sets, compile-time evaluation | the compiler knows each call's instantiation and each function value's finite set of candidates |
| `AGENTS.md` | no fallbacks and no heuristics after parsing; every stage consumes explicit data |

---

## 1. Summary

| # | Idea | From | Open problem it addresses | Fit |
|---|---|---|---|---|
| 1 | A runtime capture becomes a typed parameter slot | C# with Entity Framework, Unison, Spark | a capture of a name nothing fixes is refused (`roc-reify-design.md:76`) | high |
| 2 | A `Code` remembers the function it describes | Swift `@differentiable` function types | rule 5, inert `Code`; no reference implementation next to the translation | high |
| 3 | A derivable method lifts a value into a description | Template Haskell `Lift`, Lean `ToExpr`, Scala 3 `ToExpr` | lists, opaque values have no chosen representation (proposal section 13) | high |
| 4 | Rows keyed by content hash, names as metadata | Unison, Dhall | row serials such as `Test.id#1` depend on walk order | medium-high |
| 5 | Normalize before describing, with a stated guarantee | Links, T-LINQ, Clash | exclusion 1: a function chosen by an `if` (proposal section 10) | medium |
| 6 | Virtualized syntax, generic code over a representation | Scala-Virtualized with LMS, GHC `RebindableSyntax` | proposal 7.3 calls tracing closed to Roc | low-medium |
| 7 | A variable-free description | Conal Elliott's compiling to categories | alpha-equivalence for rule 6 | low |
| 8 | Guaranteed specialization of kernel parameters | Triton `constexpr`, Taichi `ti.static`, AnyDSL filters | mostly covered already | low |
| 9 | A library chooses a path by inspecting its function argument | Flix purity reflection | one API for reifiable and opaque functions | reject |

Ideas 1, 2 and 3 compose: section 6 shows them as one change.

---

## 2. High fit

### 2.1 A capture becomes a typed parameter slot

What the others do. C# expression trees keep a captured local as a member read
on the closure object. Entity Framework translates that read into a SQL
parameter (`WHERE age >= @__min_age_0`) and sends the value beside the SQL
text, while a literal written in the lambda is embedded in the SQL. The split
matters: one SQL text serves every value, so the database reuses its plan. F#
quotations embed captures as constants instead, and every distinct value then
produces distinct SQL. Unison and Spark ship closures to other machines on the
same principle: the code is fixed and addressable, and the environment is data
sent beside it.

The problem it addresses. The checklist now describes a value the block around
the lambda binds, by replaying the binding statement (`roc-reify-design.md:69`),
and still refuses a name nothing fixes: "a function parameter, a branch or loop
binder, or a `var`" (`roc-reify-design.md:76`). The proposal names captures the
one remaining item that "needs a representation chosen" (proposal section 10). Rule 3
justifies the refusal by timing: a captured runtime value "could only arrive as
an opaque pointer". Entity Framework shows a third option. The value arrives as
data in a slot whose type the checker already fixed, and the description names
the slot rather than the value.

For Roc:

```roc
adults_over : Rel(User), U32 -> Rel(User)
adults_over = |users, min_age|
	users.where(|u| u.age >= min_age)    # refused today: `min_age` is a parameter nothing fixes
```

| Half | When it is fixed | What it contains |
|---|---|---|
| The description | build time, as today | the body, with `Ir.Slot(0, Meta)` where `min_age` is read; `Meta.ty` is `U32` |
| The environment | run time, at the site | `[U32(min_age)]`, one value per slot, in slot order |

The translator's `from_code` still runs at build time, on the description
alone, because the description is closed. The compiler hoists that call to a
build-time constant and pairs its result with the environment at the site:

```roc
Pred :: { sql : Str, params : List(Code.Value) }.{
	from_code : Code(User -> Bool) -> Try(Pred, [BadCode(Str)])
	# emits "age >= $1" and records that $1 is slot 0 at U32
}
```

At run time the site builds `Code.Bound(Pred)`, holding the compiled constant
and the environment, and `Db.run!` sends the SQL and the parameters together.
For GLSL a slot is a `uniform`; for DBSP it is an operator parameter.

What it costs. Rule 7 ("every `Code` value is fully determined at build time")
narrows to "every description is determined at build time; a `Code` may carry
runtime values in declared, typed slots". Rule 6 equality compares descriptions
and ignores slot values, which is what a plan cache wants. A slot holding a
function stays refused: exclusion 1 still applies, since nothing fixes which
function arrives.

Fit with `AGENTS.md`: slots come from the capture set the checker already
records for a lambda (explicit data), and nothing is guessed.

### 2.2 A `Code` remembers the function it describes

What Swift does. A `@differentiable` function value is a bundle: the original
function plus its derivative functions, formed by the compiler at the
conversion. The value stays callable, and the extra artifacts ride along.

The problem it addresses. Rule 5 makes `Code` inert: "no `run : Code(a) -> a`".
The rule conflates two things. Splice generates new code and makes Roc a
two-level language (proposal section 12). Calling the original function
generates nothing: every reified function is statically known, so its compiled
machine code already exists.

For Roc:

```roc
Code(fn) :: { defs : List(Def), root : Ir, original : fn }.{
	call : Code(fn) -> fn
	call = |Code.(inner)| inner.original
}
```

What it buys a library author:

| Use | Today | With `call` |
|---|---|---|
| A reference implementation | the user's own function, which the library never sees | the library holds it next to the translation |
| Differential testing of a translator, the "only defence" of proposal section 13 | written per application | written once in the library: run the translation and `call` on the same input |
| An in-memory `Rel` for tests | a second evaluator over `Ir` | `code.call(row)` |

What it costs. Equality and hashing (rule 6) must skip `original`, because
functions have no `is_eq`. It is an open question whether the const store
accepts a function value inside a build-time constant. The checklist folds
top-level values into descriptions (`roc-reify-design.md:68`), and whether a
function value survives that path has not been measured.

This is not splice: `call` returns the function that was written, never one
derived from the description.

### 2.3 A derivable method lifts a value into a description

What the others do. Template Haskell has a `Lift` class with
`lift :: t -> Code t`, derivable with `DeriveLift`. Lean 4 has `ToExpr`, and
Scala 3 has `ToExpr[T]`. Each turns a value into the term that rebuilds it, and
none lifts a function.

The problem it addresses. Proposal section 13 says folding a constant into a
description "works cleanly for scalars, records and tuples and has no answer yet
for a list, an opaque value or a function". Roc already answers the same
question for codecs, with derived `encoder_for`: structural types derive it
automatically, and a nominal type opts in or writes its own.

For Roc, one more derivable method beside the existing six:

```roc
Money :: { cents : I64 }.{
	# written by hand: the description names the public constructor,
	# not the hidden representation
	to_code : Money -> Code.Ir
	to_code = |m| Code.Ir.Call("Money.from_cents", [Code.Ir.lit_i64(m.cents)], Code.meta_of(Money))
}

Palette := [Warm, Cool].{
	to_code : _    # derived: describes as the tag
}
```

| Value | Description |
|---|---|
| scalar, `Str`, `Bool` | `Lit`, as today |
| record, tuple, tag, list | `MakeRecord`, `MakeTuple`, `MakeTag`, `MakeList` of lifted parts, derived |
| opaque type with `to_code : _` | its backing value, derived |
| opaque type with a hand-written `to_code` | whatever its author wrote, so the representation stays private |
| function | no `to_code`; refused, as `Lift` refuses it |

With idea 1 the same method serves run time: a slot value of a structured type
is encoded by the same `to_code` when the environment is built.

---

## 3. Medium fit

### 3.1 Rows keyed by content hash

What the others do. Unison identifies every definition by a hash of its syntax
tree, with local names erased and dependencies referenced by their hashes. A
name is metadata attached to a hash. Dhall hashes the normalized,
alpha-normalized expression for its integrity checks.

The problem it addresses. A generic callee today yields rows named by walk
order: "`Test.id` and `Test.id#1`: the walk counts rows per name and every row
after the first takes its count as a serial" (`roc-reify-design.md:156-165`).
Adding an unrelated call earlier in a body renumbers rows, and a translator
that caches by row name then misses or, worse, reuses the wrong artifact.

For Roc: key each `Def` by a hash of its description, with locals erased and
callees referenced by their own row hashes, and keep the written name and
instantiation as metadata for the translator's diagnostics and emitted
identifiers.

| | Name with serial | Content hash |
|---|---|---|
| Stable under an unrelated edit | no | yes |
| Identical rows from two packages | two rows | one row |
| Cache key for a compiled artifact (rule 6) | needs a separate hash | is the key |
| Readable in emitted code | yes | only through the metadata name |

Mutual recursion needs Unison's treatment: a cycle is hashed as one component,
and each member is addressed by component hash and index.

### 3.2 Normalize before describing, with a stated guarantee

What the others do. Links integrates queries through a normalization procedure,
and Cheney, Lindley and Wadler proved that every quoted query of flat relation
type normalizes to one SQL query. The guarantee is stated by type, not by
syntax. Links also tracks, with a row-based effect type, whether a function can
run in the database at all. Clash, which compiles Haskell to hardware, runs a
normalization pass that specializes away higher-order functions; one of its
transformations pushes an application into the branches of a `case`.

The problem it addresses. Exclusion 1 of proposal section 10 refuses "a
function value nothing fixes: chosen by an `if`, read from a record field, taken
from a list". Two of those three are often fixed after all:

```roc
scale = if hdr { tone_map } else { clamp }
scale(color)
```

Here nothing fixes `scale`, but applying it commutes with the `if`:
`if hdr { tone_map(color) } else { clamp(color) }`, which names only fixed
functions. Purity makes the rewrite exact.

| Shape | Normalizes to | Needs a runtime representation of a function |
|---|---|---|
| `(if c { f } else { g })(x)` | `if c { f(x) } else { g(x) }` | no |
| `{ op: f }.op(x)`, the record literal in scope | `f(x)` | no |
| `match t { A => f, B => g }(x)` | a `match` of two calls | no |
| a function taken from a list, or from a parameter | none | yes, so still refused |

The Links lesson is to publish the guarantee with the rewrite. Roc can state
one: a function value built only by `if`, `match` and record literals from
fixed functions, and applied in the same body, describes. The rest of exclusion
1 stays.

Fit with `AGENTS.md`: the rewrite consumes explicit checked structure, and the
lambda set already names the finite candidates. It is still a rewrite of the
description, so it belongs in `design.md` as a declared rule, with the accepted
and the refused shapes pinned by tests.

---

## 4. Low fit, worth knowing

### 4.1 Virtualized syntax: tracing without reification

What the others do. Scala-Virtualized rewrites `if (c) a else b` into
`__ifThenElse(c, a, b)`, `while` into `__whileDo`, and `==` into `__equal`,
each overridable. Lightweight Modular Staging then writes a program once
against `Rep[T]`: run on `T` it computes, run on `Rep[T]` it builds code. GHC's
`RebindableSyntax` rebinds `if` and literals the same way.

What it says about Roc. Proposal 7.3 calls tracing closed to Roc because
"`is_eligible` takes a concrete `User`". That is true of an annotated function
only. An unannotated one is inferred with a `where` clause over structural
rows, so it already accepts a record of symbolic values:

```roc
is_eligible = |u| u.age >= 18 and u.country != Banned
# inferred: { age : a, country : c, .. } -> Bool where [a.is_gte : ..., a.from_numeral : ..., c.is_eq : ...]
```

Two surface rules stop the trace: `>=` must return `Bool`, and `and` requires a
`Bool`. Virtualizing both would let `{ age: Sym.col("age"), country:
Sym.col("country") }` trace into a `Sym`.

Why the fit is low:

| Limit | Consequence |
|---|---|
| annotations end it | the common case, a function annotated with concrete types, cannot trace |
| sharing is lost | `examples/reifying/glsl/main.roc:19-21` notes that a binding read four times became four texture fetches in the DSL control; LMS recovers sharing by let-insertion through side effects, which pure Roc cannot observe |
| recursion unrolls forever | LMS needs explicit staging of recursive functions |
| `match` on a symbolic value | no virtualization gives it a meaning |
| blast radius | changes what `>=`, `and` and `if` mean for all code, which proposal 7.1 already priced |

### 4.2 A variable-free description

Conal Elliott's compiling to categories translates ordinary Haskell functions
through GHC Core into morphisms of any cartesian closed category the consumer
chooses: circuits, a subset of C, automatic differentiation, interval analysis.
The description has no variables, so alpha-equivalence (rule 6) is syntactic
equality. Roc cannot express the category class without higher-kinded types,
and a point-free term is far harder for a translator author to read than `Let`
and `Local`. The one transferable fact: differentiation becomes one more
interpretation of the same description, which weakens section 12's claim that
it waits on splice for any use that only needs the derivative as data.

### 4.3 Guaranteed specialization of kernel parameters

Triton marks a kernel parameter `tl.constexpr` and compiles one kernel per
value. Taichi's `ti.static` forces an `if` or `for` to be resolved at compile
time, and AnyDSL annotates a function with filters that decide when a call is
specialized. Roc covers most of this already: template arguments fold to
literals (`roc-reify-design.md:66`), top-level values fold
(`roc-reify-design.md:68`), and monomorphization specializes every generic
callee. The remaining piece, unrolling a loop over a fixed range, belongs to a
translator that sees `Ir.For` over a literal `Range`, not to the compiler.

---

## 5. Rejected, and cautionary

| Idea | From | Why not |
|---|---|---|
| A library inspects whether its function argument is reifiable and picks a path | Flix purity reflection | Entity Framework Core 3.0 removed automatic client-side evaluation because the silent fallback hid performance cliffs. In Roc it would also be a fallback the compiler resolves |
| The compiler's own typed AST, exposed | Nim `getImpl` and typed macros | ties every consumer to compiler-internal node kinds, the second definition of an expression that proposal 7.6 warns about |
| Reflection of declarations only | C++26 reflection (P2996) | reflects declarations and types and leaves expression bodies out, which is Zig's half again (proposal section 8) |
| Effect handlers reinterpret a body | Koka, Effekt, Eff | Roc has no handlers, and its effects belong to the platform |
| Elaborator reflection | Idris 2, Agda, Lean 4 | generates definitions, which is splice |
| Parameters embedded as constants | F# quotations with Entity Framework | every distinct value produces distinct SQL; idea 1 keeps slots and literals apart for this reason |

---

## 6. Ideas 1, 2 and 3 as one change

Ideas 1, 2 and 3 amend two rules of proposal section 3 and add one derivable
method:

| | Today | Amended |
|---|---|---|
| Rule 3, closed | every capture refused | a capture of a non-function value becomes a typed slot; a function capture is refused |
| Rule 5, inert | no way to call a `Code` | `Code.call` returns the original function; no splice |
| Rule 7, build time | every `Code` fixed at build time | every description fixed at build time; slot values arrive at run time |
| Constants | scalars, records, tuples | anything with `to_code`, derived or written |

What stays: the translator sees a closed, monomorphic, first-order description
at build time, and the boundary rule of proposal section 10 keeps its three
exclusions. The only change to the third exclusion is that a runtime value now
arrives through a declared slot instead of being refused.

---

## Sources

- Entity Framework parameterization of captured variables: [dotnet/efcore#22430](https://github.com/dotnet/efcore/issues/22430), [dotnet/efcore#28151](https://github.com/dotnet/efcore/issues/28151); F# captures as constants: [dotnet/fsharp#12841](https://github.com/dotnet/fsharp/issues/12841)
- Swift differentiable function values: [DifferentiableProgramming.md](https://github.com/swiftlang/swift/blob/main/docs/DifferentiableProgramming.md)
- Links and T-LINQ: [A practical theory of language-integrated query](https://homepages.inf.ed.ac.uk/slindley/papers/practical-theory-of-linq.pdf), [Row-based effect types for database integration](https://homepages.inf.ed.ac.uk/slindley/papers/corelinks.pdf)
- Compiling to categories: [paper](http://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf)
- Scala-Virtualized and LMS: [Virtualized Scala reference](https://github.com/TiarkRompf/scala-virtualized/wiki/Virtualized-Scala-Reference), [Lightweight Modular Staging](https://scala-lms.github.io/)
- Flix purity reflection: [ECOOP 2023 paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2023.18)
- AnyDSL: [Shallow embedding of DSLs via online partial evaluation](https://compilers.cs.uni-saarland.de/papers/gpce15.pdf)
