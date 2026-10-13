# Reification in Roc compared with industry peers

This compares three properties of the design in `roc-reify-normal-form.md`
with systems that ship today:

| Property | In Roc |
|---|---|
| monomorphization | each `Code` site is described at the types it fixes (proposal rule 4) |
| type inference | principal types for every expression, with no annotations required |
| a stable, normalized representation | translators read the normal form, which is identical for every refactor in R |

Each property has close peers, and several systems combine two of them. None
of the systems below guarantees that a translator's input stays the same
across meaning-preserving refactors, and that guarantee is what this design
adds. This is a design-level comparison: the normal form is unimplemented,
and every peer ships.

---

## 1. The peers

| System | When code is captured | Types the consumer sees | Monomorphic | Still an ordinary function | What the consumer reads | Survives refactors | Stable across compiler versions |
|---|---|---|---|---|---|---|---|
| C# LINQ `Expression<T>` | run time | .NET types | yes, at the use | yes, alongside a compiled delegate | syntax tree with parameter names; closures captured as object references | no: EF Core caches and translates by tree shape | yes, a public API since 2007 |
| F# quotations, `[<ReflectedDefinition>]` | run time | F# types | can be generic | yes | syntax tree; the attribute exposes bodies, much like Roc's rows | no | yes |
| Scala 3 quotes and macros | compile time | full typed trees | can be generic | yes (`inline`) | typed syntax (TASTy) | no | yes: TASTy is a versioned format |
| Typed Template Haskell (`Code m a`) | compile time | typed at the splice | can be generic | no | nothing: typed code is opaque; inspecting it means dropping to untyped TH | not applicable | no |
| Julia typed IR (`code_typed`), CUDA.jl, GPUCompiler | JIT, per call signature | inferred concrete types | yes | yes | SSA after inference and optimization | partly: optimization erases names and helpers | no: the IR is internal and changes between releases |
| Rust GPU backends (rust-gpu, rust-cuda) | compile time | MIR types | yes | yes | MIR, through a codegen backend | partly, as for Julia | no: MIR is unstable, and the `stable_mir` effort is not finished |
| JAX `jit` (jaxpr, StableHLO) | trace time | shapes and dtypes | yes: it retraces per shape | yes | dataflow equations; Python syntax gone, helpers inlined | partly: names and helpers vanish, but equations appear in execution order, so reordering independent lines reorders the jaxpr | StableHLO: yes, with a published multi-year compatibility window |
| PyTorch `torch.compile` / `torch.export` | trace time (bytecode) | tensor metadata, guarded | yes, specialized on shapes | yes | FX graph, with node names taken from source variables | partly | `export`: aiming at it |
| Numba, Triton | JIT | inferred | yes, per signature | yes | internal IR | internal | no |
| Scala LMS / Delite | staging | `Rep[T]` | yes | no: user code is written against `Rep[T]` | a graph with hash-consing and ordering by dependencies | mostly: the graph is canonical by construction | internal |
| Dhall | normalization | System F-like | not needed | not applicable | alpha-beta normal form, hashed | yes, as a guarantee | yes |
| Unison | on save | full types | not needed | yes | name-free, hashed syntax trees | names and moves only | yes, by hash |
| Lean 4 metaprogramming | elaboration | fully elaborated terms | can be generic | yes | `Expr`, with definitional equality decided by normalization | the syntax a metaprogram sees is fragile; equality checks are not | no |
| This design | compile time | Roc's principal types | yes, by rule 4 | yes | the normal form of `roc-reify-normal-form.md` section 2 | yes, for everything in R, tested | intended: the normal form becomes the public API instead of `Code.Ir` |

---

## 2. Where the combination stands out

### 2.1 C# already chose the same trigger, in 2007

A C# lambda becomes an `Expression<T>` exactly when the expected type is an
expression type. That is S1 (`roc-reify-proposal.md`, section 3). So the
ergonomic core has a long-proven precedent.

What C# lacks is the rest. Its trees are built at run time, keep names,
capture closures as references rather than values, and are translated by
their shape. That is why EF Core translations are brittle in the way the
creator's remark describes.

### 2.2 Monomorphization plus type inference beats Julia and Numba

Julia and Numba monomorphize per signature too, but their inference can fail.
Code whose types cannot be inferred to one concrete type, called type-unstable
code, falls back to dynamic dispatch, and on a GPU that becomes a compile
error deep inside an inlined stack.

Roc infers principal types for every expression without annotations, so
specialization always succeeds and always gives the same result. That makes
monomorphization a guarantee rather than a best effort, and `AGENTS.md`'s ban
on fallbacks can only be honored with that guarantee.

### 2.3 Stability means two things, and industry has mostly solved the other one

StableHLO, TASTy and `stable_mir` promise stability across compiler versions:
the format will not change under you. None of them promise that the value
stays the same when the user refactors. The design needs both: R for
refactors, and the normal form as a versioned API (proposal 7.6) for compiler
upgrades.

| Peer | Refactor stability | Why |
|---|---|---|
| JAX | accidental | tracing erases names and helpers, but it records execution order, and nothing documents what it keeps |
| Scala LMS | structural, but only for DSL terms | its sea-of-nodes graph with hash-consing is the closest structural relative of the normal form, and it gets there without reifying ordinary code |
| Dhall, Unison | a guarantee | they normalize for identity and caching, not so that a translator reads the result |

### 2.4 Purity is the prerequisite, and only Roc enforces it

JAX requires pure functions but cannot check purity: a side effect runs once
at trace time and silently disappears. LINQ and F# allow effects, so
reordering and removing dead code would be unsound for them.

Roc's purity is in the type (`Code(a => b)` is ill-formed), so N4 to N6 of the
normal form are valid by construction. Only the order of failures needs C1.

### 2.5 Error locality

In peer systems, an unsupported construct surfaces far from the code that
caused it:

| System | Where the error points |
|---|---|
| Julia GPU | into inlined IR |
| JAX | into the tracing machinery |
| `torch.compile` | nowhere: it silently falls back to eager execution at a graph break |

`refuse_at` plus provenance (`roc-reify-normal-form.md` section 6) reports the
source line, which none of these do by design.

---

## 3. Where the peers are ahead

| Area | Peer advantage |
|---|---|
| Maturity | every system above ships; this design has no implementation, and the confluence of its simplify phase is argued, not proven |
| Control flow that depends on values | tracing unrolls ordinary Python loops for free; here a loop stays a `Loop`, which suits GPUs and SQL but means no free unrolling |
| Optimization | Julia and the Rust backends hand translators fully optimized IR; this normal form deliberately stops at rewrites that preserve meaning, so each translator optimizes for its own target |
| Higher-order code at run time | JAX traces through arbitrary closures; Roc needs every function fixed at compile time (proposal section 10) |
| Crash order | no peer needs a rule like C1, because none of them promises Roc's strict failure order to begin with |

---

## 4. Where this leaves the design

| Combination | Who reaches it |
|---|---|
| typed, monomorphic reification that keeps functions callable | Julia, the Rust GPU backends and LINQ, in part |
| canonical graphs | LMS, but only for DSL terms |
| normal forms with guaranteed invariance | Dhall and Unison, but not for translation |
| all three, for ordinary inferred pure functions | no known system |

Reifying ordinary, inferred, pure functions, monomorphized by rule, into a
representation guaranteed to be identical across a published set of
refactors does not appear to exist anywhere. Roc can offer it because it has
complete type inference, purity enforced by types, and strict semantics whose
one observable ordering can be stated as C1.

---

## Sources

- C# expression trees: [Microsoft Learn, Expression trees](https://learn.microsoft.com/en-us/dotnet/csharp/advanced-topics/expression-trees/)
- F# code quotations: [Microsoft Learn, Code Quotations](https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/code-quotations)
- Scala 3 macros and TASTy: [Scala 3 reference, Macros](https://docs.scala-lang.org/scala3/guides/macros/)
- Typed Template Haskell: [GHC proposal 195, Code type](https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0195-code-texp.rst)
- Julia GPU compilation: [CUDA.jl documentation](https://cuda.juliagpu.org/stable/)
- Rust stable MIR: [Rust project goals, stable MIR](https://github.com/rust-lang/project-stable-mir)
- JAX jaxprs: [JAX documentation, Understanding jaxprs](https://docs.jax.dev/en/latest/jaxpr.html)
- StableHLO compatibility: [openxla/stablehlo, compatibility](https://github.com/openxla/stablehlo/blob/main/docs/compatibility.md)
- PyTorch `torch.export`: [PyTorch documentation, torch.export](https://pytorch.org/docs/stable/export.html)
- Tiark Rompf, Martin Odersky, "Lightweight Modular Staging", GPCE 2010
- Dhall semantic integrity checks: [dhall-lang standard](https://github.com/dhall-lang/dhall-lang/blob/master/standard/README.md)
- Unison: [unison-lang.org, the big idea](https://www.unison-lang.org/docs/the-big-idea/)
