# Reification: whole-design alternatives from other languages

`roc-reify-proposal.md` is one architecture: the compiler describes a checked,
monomorphic function body as a public tag union, `Code.Ir`, and a translator
walks it at build time. `roc-reify-fold-alternative.md` is a second one: the
same body, folded into a type the translator owns. This document sets five more
architectures beside them, each taken whole from a language that solved the same
problem differently, and judges each against Roc.

The problem, stated once: a pure Roc function must reach a consumer that is not
the Roc backend (a GPU, a database, an incremental engine) in a form that
consumer can read. The user-facing shape stays fixed wherever possible: a
function written at, or named at, a typed position.

Status: design sketch. Nothing here is implemented, and the Roc below is written
against proposed APIs.

---

## 1. Where each design taps the program

The designs differ first in which representation of the program the translator
receives. Roc's pipeline already has each of these stages (`design.md:8631`
onward).

```
source
  |
  v
checked module ............ current proposal, fold alternative   (D4 adds a type-level row here)
  |
  v
Monotype IR (design.md:8718)
  |
  v
Lambda Solved (design.md:10674) ... D2: inline to a primitive cut, flatten to a dataflow graph
  |
  v
Lambda Mono (design.md:10843) ..... D1: the translator is a second backend
  |                                  D5: translate to categorical combinators
  v
LIR, ARC, backends
  |
  v
binary ............................ D3: descriptions shipped in the binary, reflected at run time
```

| Design | Inspired by | The translator receives |
|---|---|---|
| Current | C# expression trees, F# reflected definitions | the checked body as `Code.Ir` |
| Fold | tagless final | the checked body, folded into its own type |
| D1 Second backend | Julia GPUCompiler and CUDA.jl, rust-gpu, Clash | a lowered, first-order program |
| D2 Primitive cut | JAX jaxpr, TensorFlow graphs, Halide | a flat dataflow graph over primitives it chose |
| D3 Code is data | Unison, Erlang abstract code, Lisp | a description reflected from any function value, at build or run time |
| D4 Typed boundary | Links, with its query normalization theorem | the checked body, with translatability tracked in function types |
| D5 Categories | Conal Elliott's compiling to categories | a variable-free combinator term |

---

## 2. D1: the translator is a second backend

### Inspiration

CUDA.jl compiles ordinary Julia functions to PTX by running Julia's own compiler
pipeline through type inference and optimization, then handing the typed IR to a
GPU code generator (GPUCompiler.jl) instead of the CPU one. It replaces
functions the GPU needs differently through overlay method tables:
`@device_override` swaps `sin` for the libdevice `sin` only while compiling for
the device. rust-gpu does the same for SPIR-V as a rustc code generation
backend, and Clash compiles Haskell to hardware from GHC Core after its own
normalization.

### The design for Roc

A `Code(f)` site does not describe the checked body. It names `f` as the entry of
a second compilation that runs the ordinary pipeline through Lambda Mono and
stops before LIR and ARC. Lambda Mono is a set of decision tables over the
Lambda Solved lifted syntax, not a stored tree: release builds keep no Lambda
Mono expression tree, and only the debug materializer builds one
(`design.md:10845-10851`, `design.md:11975`). D1 materializes that tree for the
site's procedures and hands the translator a published projection of it:

```roc
Code.Lowered(fn) :: {
	procs : List({ name : Code.ProcId, params : List(Code.Local), body : Code.Stmt }),
	entry : Code.ProcId,
}
```

The program is first order, monomorphic and fully resolved. Every static
dispatch is a direct call to an exact specialization. The Lambda Mono type
store has no function type: a finite callable set is a generated tag union
whose payload is the capture record, and a call of it is a `match` on that tag
(`design.md:10861-10876`). A function value with no finite set is an erased
callable (`design.md:10804`), which has no body to show a translator. The translator supplies overlays, as ordinary Roc,
declared on its type:

```roc
Glsl.overlays = [
	Code.overlay(F32.sin, Glsl.Intrinsic.sin),
	Code.overlay(Glsl.Sampler.texture, Glsl.Intrinsic.texture),
]
```

An overlay replaces the body of the named function in this compilation only, so
the translator meets `Glsl.Intrinsic.sin` as an opaque hosted-like declaration
and emits `sin(...)`.

### What it changes

| Proposal problem | D1's answer |
|---|---|
| The construct cliff (7.5) | none on the Roc side: every pure construct lowers, so a translator refuses only what its target cannot do |
| Exclusion 1: a function value nothing fixes (section 10) | narrowed to erased callables: a finite callable set is a tag plus a `match`, which GLSL emits as `switch` and SQL as `CASE` |
| Captures (rule 3) | a capture of a finite callable set is its tag payload, an explicit record |
| `Ir` versioning (7.6) | moves to the lowered projection, which changes when lowering changes, not when syntax grows |
| Derived methods (`Ir.Derived`) | arrive as ordinary procedures, already expanded |

### What it costs

- Structure thins out. Static dispatch, derived methods and closures are
  resolved, so a SQL translator meets `Str.concat` as a call to an exact
  specialization and a closure call as a `match` on a generated tag. D1 suits targets
  that are themselves low level: PTX, SPIR-V, WebAssembly, C.
- Release builds would have to materialize a tree they deliberately do not
  store, for every site.
- The projection is the compiler's internal program seen from outside, which is
  the second definition of an expression proposal 7.6 warns about. Nim's typed
  macros show the cost of exposing a compiler's internal AST.
- A generated callable tag or capture record has no source region of its own.
- Overlays are a new kind of declaration the checker must validate: the
  replacement must have the replaced function's type.

Fit with `AGENTS.md`: backends must follow explicit `incref` and `decref` only.
D1 stops before ARC, so the translator never sees reference counting and needs
no rule of its own.

---

## 3. D2: a primitive cut and a dataflow graph

### Inspiration

JAX traces a Python function into a jaxpr: a flat, typed list of equations,
each applying one primitive (`add`, `sin`, `dot_general`) to variables, plus a
handful of structured control primitives (`cond`, `while`, `scan`). Every
transformation JAX offers (`grad`, `vmap`, `jit`) is an interpreter over jaxprs
that returns a jaxpr, which is why they compose: `jit(vmap(grad(f)))`. Structured
arguments (pytrees) are flattened to leaves with a separate shape descriptor.
Halide and TensorFlow graphs make the same cut: a small set of operations, and
everything above them compiled away.

### The design for Roc

The vocabulary of the description is not Roc's syntax but a set of functions
the translator names: its primitive cut. The compiler inlines every pure
function outside the cut, transitively, until only primitives and a fixed set of
structured control nodes remain, and flattens records and tuples into leaves.

```roc
Glsl.cut : Code.Cut
Glsl.cut = Code.Cut.of([
	F32.plus, F32.times, F32.sin, F32.is_lt,
	Glsl.Vec2.make, Glsl.Sampler.texture,
])

Code.Graph := {
	inputs : List(Code.Leaf),
	eqns : List({ outs : List(Code.Var), op : Code.Op, args : List(Code.Atom) }),
	outputs : List(Code.Atom),
}

Code.Op := [
	Prim(Code.PrimId),                                # a function in the cut
	Cond(Code.Graph, Code.Graph),                     # structured control, owned by the language
	Switch(List(Code.Graph)),
	Fold({ body : Code.Graph, carried : U64 }),
	While({ cond : Code.Graph, body : Code.Graph }),
]
```

`Code.Cut.of` takes function references, not strings, so a misspelled primitive
is a compile error in the translator. The graph for `post_process` in
`examples/reifying/glsl/main.roc` is about twenty equations, and each one is a
GLSL expression.

Transformations become ordinary Roc libraries, `Code.Graph -> Code.Graph`,
because the graph is small and uniform:

```roc
Ad.jvp : Code.Graph, Ad.Rules -> Code.Graph      # forward-mode derivative
Batch.vmap : Code.Graph, U64 -> Code.Graph       # the same kernel over a batch
```

### What it changes

| Proposal problem | D2's answer |
|---|---|
| `Ir` versioning (7.6) | the language owns five control nodes; every other operation is a function a library named, so the vocabulary grows in libraries |
| Section 12: symbolic differentiation waits on splice | a derivative is a graph transformation written in Roc; running the result on the CPU still needs an evaluator over graphs |
| 7.7: it looks like Roc and does not mean Roc | a primitive is an explicit function reference, so the translator states exactly which Roc operations it reinterprets |
| What a translator writes | one case per primitive plus five control nodes, instead of one case per construct |

### What it costs

- Recursion cannot be inlined. A recursive function must be in the cut or the
  site is refused, which excludes tree-shaped algorithms.
- Function boundaries are gone, so a GLSL helper function or a SQL
  user-defined function cannot be emitted as one. Code size grows with inlining.
- Tag unions have no leaf form. They flatten to a discriminant plus padded
  payload leaves, which suits GLSL and CUDA and is foreign to SQL.
- The cut is a compile-time constant the checker must read before it can
  describe the site, so the order of checking gains a dependency.

Fit with `AGENTS.md`: the cut is explicit data the translator declares, and
inlining consumes the resolved calls the checker recorded. Purity makes inlining
exact.

---

## 4. D3: code is data at run time

### Inspiration

Unison stores every definition by the hash of its syntax tree, and a running
program can serialize any function value, including a closure, and send it to
another node, which fetches the missing definitions by hash. Erlang keeps the
abstract code of a module in its compiled BEAM file, and Lisp never separated
code from data. None of them decides at a typed position whether a function is
data: every function is, whenever someone asks.

### The design for Roc

There is no `Code(f)` slot rule. One builtin reflects any pure function value:

```roc
Code.reflect : (a -> b) -> Code(a -> b)
```

It is total over pure functions. A statically known function reflects to its
description. A closure reflects to its lambda-set tag and its captured values,
because Roc already represents a closure as exactly that. The binary carries
content-addressed descriptions of every function reachable from a `reflect`
call.

Build time is not a separate mechanism. When the argument is fixed at build
time, the compile-time evaluator folds `Code.reflect` and the translator's call
like any other constant, so a query that is a top-level constant is translated
and refused during `roc build`:

```roc
adults : Sql.Query(User)
adults = Sql.table("users").where(Code.reflect(eligible))    # translated at build time

over : U32 -> Sql.Query(User)
over = |min_age| Sql.table("users").where(Code.reflect(|u| u.age >= min_age))
# translated at run time; `min_age` arrives as a captured value, so SQL gets a parameter
```

### What it changes

| Proposal rule | D3 |
|---|---|
| Rule 3, closed | dropped: a capture is data in the closure |
| Rule 7, build time only | dropped: build time when the argument is constant, run time otherwise |
| Exclusion 1 | dropped: a function chosen at run time reflects to its tag |
| Exclusion 3: a `Code` not fixed at build time | dropped |

### What it costs

- A refusal of a non-constant site is a run-time error. That is the Entity
  Framework failure proposal 7.5 counts this design's main advantage over, and
  D3 brings it back.
- Binary size grows with every reachable description, and translation at run
  time costs latency on first use.
- The user writes `Code.reflect`, so the call site stops looking like an
  ordinary call. The type-directed spelling could remain as sugar for it.
- The compile-time evaluator must be able to fold `reflect`, which ties
  build-time translation to how far constant evaluation reaches: an optimization
  boundary becomes a semantic one.

Fit with `AGENTS.md`: lambda sets and captures are explicit data. The risk is
the last cost above: whether a site is translated at build time must be decided
by an explicit rule, not by whatever the evaluator happens to fold.

---

## 5. D4: translatability tracked in the type

### Inspiration

Links integrates database queries into a general-purpose language, and its
effect system tracks whether a function can run in the database: a function
that could not is marked `wild` in its type. Cheney, Lindley and Wadler then
proved that every quoted query of flat relation type normalizes to one SQL
query. Together the two give Links a boundary that is known at the definition
and a guarantee stated by type.

### The design for Roc

Every pure function type carries an inferred row of what its body uses beyond
the core, the way `=>` records effects today: `User -[str_ops]-> Bool`. The
core is what every translator is assumed to handle: arithmetic, comparison,
records, `if`. A translator's signature names the row it admits:

```roc
where : Table(row), Code(row -[]-> Bool) -> Query(row)    # the core only
```

Passing a function whose inferred row contains `lists` is an ordinary type
error, reported at the definition that introduced the construct. A normalization
pass, stated as a theorem in the Links manner, guarantees that a function of
admitted row and flat type always translates.

### What it changes

The boundary lives in the type system, where the DSL puts it (proposal 7.1,
the counterweight) and where the reader of a signature can see it.

### What it costs

- A new dimension on every function type, which is what proposal 7.3 rejected
  for effect rows.
- Roc's purity is syntactic and not polymorphic. A higher-order function such as
  `List.map` would need row polymorphism over its argument's row, which Roc does
  not have for effects either.
- The core is a language decision made once for all translators, which is the
  `Ir` versioning problem moved into the type system.

---

## 6. D5: a variable-free description

### Inspiration

Conal Elliott's compiling to categories is a GHC plugin that rewrites any
ordinary Haskell function, from GHC Core, into morphisms of a cartesian closed
category the consumer chooses. One program, many interpretations: circuits, a
subset of C, automatic differentiation, interval analysis.

### The design for Roc

The compiler translates the Lambda Mono program of the site into a term over a
fixed set of combinators: `id`, `compose`, `fork` and projections for products,
`case` and injections for sums, a fixpoint for recursion, and a primitive
morphism per builtin operation. A translator implements the combinators on its
own type through static dispatch, as a monotype because Roc has no higher-kinded
types.

### What it changes

The vocabulary is mathematically closed. It never grows with the language,
because every future construct compiles into the same dozen combinators, which
removes proposal 7.6 permanently. Without variables, alpha-equivalence
(rule 6) is syntactic equality.

### What it costs

- A translator for SQL or GLSL wants named bindings and structured control, and
  must reconstruct both from point-free terms.
- Point-free terms grow quickly with the number of variables in scope.
- Without higher-kinded types the combinators lose their types, and with them
  most of what makes the categorical view checkable.

---

## 7. Considered and set aside

| Design | From | Why not |
|---|---|---|
| Two-level staging: users write `Rep` types, quotes and splices | MetaOCaml, Terra, AnyDSL, Mojo | changes the user-facing shape, which this document keeps fixed; also the two-level language proposal section 12 declines |
| Multitier placement types: a value's type says which tier it runs on, and the compiler splits the program | ScalaLoci, Eliom, Hop, Links | the compiler would own the split and every tier's backend; in Roc the platform already is the tier boundary |
| Effect handlers reinterpret the body | Koka, Effekt, Eff | Roc has no handlers, and its effects belong to the platform |
| A first-class declarative sublanguage | Flix first-class Datalog | serves the DBSP motivation only, and is a second language beside Roc |

---

## 8. Comparison

| | Vocabulary owned by | Grows when Roc grows | Refusal appears | Captures, runtime functions | Keeps structure for SQL | Transformations such as AD | New compiler surface |
|---|---|---|---|---|---|---|---|
| Current | compiler, `Code.Ir` | yes | build time, in `from_code` | refused | yes | data only | reifier over the checked body |
| Fold | translator | only by new method names | check time, footprint | refused | yes | data only | footprint check, residual program |
| D1 Second backend | compiler, lowered projection | when lowering changes | build time | finite callable sets yes, erased callables no | partly | on low-level code | a materialized Lambda Mono projection, overlays |
| D2 Primitive cut | translator, the cut | five control nodes only | build time | refused | partly | yes, graph to graph | inliner to a cut, flattener |
| D3 Code is data | compiler | yes | build time if constant, else run time | both yes | yes | data only | descriptions in the binary |
| D4 Typed boundary | compiler, the core row | yes, in types | check time, at the definition | refused | yes | data only | a row on every function type |
| D5 Categories | fixed combinators | no | build time | functions yes | no | yes | categorical translation |

---

## 9. Conclusion: the stage is the open dimension

Each design picks one point of the pipeline and gives every translator the
program as it looks there. The translators disagree about which point they want:

| Target | Wants | Best served by |
|---|---|---|
| SQL, DBSP, Datalog | `and`, `match`, records, named bindings | the checked body: current proposal or fold |
| GLSL, CUDA, compute kernels, AD | flat numerics, fused operations, derivatives | the primitive graph: D2 |
| PTX, SPIR-V, WebAssembly, C | everything resolved, with closures as tags | the lowered program: D1 |

This points to a design none of the source languages has: `Code` carries its
stage as a type parameter, and the translator's signature picks one:

```roc
where : Table(row), Code.Checked(row -> Bool) -> Query(row)
fragment_330 : Code.Graph(Varyings, Uniforms -> Vec4, Glsl.cut) -> Str
kernel : Code.Lowered({ a : F32, x : F32, y : F32 } -> F32) -> Cuda.Ptx
```

The user writes the same function at the same kind of position in all three.
The checked body exists today, and the Lambda Mono tree exists in debug builds;
the primitive graph of D2 is new. The cost is three public representations
instead of one, each with its own versioning obligation. The ordering by value is D2 first, because it serves the
use cases proposal section 5 lists as needing no DSL at all (shaders and
kernels), and D1 second, because it is the only design that narrows exclusion 1 to
erased callables without shipping descriptions into the binary.

---

## Sources

- JAX: [Autodidax, JAX core from scratch](https://jax.readthedocs.io/en/latest/autodidax.html), [jaxpr reference](https://jax.readthedocs.io/en/latest/jaxpr.html)
- CUDA.jl and GPUCompiler.jl: [GPUCompiler.jl](https://github.com/JuliaGPU/GPUCompiler.jl), [CUDA.jl overrides](https://cuda.juliagpu.org/stable/)
- rust-gpu: [rust-gpu](https://github.com/Rust-GPU/rust-gpu)
- Clash: [clash-lang.org](https://clash-lang.org/)
- Unison: [The big idea](https://www.unison-lang.org/docs/the-big-idea/)
- Links: [A practical theory of language-integrated query](https://homepages.inf.ed.ac.uk/slindley/papers/practical-theory-of-linq.pdf), [Row-based effect types for database integration](https://homepages.inf.ed.ac.uk/slindley/papers/corelinks.pdf)
- Compiling to categories: [paper](http://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf)
- ScalaLoci: [scala-loci.github.io](https://scala-loci.github.io/)
