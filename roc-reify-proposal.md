# Reified code in Roc

A proposal for one new kind of value: a pure Roc expression reified into data
instead of compiled into machine code. It lets an external compiler consume Roc
as a specification, which is what makes GPU kernels, shaders, incremental
computation and other DSL-like use cases expressible as libraries rather than as
compiler features.

Status: design sketch, with a working prototype on the `reify` branch. Semantics
and syntax come first; the deep material is sections 9 onward.

---

## 1. Summary

Roc's platform architecture answers one question about a program:

> Where and how do my effects execute?

Nothing in Roc answers the neighbouring question:

> Where and how does this pure computation execute?

Today the answer is always "here, as machine code the Roc backend emitted". A
shader, a GPU kernel, a database predicate and an incremental view each need a
different answer, and the obstacle is neither the type system nor the effect
system. It is that a Roc function reaches any other consumer as a function
pointer, which cannot be inspected, translated or fused.

The proposal is one type and one rule.

| | |
|---|---|
| `Code(a)` | A pure Roc expression of type `a`, as data |
| The rule | A function-typed expression in a position expecting `Code(...)` is reified rather than compiled |

The position is a parameter. Any function that takes a `Code(f)` receives a
description of whatever function its caller passes, so there is no hook method
and no registration: declaring the parameter is the whole interface.

Everything else is a library. The compiler learns the word reification and never
learns the words shader, kernel, SQL or Z-set.

A translator is the consumer of `Code(a)`: a function written in pure Roc that
takes one, run at build time, and turns it into data. It has no runtime and no capabilities.
Section 4 defines it; section 11 covers where its output executes.

---

## 2. Naming

The source discussions called this staging, after multi-stage programming, and
typed quotation, after MetaOCaml. Both names were dropped.

Staging collides with CI environments, with the git index, with compiler
pipeline phases (`src/lir/` already uses the word that way), and with multi-stage
programming itself, where a stage is a time rather than a component. The feature
is not multi-stage programming in any case, having neither splice nor `run`.

Quotation is already taken: `from_quote` is the well-known method a type defines
to accept a string literal.

| Concept | Name | Reasoning |
|---|---|---|
| The value | `Code(a)` | MetaOCaml `code`, Scala 3 `Expr[T]`, C# `Expression<T>`. Short in signatures |
| The act | reification | Turning a computation into data the program can read |
| The consumer | a translator | A compiler, in pure Roc, run at build time |
| The IR | `Code.Ir` | A plain Roc tag union |

There is deliberately no noun for the module that holds a translator. Naming the
role would imply a new kind of module, and a translator is an ordinary package.

---

## 3. Syntax

### Semantics of `Code(a)`

1. **Typed.** `Code(Person -> Bool)` holds only expressions of that type. A type
   error inside one is an ordinary Roc type error at the ordinary place with the
   ordinary message. This is the whole advantage over string-carrying DSLs.
2. **Pure only.** `Code(a => b)` is ill-formed. An effectful lambda in a reified
   position is a type error, and existing purity inference produces it for free.
3. **Closed.** A description carries no scope, so everything a body reads from
   outside itself is written into the description. Besides its parameters and
   its own bindings, a body may read:
   - a top-level value written out as data: a literal, or a record, tuple,
     list, tag or nominal built from literals, in this module or one it
     imports. `limit = 7.0` read as `x > limit` describes as `x > 7.0`.
   - a value the surrounding block binds, when the lambda is written at the
     `Code` position inside that block. The binding is repeated at the head of
     the lambda's body, so it describes as a `Let`.
   - a named function, which describes as a call, with the callee's own
     description in a table beside the root (section 4).

   What it cannot read is a value that exists only once the program runs: a
   function parameter, a branch or loop binder, a `var`. That is timing rather
   than purity: the description is built before any such value exists, so a
   captured one could only arrive as an opaque pointer, which is what this
   feature exists to avoid. A top-level value that has to be computed,
   `limit = xs.len()`, is refused the same way for now, because the compiler
   evaluates it after the description is built. The refusal names the value.
   Section 13 carries what is left of this.

   A template goes further: a function returning `Code` whose arguments are
   fixed at the call and written into the body it returns. An argument can be
   a literal, a name bound to one, an aggregate of those, or a function.
4. **Monomorphic.** Each site is described at the types it fixes. A generic
   function named at `Code(Str -> U16)` is described with its type variables
   at those types, a generic function the body calls is described once per
   instantiation, and a polymorphic template yields its own concrete
   description at each call.
5. **Inert.** There is no `run : Code(a) -> a`. A `Code` value is data, not a
   thunk, and cannot be called. Section 12 covers what that costs.
6. **Structural.** `Code` derives `is_eq` and `to_hash` over an alpha-equivalent
   normal form, which gives translators common-subexpression detection and a
   stable cache key for compiled artifacts for free. The prototype does not
   have this yet: neither `Code` nor `Code.Ir` has an `is_eq`, and names are
   kept as the author wrote them.
7. **Compile-time constructible only.** No runtime constructor. With rule 3,
   every `Code` value in a program is fully determined at build time.
8. **Roc reifies; the translator validates.** The compiler never asks whether an
   expression is lowerable. It guarantees only that it is well-typed, pure,
   closed and monomorphic, in a stable representation. Whether a GPU can run
   `Str.split_on` is the GPU translator's business, answered in its own Roc.

Those eight give the boundary its one rule: a body describes when everything it
names is fixed by the time checking ends. Section 10 states what that excludes,
which is three things and not a chosen subset of the grammar.

### S1. Type-directed reification

No new grammar. A function-typed expression whose expected type is a reified
type is reified rather than compiled.

```roc
crt : Shader.Spirv
crt = Shader.compile(|uv| shade(uv))

# because the signature says so:
Shader.compile : Code(Vec2 -> Vec4) -> Shader.Spirv
```

This is `from_numeral` applied to lambdas. It is also how C# expression trees
work: `Func<Person,bool> f = p => p.Age >= 18` compiles a delegate and
`Expression<Func<Person,bool>> e = p => p.Age >= 18` builds an inspectable tree
from identical source text. That design is what made LINQ-to-SQL work.

The rule must extend past literals to named references, or the biggest win is
lost:

```roc
is_eligible : User -> Bool                      # ordinary Roc, ordinary tests
is_eligible = |u| u.age >= 18 and u.country != Banned

query = users.where(is_eligible)                # reified at this call site
```

Precisely: an expression of function type in a position expecting `Code(...)` is
reified, provided the compiler can read its body. These qualify:

- a top-level function of this module or of one it imports, including one
  declared on a type (`Maker := {}.{ ... }`)
- a function bound inside a block, named where the `Code` is expected
- a lambda written at the position itself, at the top level or inside a
  function body

A function received as a runtime argument does not qualify, and neither does
one chosen by an `if` or read out of a record. Those are the error cases, with
a message that says so.

A `Code(...)` itself appears in exactly two places: a function parameter, which
takes a description, and a function's return type, which makes that function a
template.

The cost is invisibility: nothing at the call site distinguishes a reified
lambda from a compiled one. What takes the sting out is that the signature is
one hop away, the failure mode is a compile error rather than a silent change of
meaning, and Roc already accepted the same trade for `temp : Celsius = 21`.

### S2. Explicit construction

Roc spells explicit nominal construction `Distance.(26)` and `Pair.(1, "two")`,
for when no expected type drives the conversion. The same form could cover
code:

```roc
pred = Code.(|p| p.age >= 18)
same = Code.(is_eligible)
```

The prototype refuses it. `Code` is opaque, so user code cannot construct one,
and that is also what stops a hand-built `Code` from posing as a description
the compiler wrote. Admitting `Code.(f)` for a function would give S1 a spelling
that is visible at the call site; nothing so far has needed one, because the
signature one hop away already says it.

### S3. Annotate the definition

```roc
is_adult : Code(Person -> Bool)
is_adult = |p| p.age >= 18
```

The prototype refuses this too, by the placement rule above: a value annotated
`Code` would be a description that outlives the compiler, and a `Code` exists
only while the compiler runs. What S3 was for, a package shipping reusable
reified functions, needs no form of its own. The package ships `is_adult` as an
ordinary function, callers name it wherever a `Code` is expected, and it stays
callable and testable in the package's own `expect`s.

So the prototype has one form, and the other two are recorded because they are
the ones a reader reaches for first. Section 12 records two more that were
considered and dropped.

| Option | New grammar | Visible at call site | Retrofits existing functions | Precedent in Roc | Prototype |
|---|---|---|---|---|---|
| S1 type-directed | none | no | yes | `from_numeral` | yes |
| S2 `Code.(…)` | none | yes | yes | `Distance.(26)` | refused: `Code` is opaque |
| S3 annotation | none | at definition | no | value annotations | refused: a `Code` names a parameter or a result |

---

## 4. The translators

This is the load-bearing definition. Getting it wrong makes the proposal much
larger than it needs to be.

> A translator is a compiler, not a runtime. It is ordinary pure Roc, it runs
> during `roc build`, and it produces data.

Four consequences follow:

- It is an ordinary package. No new module kind, no native code, no capability
  declaration, no link step.
- It extends nobody's trust boundary. Roc's guarantee that all native code
  arrives through the platform is untouched.
- Roc's build stays hermetic. The langref is explicit that the compiler runs no
  platform-provided low-level code during compilation, so `roc check` and `roc
  build` cannot perform I/O, and a pure-Roc translator keeps that true.
- Its output is a top-level Roc value, which Roc already evaluates at compile
  time, so it is already a constant in the binary. No emission pass, no artifact
  format, no build-system plumbing.

A translator is any function with a `Code(f)` parameter. The caller passes an
ordinary function, the compiler hands the translator its description, and a
top-level value that calls the translator runs during `roc build` like any
other.

```roc
Kernel := { ptx : Str }.{
	compile : Code(f) -> Try(Kernel, [BadCode(Str)])
	compile = |code| match code.ir().find_unsupported() {
		Ok(node) => Err(BadCode(
			"this GPU translator cannot lower ${node}. Arithmetic, comparison,
			 field access, tags and match are supported; heap allocation
			 is not."
		))
		Err(NotFound) => Ok(Kernel.lower(code))
	}
}

job = Kernel.compile(saxpy)
```

This is the move the proposal turns on. The compiler learns one concept, and
every diagnostic a user ever sees about what a GPU, a query planner or an
incremental engine accepts is written in Roc by the author of that translator.

A refusal is an ordinary `Err`, and the program decides what to do with it.
`examples/reifying/glsl/main.roc` matches on the result; a `crash` on the `Err`
is reported as a compile-time crash at the call. Section 13 asks whether an
`Err` should reach the user as a compiler diagnostic instead.

`Code.ir : Code(a) -> Ir` exposes the expression as a plain nominal tag union so
a translator can walk it. A `Lambda` at the root, then `Param`, `Local`, `Let`,
`Lit`, `Binop`, `Unary`, `Call`, `Field`, `OptField`, `Index`, `Range`,
`MakeRecord`, `MakeTuple`, `MakeList`, `MakeTag`, `If`, `Match`, `For`,
`While`, `Break`, `Return`, `Crash` and `Derived`: 24 nodes. Every node carries
its type and its source region, so a translator can both decide what a call
means in its target and point at the line that produced it.

A call to another function names it, and `Code.definitions` holds the
description of every function the root reaches, in this module or any other,
one row per instantiation. A translator resolves a `Call` against that table
and so keeps the structure the author wrote, recursion included.

`Derived` is the one that needs a word here. A compiler-derived method such as
`parser_for` has no Roc body to describe, so the node names the method and the
type it derives over and stops. A translator that owns the target format expands
it in its own language; every other translator refuses it by name.

The real cost of the feature is that `Ir` becomes a public API with a versioning
obligation. Section 7.6 argues that the right answer is to stabilize it on the
boundary of section 10, which is all of pure Roc the compiler has fixed, rather
than to track the language.

---

## 5. Uses

In each of these, an ordinary Roc function is the natural way to say what the
computation is, and the computation cannot run as Roc machine code.

| Use | Why not another language feature |
|---|---|
| Fragment and vertex shaders | The GPU runs SPIR-V or GLSL. A Roc function pointer is not either, and a string of GLSL is a second language with no type checking |
| GPU compute kernels | Same, plus the kernel body is exactly the kind of small numeric function worth unit-testing on the CPU first |
| Query pushdown to a database | The predicate must reach the server as SQL. An ORM expression builder is the standard answer, and it is a query language the application author has to learn per library |
| Incremental view maintenance | An engine such as DBSP keeps a query's answer current under change. It needs the query, not a callback it cannot see into |
| Regex to a DFA table, schema to a codec, protocol to a state machine | The output is a build-time table. Writing it by hand or generating it from a separate file both leave the specification outside the language |
| Symbolic work: differentiation, algebraic simplification | The consumer needs the expression's structure, not its value at a point |

The library-only alternative in every row is a DSL: a symbolic type whose
operators build an AST. Roc supports more of that pattern than most languages
do, and section 7.1 works through how much. The short version is that a Roc DSL
gets operators, literals, bindings and type safety, and loses two things that
matter: record field access, which is syntax rather than a method, and the
ability for one definition to stay an ordinary function that ordinary code can
call and `expect` can test.

Section 14 works three of these through against real APIs.

---

## 6. Why the design is a good fit for Roc

**It adds no syntax.** S1 is the grammar Roc already has. The
compiler gains types and a rule about where they apply, not a new way to write a
function. Roc documents having exactly one syntax for defining a function, and
this proposal keeps that true.

**It is the pure-computation half of the platform idea.** Roc's central
architectural move is to take a question everyone else answers in the language,
"where do my effects run", and answer it outside the language, in a platform
chosen per application. Reification takes the neighbouring question and answers
it the same way: outside the language, in a translator chosen per use. A
platform knows about sockets and the compiler does not; a translator knows about
SPIR-V and the compiler does not.

**It keeps the trust boundary exactly where it is.** A translator is pure Roc
with no capabilities. Nothing about "all native code arrives through the
platform" changes, and the hermetic build survives.

**It reuses the type-directed conversion Roc already chose.** `from_numeral`,
`from_quote` and `from_interpolation` already mean that a literal becomes
whatever the expected type says, with errors at compile time. A `Code(f)`
parameter extends that to one more kind of literal, the lambda.

**It trades implementation complexity for usage simplicity, which is the trade
Roc keeps making.** Static dispatch instead of type classes, one number tower
instead of a numeric hierarchy, derivation instead of boilerplate, platforms
instead of a standard library of effects: each spends work inside the compiler
to reduce what a user has to hold in their head. Reification goes the same way.
Section 7.4 does the accounting, because the first-glance reading of "minimal"
points the other way.

**Most of the machinery already ships.** Compile-time evaluation of top-level
values, literal conversion hooks, syntactic purity tracking and a checker that
records every solved type and every resolved method call are each doing the job reification needs, for reasons that predate it. Section 9
counts what is left over.

---

## 7. Considerations on obvious criticisms of the design

The proposal reads as redundant on first glance, and the redundancy is real
rather than imagined. This section states each objection at its strongest before
answering it.

### 7.1 Static dispatch already lets you build a DSL

Correct, and Roc makes that DSL unusually good. Several of the standard
arguments for quotation simply fail here.

Arithmetic dispatches to methods on the receiver and keeps the receiver's type,
so `+` can be made symbolic, and `from_numeral` lets a bare literal join in:

```roc
Sym := [Lit(I64), Col(Str), Plus(Sym, Sym), Gte(Sym, Sym)].{
	from_numeral : Numeral -> Try(Sym, [InvalidNumeral(Str)])
	from_numeral = |n| match I64.from_numeral(n) {
		Ok(i) => Ok(Sym.Lit(i))
		Err(e) => Err(e)
	}

	plus : Sym, Sym -> Sym
	plus = |a, b| Sym.Plus(a, b)
}

age : Sym
age = Sym.Col("age")

sum : Sym
sum = age + 1    # works: `+` dispatches to `plus` and returns Sym
```

So a Roc DSL gets infix arithmetic, numeric and string literals, ordinary `x =`
bindings whose right-hand side is symbolic, method-call syntax, and full type
safety. That is closer to natural code than Diesel, SQLAlchemy or jOOQ manage.

Five gaps remain. The cheapest thing that would close any of them is a derivable
lift of a record's fields into a type constructor, so that `Order` yields
`{ amount : Sym, customer : Sym, … }`: the structural walk the compiler already
performs for derived codecs, pointed at a different target. No new IR, no public
API, no capture analysis, no subset boundary. It is genuinely cheaper than this
proposal, and it closes one row of the five.

| Gap | Why | Would the field lift fix it? |
|---|---|---|
| Record field access | `p.age` is syntax, not a method, so a DSL needs one accessor per field, written and maintained by hand for every type | Yes. That is exactly its job |
| Comparison syntax | `>=` dispatches, but its result type is fixed to `Bool` whatever the method declares | No. Only a change to what `>=` desugars to would, and that reaches every existing use of `is_lt` and its siblings |
| `and`, `or` | Short-circuiting keywords the compiler turns into `if`, with no method hook | No. A DSL keeps a combinator and loses the syntax |
| `if`, `match` syntax | Both need a real `Bool` and a real scrutinee. Accelerate answers this in Haskell with a separate `(?)` operator, and the ergonomic damage is well documented | No, same combinator, same loss |
| Reuse | A DSL predicate is a value of type `Sym`, so it cannot be called on a real `Person`, tested with `expect`, or used as a reference implementation | No, and neither would anything else. Nothing turns a `Sym` into an `Order -> Bool` |

The comparison wall, against the 2026 nightly:

```
── ✗ type mismatch ─ sym.roc:24:8

This expression is used in an unexpected way.

pred = age >= 18
       ^^^^^^^^^

It has the type:

    Bool

But the annotation says it should be:

    Sym
```

So the ceiling for a pure library is:

```roc
p.age().gte(18).and(p.active())      # the library-only ceiling
```

instead of:

```roc
|p| p.age >= 18 and p.active         # ordinary Roc
```

So if the goal is a clean DSL UX the choice is not one small feature against one
large one. It is one small feature, plus a change to operator desugaring with its
own blast radius. Even with both, `and`, `or`, `if` and `match` still cannot be
used inside a DSL expression, so every branch and every conjunction is written as
a combinator call. And the result is still a predicate that is not a function.

That last row is where the proposal rests. `is_eligible` written as ordinary Roc
is callable on a real `User`, testable with `expect`, usable outside any query,
and usable as the reference implementation a translator's output can be checked
against. Written as a `Sym` it is none of those, and the workaround is to write
the rule twice, symbolically and as a function, with nothing checking that the
two agree. Two definitions drifting silently is the failure this proposal exists
to prevent, and that is not an ergonomics argument.

**The counterweight, which cuts the other way.** A DSL puts its boundary
in the type system. You cannot write an expression the backend will reject,
because the type will not let you, and you learn the boundary while writing
rather than at build time. Reification inverts that: you write ordinary Roc and
find out later that a translator refuses it. That is the strongest argument
against this proposal, and section 7.5 is the answer it deserves.

### 7.2 So the reifier is a built-in, limited Roc parser?

No, and the distinction decides how much of the language the feature has to keep
up with. The reifier runs after canonicalization and type checking, on the
checked body, so it never sees syntax. It sees elaborated, type-annotated
semantics, specialized to the types each site fixes, which is why `and` arrives as an `if`, why `21` arrives
with the type it was solved to, and why a polymorphic function arrives once per
instantiation.

The related worry is that this is macros under another name, and Roc excluded
macros on purpose.

| | A macro | Reification |
|---|---|---|
| Consumes | syntax, before it means anything | a checked, monomorphic, pure body |
| Produces | syntax | a value |
| Can change what the program means | yes | no |
| The original code still runs | not necessarily | always |
| Needs hygiene | yes | no |
| Reader must know it happened to read the code | yes | no |

Reification is observation, not transformation. A reified function still
compiles, still runs, still tests. That is why it is not what Roc excluded when
it excluded macros, and why getting it wrong costs a build error rather than a
program that quietly means something else.

### 7.3 Why not a different mechanism

**Monads.** They structure composition, not representation. A monadic builder
still ends up holding an opaque host function, which is the actual problem. Roc
also has no higher-kinded polymorphism by design, so the reusable abstraction
cannot be written anyway. A free monad has the same defect: `Filter(Person ->
Bool)` still contains a function pointer; what is wanted is
`Filter(Code(Person -> Bool))`.

**Effect rows.** Inspired by Koka, where a function's type carries a row of the
effects its body performs, `int -> <exn,div> int`, and by CUDA's `__device__`
and `__global__`, which qualify a function with the processor it is compiled
for. The syntax: let the row name a target rather than an
effect, so that `a -[GPU]-> b` says compile this body for the GPU.

New type-level syntax, like the monad above. What the row buys is the question,
and the answer is nothing a potential translator can use. A row says where a
function runs; a translator needs what the function says, as data. The compiler
would still have to own the GPU backend, which section 12 rules out.

The label is also wrong in both directions. A shader affects nothing, so
`-[GPU]->` claims an effect that is not there, while `!` already means
"observably affects the world", so widening that channel to also mean "executes
elsewhere" costs Roc the distinction it has. `Code(a)` is a type of value, so it
needs no effect system change and no kind system change.

**Tracing**, which is how JAX, PyTorch and Nx solve this problem: run the
function on symbolic values and record what it does. Closed to Roc, and not by
choice. Tracing needs a value that is dynamically symbolic while statically
passing for the real type, and Roc is statically typed and monomorphic, so
`is_eligible` takes a concrete `User` of concrete scalars and there is no
symbolic `U8` to hand it.

The general shape is worth stating, because it shows the design is not an
arbitrary addition:

| Language shape | Mechanism available | Examples |
|---|---|---|
| Dynamically typed | tracing | JAX, PyTorch, Nx |
| Syntactic macros | rewrite the definition before it means anything | Lisp, Template Haskell, Elixir `defn` |
| Statically typed, no macros | reify the checked body, or build a DSL | C#, F#, Roc |

Roc sits in the third row because of two decisions it already made, and that row
has two entries. This proposal is one; section 7.1 is an honest account of the
other.

**A compiler that knows the domains.** First-party lowering for each target is
neither general nor realistic, and it puts every diagnostic in the compiler
instead of in the library that understands the domain.

### 7.4 This is not minimal

Counted in language concepts the objection is correct, so here is the count.

| Counted in | The DSL path | Reification |
|---|---|---|
| Concepts added to the language | one derivation, at most | `Code(a)`, public `Code.Ir` and `Code.Ty`, a placement rule, a compile-time trigger, a boundary rule with its own diagnostics |
| What one library author writes | a query language | a translator |
| What every application author learns | one query language per library | Roc |

The ordering reverses between the first row and the third, and which row counts
is the whole disagreement.

Roc's "powerful but minimal" has consistently meant what the third row names.
Static dispatch instead of type classes: more compiler, less for a user to learn.
One number tower instead of a numeric hierarchy: more solver, fewer annotations.
Derivation instead of boilerplate for the parsers: more machinery, less code
in front of a reader. Platforms instead of a standard library of effects: a whole
architectural layer, so that a program's effects are described in one place a
user chooses.

Each spends implementation complexity to reduce what a user holds in their head,
and reification goes the same way. The feature is not small. It is small in the
dimension Roc optimizes: the mental model a user carries while writing code.

Section 9 is the evidence that the first row is smaller than it looks. The
prototype's reifier is a single cohesive module the rest of the compiler does
not depend on, and deleting it is mechanical work.

### 7.5 The language subset cliff is permanent

Half correct, and the half that is wrong is the half that decides the feature.

C# is the cautionary tale. It shipped expression trees in 2007, and twenty years
later a statement-bodied lambda, `await`, `ref` and `out` parameters are still
not convertible; "an expression tree may not contain…" is still a compiler error
people meet; and Entity Framework's "could not be translated" is still a runtime
surprise. The cliff never went away.

What makes that cliff hurt is that it is arbitrary. A statement-bodied lambda is
perfectly determinate, and C# excludes it because the 2007 implementation did
not cover it. A boundary that is a list of what one release happened to support
cannot be learned, only bumped into, and every release moves it.

This design's boundary is a rule, and section 10 states it in a sentence: a body
describes when everything it names is fixed by the time checking ends. Its three
exclusions are that one rule applied rather than three decisions, so an author
who knows the rule predicts every refusal without consulting a table, and the
boundary does not move as Roc grows. It is a cliff, and it is permanent, and it
stands where a reader would have drawn it.

LINQ is also one of the most successful language features ever shipped, and its
arbitrary cliff did not stop it. The lesson is not that a cliff is acceptable,
but that where it lands and how a user learns about it is the feature's entire
user experience. Two consequences follow:

- Refusal diagnostics are the feature, not its error handling. A translator
  returning `Err` is the primary interface a user meets, and should be budgeted
  and reviewed accordingly.
- Entity Framework's failure is the worse one, because it happens at run time.
  This design cannot repeat it: a translator runs during `roc build`, so a
  refusal happens before the program exists, by construction.

### 7.6 `Code.Ir` becomes public API, forever

This is the decision that actually matters, and it is larger than the choice
between a DSL and a reifier.

If `Ir` tracks the language, then every future Roc feature becomes a two-place
change forever, and Roc acquires a second definition of what an expression is,
which will drift.

If `Ir` stabilizes on the boundary of section 10, it covers all of pure Roc the
compiler has fixed and stops there whatever the language grows next. That is
C#'s twenty years, arrived at on purpose rather than by accident, and with the
boundary somewhere a reader can state.

Stabilizing is cheaper than it sounds, because Roc's pure expression forms
bottom out in a small set of shapes and 24 nodes already cover them. Most of
what a language adds is sugar over shapes that exist: `?` is a `match`, a
destructuring binding is a field read, a `for` is a fold. The versioning
obligation is about the rare genuinely new shape, not about every feature.

The recommendation is the second, decided out loud rather than left to
accumulate: publish the rule, then publish `Ir` with a declared version and a
content hash, the way platforms are versioned. The prototype is short of the
rule and knows exactly where, which section 10 separates from the rule itself:
the gap between what is describable and what a release describes is a release
note, not a language boundary. What stabilizing buys is that the effort saved
goes into the diagnostics of section 7.5, where a user actually meets the
boundary.

### 7.7 It looks like Roc and does not mean Roc

The objection not to wave away. The half of it about types turns out to be
answered; the half about semantics is not.

`o.amount * 0.8` inside a reified body looks like Roc arithmetic. The
multiplication that eventually runs belongs to somebody else: a GPU may contract
it into a fused multiply-add and flush denormals, a SQL engine propagates NULL
through it and rounds by its own rules, and where Roc's integer `*` crashes on
overflow both of them carry on. The ergonomic win of section 7.1 is exactly what
erases the signal that the reader has left the language.

A DSL does not have this problem, because `Sym.times` is visibly not Roc
arithmetic and nobody expects Roc's semantics from it.

The type question answers itself, the way Roc answers everything else:
the translator decides. A reified signature pins the arithmetic through
the whole body, and every `Lit` node carries the type the checker solved it to,
so a translator sees exactly which numeric type it was handed and refuses by
name anything its target cannot represent. Inside `scaled : F32 -> F32` a bare
`2.0` is an `F32`, including when it is bound to an unannotated local first.
None of this needs a new rule, a literal-suffix discipline, or a defaulting
override for reified contexts.

What remains is the part types cannot express. An `F32` is an `F32` in both
places, and multiplying two of them is still not the same operation. A
translator can enumerate the types it supports; it cannot enumerate the ways its
target rounds, saturates or refuses to fail. That is the crash-semantics
question of section 13, and it is the whole of this objection once typing is set
aside.

### 7.8 Then reify effectful functions too

`Code(a => b)` is ill-formed by rule 2 of section 3, and that is not a gap left
open for later.

The effects a translator meets belong to its target rather than to Roc, and a
parameter describes them purely. A GPU texture fetch reads memory the
application bound, and the example shader spells it
`settings.texture0.texture(shifted)`, a method on a `Glsl.Sampler` the caller
supplies. That is what lets a test hand it a sampler answering one flat colour
and call the shader on the CPU. Spelled `texture!` the fetch would make the
shader itself effectful, so no `expect` could call it, and it would leave the
translator reading an effect it must then pretend to perform.

What reifying `!` would cost:

| | |
|---|---|
| `Code.Ir` gains ordering semantics | today `Let` is pure, so a translator is free to inline a binding, share it, or drop one nothing reads, and each choice is a quality question only. With effects the freedom is gone: dropping an unused binding silently changes meaning, and every translator inherits an obligation nothing checks it meets |
| The platform boundary moves | a reified `File.read!` either runs during `roc build`, which is then effectful and no longer reproducible, or is emitted into a target that performs I/O no platform authorized |
| Section 7.7 gets its worst case | `o.amount * 0.8` not meaning Roc's arithmetic is already the sharpest objection here. `db.write!(row)` not meaning Roc's effect is the same lie told about the guarantee Roc makes hardest |

The honest pull is a sequenced target: a migration, a stored procedure, a
compute kernel with a barrier. The answer there is the split Halide and Futhark
make. The reified function is the algorithm, pure and per-element, and the
ordering lives in the combinator library that consumes it, where Roc's effect
syntax works normally. `Glsl.fragment_330(post_process)` is already that shape,
with a trivial schedule.

### 7.9 An alternative: the translator owns the description

Everything above assumes one fixed `Code.Ir` that the compiler builds and every
translator walks. The user side of the design does not depend on that, so the
translator side can be turned around: the translator supplies a type, and the
compiler builds the description by calling one method on that type per
construct in the body, children first. `a and b` reaches a SQL translator as a
call to its `on_and`, and a GLSL translator's `on_plus` returns GLSL text
directly. The translator's own type is its IR.

```roc
Pred := [Row, Col(Str), Op(Str, Pred, Pred)].{
	on_param = |_, _| Ok(Pred.Row)
	on_field = |_, name, _| Ok(Pred.Col(name))
	on_and = |a, b, _| Ok(Pred.Op("AND", a, b))
	on_is_gte = |a, b, _| Ok(Pred.Op(">=", a, b))
	on_if = Code.refuse("a WHERE clause has no `if`; write it with `and` and `or`")
}

where : Table(row), Code(row -> Bool, Pred) -> Query(row)
```

This answers several of the criticisms above:

| Criticism | With the translator's own type |
|---|---|
| 7.1: a DSL checks its limits in the type system, a translator only at build time | the compiler requires only the methods the body uses, so a construct the translator lacks is an error in `roc check`, on the user's line |
| 7.5: the refusals are the feature | a refusal is a one-line declaration, and the compiler attaches the location |
| 7.6: `Code.Ir` is public API forever | a new construct is a new method name, and a translator that lacks it refuses only programs that use it |
| 7.1: the DSL and the reifier compete | one type can carry both the methods a user calls and the methods the compiler calls |

It also stops the compiler from choosing a lowering for everyone. Today `a and
b` arrives as an `If`, and a SQL translator has to recognize that shape and turn
it back into `AND`. With a method per construct, the target keeps the form it
has.

The price is that information flows only upward: a method sees its children,
not its surroundings, and a translator that wants to read the whole body more
than once, to share subexpressions or optimize a circuit, has to build a tree
first. That path stays open, because today's `Code.Ir` becomes one such type,
supplied by the builtins, whose methods build the tags. Existing translators
keep working, and each one can move to its own type one construct at a time.

This is a sketch, not a plan. [`roc-reify-fold-alternative.md`](roc-reify-fold-alternative.md)
has the method vocabulary, the GLSL and SQL versions, the costs in full and the
open questions.

---

## 8. Prior art

Ordered by how close each is to this design. The five closest reify a body; the
last two do not, and are here because they are the ones most likely to be
offered as sufficient.

| Feature | Reifies | Has splice | Closest in |
|---|---|---|---|
| C# `Expression<Func<>>` | a lambda at a typed position | no | mechanism and trigger |
| F# `[<ReflectedDefinition>]` | a named definition | yes, via `Expr` eval | what gets reified |
| Julia + GPUCompiler | the compiler's typed IR | not applicable | what a library receives |
| Swift `#Predicate` | a closure, by macro | no | the target use case |
| Scala 3 `Expr[T]`, MetaOCaml, Template Haskell | a quoted term | yes | the type, not the design |

### Closest in mechanism: C# expression trees

`Expression<Func<Person,bool>> e = p => p.Age >= 18` and
`Func<Person,bool> f = p => p.Age >= 18` are the same source text, and the
target type decides whether the compiler emits a delegate or an inspectable
tree. That is S1 exactly, twenty years earlier, and LINQ-to-SQL, LINQ-to-Entities
and every `IQueryable` provider since is what it bought. Section 7.5 covers what
it cost.

One difference worth copying: C# validates nothing about the tree. Every
"could not be translated" message comes from the provider, which is the same
division this proposal draws between the compiler and the translator.

### Closest in what gets reified: F# reflected definitions

`[<ReflectedDefinition>]` marks a named function so that its quotation is
available later, which is the named-reference half of S1: a function an author
names at a `Code` position.
F# also reifies far more of its language than C# does, so its cliff is much
shallower.

The price is on the consumer. F# `Expr` is pre-inlining and not monomorphized,
so a translator receives generic code with constraint witnesses in it and has to
specialize it itself. Roc describes a body at the types its site fixes, one row
per instantiation, so a translator never sees a type variable, which is strictly
better on this axis. F# is also genuinely two-level, since it can evaluate an `Expr`; this
proposal is not, and section 12 says what that costs.

### Closest in what a library receives: Julia and GPUCompiler

CUDA.jl compiles Julia functions to PTX by consuming the compiler's own
post-inference typed IR through a documented interface. A package, not the
language, owns the GPU. It is the strongest empirical support for the reuse
argument of section 7.1: people really do write one kernel, test it on the CPU
and run it on the GPU, and that workflow is why the ecosystem exists.

The disanalogy is the one that matters for cost. Julia has a compiler at run
time, so exposing IR to a package costs it nothing it was not already paying.
Roc would be paying it new, which is section 7.6.

### The target use case, by macro: Swift `#Predicate`

SwiftData's `#Predicate { $0.age >= 18 }` turns a closure into an inspectable
`Predicate` value that a store can translate. Same goal, same ergonomics,
reached through a macro system this proposal neither has nor wants. Worth citing
because it shows the use case is mainstream rather than exotic, and because the
macro route carries hygiene and tooling costs Roc has declined elsewhere.

Swift's `KeyPath` (`\Person.age`) is a narrower relative and the one Roc would
reach for if section 7.1's field-access residue were the only problem.

### Full multi-stage programming: Scala 3, MetaOCaml, Template Haskell, Lean

`Expr[T]` with `'{ }` and `${ }`, MetaOCaml's `.< >.` and `.~`, Template
Haskell's `[|| ||]`, Lean 4's elaborator. All have splice, most have `run`, and
all therefore carry hygiene, cross-stage persistence and a two-level type
system. `Code(a)` borrows the type and none of the rest: it is the observation
half of quotation with the code-generation half left out, and section 12 is
honest about which consumers that puts out of reach.

Quill is the instructive one here, being compile-time quotation aimed at exactly
the query-pushdown case, and a good illustration of how much machinery the full
mechanism drags along.

### Type reflection without body reification: Zig, Rust, Go

Zig has `@typeInfo` and no macros: a library can see the shape of a type and
generate code from it, and can never see a function body. Rust's derive macros
and Go's reflection land in the same place. This is the comparison that should
worry the proposal most, because Roc already has Zig's half: derived `is_eq`,
`to_hash`, `parser_for` and `encoder_for` are exactly "read the shape of a type,
produce the code".

The distinction is one sentence. Type reflection moves a description of data;
body reification moves a computation. Everything in section 5 needs the second,
and none of it can be assembled from the first.

### The DSL end state: C++ expression templates

Eigen and Blaze push operator overloading as far as any language allows, which
is why section 7.1 deserves to be taken seriously: a determined library really
can build the whole thing. They are also why section 7.5 cuts both ways, because
their diagnostics are a standing joke, and the failure mode of a type-level DSL
is an error message nobody can read. Roc's DSL story is better than C++'s and
would still end in types no reader wants to see printed.

---

## 9. Notes on integration into the current compiler

### 9.1 Four mechanisms were already there

Each of these ships today for reasons that predate reification, which is why the
new surface area is small.

1. **Top-level values are evaluated at compile time.** A translator's output is
   already a build-time constant, so reification adds no new phase, only a new
   thing to put in the phase that exists.
2. **Literal conversion hooks already let a type reinterpret syntax.**
   `from_numeral`, `from_quote` and `from_interpolation` make `21`, `"POST"` and
   `"${a}b"` become whatever the expected type says, with errors at compile
   time. Type-directed reification extends that pattern to one more kind of
   literal.
3. **Purity is tracked and separated syntactically.** A translator needs pure
   code and nothing else, so no new arrow, no effect rows, no effect
   polymorphism.
4. **The checker already records what a translator needs.** Every node has a
   solved type and every method call a resolved target. The reifier reads
   those, and matching a generic function's type against the one a site fixes
   is all the specialization it adds, so a translator receives a monomorphic
   typed expression, which is what a code generator wants.

### 9.2 The prototype's shape

The feature is the single commit on the `reify` branch, over roc-lang/roc
`main` at `f45bfbed19`. The measurements below cover `src/` only: the
translator examples and the regenerated snapshots are beside it.

| File | Added | Removed | What it is |
|---|---|---|---|
| `src/check/code_reifier.zig` | 8425 | 0 | The whole feature |
| `src/eval/test/eval_staging_tests.zig` | 1917 | 0 | Its tests |
| `src/compile/test/code_reifier_test.zig` | 1602 | 0 | Its tests |
| `src/build/roc/Builtin.roc` | 668 | 0 | `Code`, `Ir`, `Ty`, `Lit`, `Pattern`, `Branch`, `Def` declarations |
| `src/check/Check.zig` | 660 | 12 | Recording each `Code` site and template, plus hooks in annotation checking |
| `src/check/checked_artifact.zig` | 507 | 25 | The single entry point, the foreign lookup, plus switch arms |
| `src/check/report.zig` | 215 | 0 | Refusal diagnostics |
| `src/postcheck/monotype/lower.zig` | 83 | 137 | Net smaller after the change |
| `src/postcheck/boxy/lower.zig` | 61 | 186 | Net smaller after the change |
| 22 further files | 522 | 12 | One to a hundred lines each |

Of 14660 added lines, 11944 are the reifier and its own tests. The module is a
bolt-on by construction: it takes the module being published as `anytype`,
reaches the rest of the compiler through a `ForeignLookup` vtable, reads only
const views, mutates nothing but a `ConstStore` handed to it, and is called from
exactly one place (`src/check/checked_artifact.zig:36975`). The two largest
exhaustive-switch files in the pipeline came out of the change smaller than they
went in.

### 9.3 How the reifier affects working on the Roc compiler

It adds some mechanical work, but doesn't couple much to the rest of the compiler.

Reification is inert unless a `Code(f)` appears in an annotation, so most work
on the compiler never has to reason about it. It adds one case to the checked
expression union, `code_from_lambda`, and nearly everywhere that case appears it
is a no-op sitting with its neighbours.

The mechanical cost comes from that same variant. It has to be listed in 93
places outside the reifier, most of them one-line prong lists of about 45
variants, which is the worst shape a merge conflict can have. The new builtin
type declarations shifted every type-variable number the snapshot tests print,
so 342 snapshots were regenerated, and `CACHE_VERSION` moved to 107.

The snapshot number says more about the snapshot format than about this feature.
Any future builtin addition will pay the same 342-file toll.

Three places couple more deeply:

1. `Check.zig` routes annotation unification for a reified site through its own
   type variable, so anyone reworking annotation unification will meet it.
2. `report.zig` intercepts the general argument-mismatch report and substitutes
   a reification-specific one when the expected type is `Code`.
3. The reifier's own exhaustive switches. A new checked-expression or
   checked-type variant has to be taught to the reifier or grouped into one of
   its rejection arms, and choosing which is a judgement call.

Only the third recurs; the first two are one-time reading.

### 9.4 Dropping it

Deleting the `code_from_lambda` variant makes Zig's exhaustiveness checker point
at all 93 arms, so removal is mechanical and nothing can be silently missed.
Roughly a day, and no judgement calls except the snapshot regeneration.

What cannot be done cheaply is putting the feature aside. The union variant, the
`NodeStore` side table, the `Check.zig` frame field and the builtin declarations
all sit unconditionally in shared structures, so there is no seam to hide behind
a flag; inventing one would cost more than either keeping or deleting. The
options are keep or delete, not park, and delete is cheap.

---

## 10. The boundary, and where a release sits

A reified body may name only what the compiler has already fixed. That is the
whole rule. Three kinds of thing are never fixed, and they are the only
exclusions.

| Excluded | Why |
|---|---|
| A function value nothing fixes: chosen by an `if`, read from a record field, taken from a list | the compiler cannot say which function it is, so there is no body to describe. Defunctionalizing it would emit a dispatch table, and GLSL and SQL have no dispatch table |
| An undetermined type: a type variable, a `where` variable or an open row that nothing fixes | the body reads differently at each instantiation, so there is no one body to describe |
| A `Code` not fixed at build time: a template argument computed at run time, or a `Code` passed to a template | rule 7 of section 3. This one is a choice rather than an absence, and lifting it raises the cross-stage persistence question section 12 defers |

A reified function's types are worked out the way any other Roc function's are.
Passing `pick : a -> U16` to `describe : Code(Str -> U16) -> Str` is an
ordinary call, so `a` becomes `Str` here for the same reason it would if `pick`
were being called rather than reified, and `Str` is the type the translator
reads. A function annotated more narrowly than the place it is used works out
the same way: a `Str -> [Red]` passed to a `Code(Str -> [Red, Green])` is
described as returning `[Red]`, the variants its body can build, and `Green`
is what `describe` accepts beyond them. A generic function the body calls is
the same story one level down: it is described at the types that call gives it.

None of that is special to `Code`. The only types left out are the ones the
program never settles on, which is the second exclusion above.

Everything else in pure Roc describes: calls into other modules, recursive
functions, generic functions at whatever types the program settles them to,
`where` constrained functions at the type the site fixes, a function passed to
a function that the call fixes, lambdas written inside the body, a lambda
written where the `Code` is expected and the values the block around it binds,
top-level constants, builtins, opaque nominals, derived `is_eq` and the method a type writes in
place of deriving one, an embedded file, a destructuring binding, an early
`return` and the `?` that rides on it, a `var`, every loop and everything that
leaves one, and `crash`, which is how a branch that cannot happen is written.

A rule is worth more here than a list of supported syntax, for two reasons. An
author who knows the rule can predict every refusal. And the rule does not move
when Roc grows, because a new construct describes if it names fixed things,
whoever adds it. Section 7.5 works through the contrast with C#.

A release is a separate matter. The rule says what may be described; the
prototype does not yet describe everything the rule admits. What is left falls
into two kinds, and each of them refuses by naming the construct that stopped
the walk and the reason, so an author meets a report rather than a failure
further down the pipeline.

| Kind | What is left |
|---|---|
| Mechanical | a tag union whose row the checker left open; `to_inspect`; a record update over a record with an optional field; a `.?` path; a record pattern whose rest binds a name |
| Needs an order decided | a top-level value that has to be computed, which the compiler evaluates only after it builds the description |

`roc-reify-design.md` lists every construct, ticked or not, with the reason
line the compiler prints for each refusal.

The statements that leave or assign share one shape, which is why they closed
together. The `Ir` has no assignment and needs none: a branch that returns
hands its value back and a branch that does not runs the statements written
after it, so `if c { return a }` is an `If` whose alternative is the rest of
the body, and `x?` is that same rewrite around a binding, even when the `?` is
written inside an expression. A `var` is versions rather than mutation, `$x`
then `$x#1`, and a loop is the fold it already was, carrying the `var`s its
body writes from one turn to the next. All of that is work in the compiler,
needing nothing from the language.

Where an escape leaves is what decides its shape. What an early `return`
transfers to is written after it, so a branch says the whole of it. What a
`break`, and a `return` that crosses a loop, transfer to is the turns of the
loop that have not run, which no branch says, so those two take a node each.
The node carries the value the author wrote rather than a `[Continue, Break]`
step result, so a target with its own `break` and `return` emits them where
they stand and a target that folds lowers them itself. The split falls along
target capability: a target with no loops at all, SQL or a query plan, still
takes `return` and `x?` and never meets a control-flow node.

---

## 11. Types of applications

Three cases. All three work with what this proposal introduces; the third works
better with one more thing.

### 11.1 Nowhere: the translator is the whole story

A shader compiler's output is bytes, and the consumer already exists: the
platform owns the GPU, and the translator only changed what language the shader
was written in. The same shape covers a regex compiled to a DFA table, a
protocol validator compiled to a state machine, and a schema compiled to a
codec.

### 11.2 The platform already owns the executor

A CUDA kernel lowered to PTX at build time still has to be launched, and
`/dev/nvidia` is I/O, so the platform owns the launch. Query pushdown has the
same shape with a database connection in place of a driver: the predicate
compiles to SQL where it is used in a query and runs in the process where it is
called directly, and there is exactly one definition to test. No platform change
is needed here either, because the driver or the connection is already there.

### 11.3 The executor is native and no existing platform carries it

An app that needs a native engine its platform does not have. Incremental
computation over an engine such as DBSP is the clearest example.

A translator plus a platform that carries the engine is enough to make this
work, and that is the whole requirement. What it costs is choice: the app is
then tied to that one platform, and a webserver app and a game app need two
different platforms both carrying the same engine.

A potential platform extension feature would lift that: a mechanism for
composing I/O capabilities from more than one source, so an engine can be added
to a platform without forking it, while native code still arrives only through a
platform. Reification does not depend on it, and it has its own independent
motivation, but the two together are what make an engine usable from any app
rather than from one platform's apps.

Letting a translator package ship native code directly would be the other way to get there,
and it is the wrong one. It would give Roc its first exception to "all native
code arrives through the platform", which is a much larger decision than any one
integration justifies.

Of the uses in section 5, shaders, regex and codecs are 11.1; GPU kernels and
query pushdown are 11.2; only incremental computation is 11.3.

---

## 12. What the design avoids

**Splicing.** No `Code(a) -> a`, and this is the significant omission. Symbolic
differentiation is the clean example: a translator could walk
`Code(Params -> F64)` and derive its gradient, but with no splice the result is
data the program must interpret rather than a Roc function it can call. Adding
splice would make Roc a two-level language, with hygiene and cross-stage
persistence attached. Worth wanting and worth deferring, so long as the cost is
stated: some translators are out of reach until it exists.

**A runtime constructor for `Code`.** Every `Code` value is determined at build
time, which is what makes rule 7 of section 3 hold and what keeps a translator
from needing a runtime.

**Automatic lifting.** Not `f(xs)` where `f : a -> b` and `xs : Rel(a)`.
Type-directed lifting reads as magic exactly when a reader most needs to know
what is happening. `xs.map(f)` gives the same result and says it.

**Higher-kinded types.** Not needed. `Code(a)` is a first-order constructor used
at concrete types.

**Any first-party knowledge of shaders, GPUs, SQL or incrementality.**

**A reified region block.** A form such as `Gpu.kernel { … }` would buy a
visible boundary and a scope where "only reifiable calls are in scope" could be
enforced eagerly. It costs new grammar and a block-mode construct Roc has
nowhere else. Revisit only if S1's invisibility turns out to be a real
complaint.

**A sigil on the lambda.** Forms such as `^|p| p.age >= 18`, echoing Template
Haskell's `[|| … ||]` and Scala's `'{ … }`. Rejected on two grounds: Roc
documents having exactly one syntax for defining a function, for the same reason
it has one syntax for every other value; and the free sigil budget is spent
(`!` effectful, `$` var, `?` try, `_` ignore).

---

## 13. Open questions

**Crash semantics.** Roc's `+` crashes on overflow and pure functions are not
total. A GPU warp or a database engine has nowhere to put a crash. Either
translators reject any expression that can crash, which rules out bare `+` and
pushes reified code onto `plus_try`, or translators define what a crash means in
their domain. `Code` should at minimum expose whether an expression can crash so
a translator can enforce a policy. It is the sharpest unsolved question here, and
it comes from Roc's own choices rather than any consumer's.

**`Dec` where a translator cannot run it.** `Dec` is 128-bit fixed point scaled
by 10^18, which most GPUs cannot do. This is much less of a problem than it
first looks, because the reified signature pins the arithmetic: inside
`scaled : F32 -> F32`, a bare `2.0` reifies as `F32`, and so does a `2.0` bound
to an unannotated local and used against an `F32`. A `Dec` reaches a translator
when the author asked for one, and the translator refuses it by name like any
other type it cannot honour. What is left open is only the quality of that
refusal, which is the section 7.5 point: a translator should say what it does
support rather than only what it does not.

**Naming a constant.** Mostly settled. A top-level value written out as data,
a literal or an aggregate of literals, folds into the description where the
name stood, and so does a template argument named the same way; a value the
block around a lambda binds is repeated at the head of its body. What is still
refused is a top-level value that has to be computed, `limit = xs.len()`,
because the compiler evaluates it after the description is built. Describing
it means evaluating it first and folding the result, which works for anything
the fold already writes and has no answer yet for an opaque value or a
function. One consequence to design for either way: folded constants become
load-bearing in the alpha-equivalent normal form of rule 6, so two
instantiations of one template at different constants must not compare equal
or hash alike.

**Crossing the boundary in both directions.** A translator that hands values to
a native engine needs them encoded, and the encoding is a format the translator
defines rather than a function it writes. Roc's existing derivation should
synthesize the rest from the record types involved, the way `parser_for` and
`encoder_for` already do. The risk is that one format then has three independent
derivations: the compiler's for the Roc side, the translator's for the IR it
emits, and the engine's for its own row layout. The first and third must agree
byte for byte with nothing checking it, so a disagreement is a wrong answer
rather than a build error, and a differential round-trip test is the only
defence.

**Reification across a module boundary.** The prototype settled this. A plain
call carries a call node the translator resolves itself rather than inlining
the callee, which keeps the structure a translator wants and is the only design
a recursive function has an answer for; the compiler hands the translator a
table of reified definitions beside the root, so resolving that name is a
lookup rather than the user's bookkeeping; and the table spans modules, reaching
even one the described module never imports, because a callee is resolved
through the binding the checker recorded rather than through an import. The
generic callee settled the same way: the compiler matches the callee's scheme
against the type the call fixes it to and writes one row per instantiation,
keyed by what was fixed, and a function named at a `Code(f)` takes the same
treatment from its site. What a translator reads off a row is the row's own
type, so the substitution stays inside the compiler and section 7.6's question
about what a `Code` value contains does not move.

**A refusal as a compiler diagnostic.** A translator's `Err` reaches the user
as whatever the program does with it, and the `crash` most programs reach for is
reported as a compile-time crash at the call, not at the construct the
translator refused. Every node already carries its region, so a translator can
name the line in its message, as `Glsl.roc` does. A well-known method in the
spirit of `from_quote`, whose `Err` the compiler reports at a region the
translator names, would make the refusal a diagnostic in `roc check`. It would
be parameterized by the function type, where `from_quote` is not, and whether
the well-known method table accommodates that is a real question.

**Compile-time cost.** A translator that runs a real lowering executes inside
`roc check`. Roc already evaluates top-level values at compile time, so this is
more of the same in kind but not in degree, and it lands on editor latency.

**Higher-order code.** Settled for the first-order targets this proposal is
written for, and open past them. A function the compiler fixes is described by
naming its row, so a lambda written at a call site and a function passed as an
argument both describe today, and a function value nothing fixes is outside the
boundary of section 10. What stays open is whether `Ir` should ever carry a node
for applying an expression, which would serve a target holding closures of its
own, a JavaScript backend or an interpreter, at the price of every other
translator having to refuse it.

**`dbg` and `expect` inside reified code.** The prototype refuses `dbg` and
passes over `expect`, because an assertion written for Roc's own test run has
no place in a target. `expect` could be more interesting: a translator could
discharge some statically and compile others into runtime checks, giving
reified code a property ordinary DSL predicates lack. That needs an `Ir` node
for it, and none exists.

---

## 14. Example usage

One per case in section 11, written against real APIs.

### 14.1 A fragment shader for roc-ray, case 11.1

roc-ray's `Draw.Shader.from_source!` already takes GLSL as a `Str`. A shader
translator changes nothing about the platform; it changes what language the
string was written in.

```roc
# Ordinary Roc over ordinary numbers. Callable, testable, readable.
wobble : { uv : Vec2, time : F32, scene : Glsl.Sampler } -> Vec4
wobble = |{ uv, time, scene }| {
	wave = F32.sin(uv.y * 28.0 + time * 2.0) * 0.004
	scene.at({ x: uv.x + wave, y: uv.y })
}

expect wobble(Glsl.flat_probe).a == 1.0        # an ordinary test

# The translator. Runs during `roc build`; `source` is a Str constant in the binary.
source : Str
source = Glsl.fragment_330(wobble)
#   #version 330
#   in vec2 uv; uniform float time; uniform sampler2D scene;
#   out vec4 finalColor;
#   void main() { float wave = sin(uv.y*28.0 + time*2.0)*0.004;
#                 finalColor = texture(scene, vec2(uv.x + wave, uv.y)); }

init! = |io| {
	shader = Draw.Shader.from_source!({ vertex_source: "", fragment_source: source })?
	time = shader.uniform_f32!("time")?
	Ok({ shader, time })
}
```

The argument record is the interface: each field becomes an `in` or a `uniform`
by name and type, and the return type becomes `finalColor`. Nothing new reaches
the platform or the host.

### 14.2 A CUDA kernel and a pushed-down query, case 11.2

The lowering is the same idea against a different text format. What differs is
that the output cannot run by itself: somebody has to own the driver, and a
driver is I/O, so the platform owns it.

```roc
saxpy : { a : F32, x : F32, y : F32 } -> F32
saxpy = |{ a, x, y }| a * x + y

# Compile time: lowered to PTX, a constant in the binary.
job : Cuda.Kernel({ a : F32, x : F32, y : F32 }, F32)
job = Cuda.kernel(saxpy)

# Run time: the platform owns /dev/nvidia, so it owns the launch.
main! = |_| {
	out = Cuda.launch!(job, { grid: 4096, args })?
	…
}
```

Query pushdown has this exact shape with a database connection in place of a
driver, and it is the clearest demonstration of what section 7.1 claims:

```roc
eligible : User -> Bool
eligible = |u| u.age >= 18 and u.country != Banned

expect eligible({ age: 21, country: Fr })      # ordinary test, ordinary function

adults : Sql.Query(User)
adults = Sql.table("users").where(eligible)
#   at compile time:  SELECT * FROM users WHERE age >= 18 AND country <> 'RU'

main! = |_| {
	rows = Db.run!(conn, adults)?
	…
}
```

One predicate. It runs in the database when used in a query and in the process
when called directly, and there is exactly one definition to test. No ORM
expression builder, no string SQL, no second language.

### 14.3 An incremental view over DBSP, case 11.3

DBSP is an incremental view maintenance engine. A query is defined once over
collections, and the engine keeps its answer current under insertions and
deletions by computing the change rather than the answer again, at a cost
proportional to the change rather than to the data.

```roc
# The translator lowers these lambdas; the combinators build the circuit.
alerts : Rel(Alert)
alerts =
	Rel.input(Reading)
		.filter(|r| r.celsius > 80.0)
		.key_by(|r| r.sensor)
		.count()
		.filter(|(_, n)| n >= 3)
		.map(|(sensor, n)| { sensor, breaches: n })

main! = |_| {
	engine = Engine.start!(alerts)?
	engine.push!(batch)?
	changed = engine.step!()?          # only what the batch changed
	…
}
```

The engine is a library with its own operators and its own way of describing a
circuit over them. The translator's job is to read the `Code(a)` for each lambda
and say the same thing in that vocabulary: the combinators fix the topology, and
reification supplies the expressions it is built out of.

The executor is native and does not finish at build time the way a shader
compiler does, so some platform has to carry the engine. Reification lowers the
lambdas and stops there. Section 11.3 covers what carrying the engine means, and
why a platform extension mechanism would let any app use it rather than only the
apps built on a dedicated platform.

---

## 15. The motivation behind the proposal, and closing thoughts

The proposal grew out of one concrete idea: make an incremental view maintenance
engine pleasant to use from Roc, in the applications that would benefit most
from one and are least likely to adopt a specialized platform.

- A webserver keeping a derived view current.
- A game keeping per-frame queries over its own entity tables current without
  recomputing them.

Both want the engine's semantics. Neither wants to be locked to one platform,
and neither wants a query DSL wedged in beside Roc.

There are two ways to get there. One is a DSL built on static dispatch, and
section 7.1 is the honest account of how far that carries in Roc, which is
further than most languages manage. The other is to let the engine read the
function the programmer already wrote. The reason to prefer the second is not
elegance. It is that a query which is an ordinary Roc function can be tested
with `expect`, called on real values, read by someone who knows Roc and nothing
else, and checked against a pure-Roc reference implementation. A DSL predicate
is none of those, because it was never a function.

The wider case is that the same mechanism, once it exists, turns shaders, GPU
kernels and query pushdown into libraries rather than compiler or platform
features, and that languages which added some version of it have generally been
glad they did. C# got LINQ. Julia got a GPU ecosystem. F# got query expressions
and a decade of tooling.

Three conditions would make it defensible rather than merely attractive:

1. `Code.Ir` stabilizes on the boundary of section 10, declared as the rule it
   is rather than accumulated by omission, so it never becomes a second
   definition of what a Roc expression is and an author can say where it ends
   without consulting a table.
2. Refusal diagnostics are treated as the feature rather than as error handling,
   because they are the interface every user eventually meets.
3. The proposal is defended on the claim that survives section 7.1. Arguing it
   on ergonomics alone invites the reply that a Roc DSL is nearly as ergonomic,
   and that reply is substantially correct. The claims that hold are the
   predicate which is also a function, the syntax a DSL cannot reach without
   changing what `>=` means, and the uses in section 5 where no DSL is in the
   running at all, such as a shader.

The one thing not to do is claim the whole territory and then defend only the
part that holds.
