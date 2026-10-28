# Reified code in Roc

A proposal for one new kind of value: a pure Roc expression reified into data
instead of compiled into machine code. It lets an external compiler consume Roc
as a specification, which is what makes GPU kernels, shaders, incremental
computation and other DSL-like use cases expressible as libraries rather than as
compiler features.

Status: design sketch, with a working prototype on the `reify` branch and three
example translators. Section 1 ends with a status table. Semantics and syntax
come first; the deep material is sections 9 onward.

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

### Where the prototype stands

| Part | State |
|---|---|
| What it describes | Pure Roc as section 10 states it: literals, operators, calls (helpers, generic and recursive functions, other modules), lambdas, templates, `if` and `match`, loops, early `return` and `?`, `var`, `crash`, top-level constants, nominal types, derived methods. A construct it does not describe stops with a report that names the construct |
| What a translator reads | A normal form: rows of nodes, each with its type, in one canonical order. Every refactor in the list of `roc-reify-normal-form.md` section 7 gives the same value. `Code.is_eq` and `Code.to_hash` compare it. It is version 17 (`src/reify/mod.zig:38`) |
| How a translator names a node | `Code.Inlined.inline_digest` gives a node of the `inline` view a content digest that survives the refactors above and helper extraction (`roc-reify-normalization-plan.md`, M8) |
| Rows the compiler chooses | A `Code.Outlined(f)` site gets the `outline` view: each computation of at least four operations that repeats is one row (`roc-reify-normalization-plan.md`, M9). Places that differ in a value pass it as an argument, so `step(input.a)` and `step(input.b)` call one row (V3b). The rows do not depend on how the author split the code into helpers |
| Laws of the builtins | A `Code.Lawful(f)` site gets the `graph` view under layer L: a loop that appends meets `List.map` or `List.keep_if`, a `List.fold` meets its loop, two `map`s meet one, and `len() > 0` meets `!is_empty()` (`roc-reify-normalization-plan.md`, M10). A site of any other type keeps each form as written |
| Literal intervals | Every integer value has an interval from literals, from the tests that dominate it and from the index of a range loop. A test it decides is gone, `while $i <= n` with `n` bounded below the type's highest value meets `for i in 0..=n`, a checked `+` proved to fit can leave a loop, and a bounded `(a + b) + c` meets `a + (b + c)`. `1 + a` meets `a + 1`, and two parameters of the root are in parameter order (`roc-reify-normalization-plan.md`, M11) |
| Facts across loop turns | A loop controlled by a `$done` flag meets the same loop with `break`, and a second counter stepped with the index meets `i + j0` (`roc-reify-normalization-plan.md`, M12) |
| How a translator refuses | It returns an `Err`, or calls `Code.refuse_at`, which the compiler reports at the source of the node (section 13) |

Three translators ship as examples. Each one has an `expected_output` file and a
`refactored.roc` that prints the same text after renames and reordered bindings.

| Example | It emits | `roc test` expects | Run by `parallel_cli_runner.zig` |
|---|---|---|---|
| `examples/reifying/glsl/` | a GLSL 330 fragment shader | 8 in `main.roc`, 1 in `refactored.roc` | both |
| `examples/reifying/sql/` | a SQLite script for a schema, migrations, seed rows and queries | 12 in `main.roc`, 11 in `refactored.roc` | `refactored.roc` |
| `examples/reifying/dbsp/` | a Rust program for the `dbsp` crate, which is not compiled here | 19 in `main.roc`, 1 in `refactored.roc` | both |

`examples/reifying/hello/` is a fourth, smaller translator of 63 lines. It turns an arithmetic function into an expression, and it shows both ways to refuse (`Err` and `Code.refuse_at`). The CLI suite runs it.

`examples/reifying/shaders-without-reifying/` is the control experiment: the
shader of the GLSL example written as a library DSL.

What the prototype still refuses (`roc-reify-design.md`, "What the remaining
unticked boxes cost"):

| Refused | Why |
|---|---|
| A function value nothing fixes: read from a list, or from a parameter of the described function | there is no definition to describe. A function chosen by an `if`, or read from a record literal, between known functions describes |
| A name that exists only at run time: a function parameter, a branch or loop binder, a `var`, read by a lambda from outside itself | timing: the description is built before the value exists |
| A site that names a top-level value computing a function | the site's root needs a lambda whose parameters it can list. A use of such a value inside a described body describes (section 13, "Naming a constant") |
| A computed top-level value of another package | its body belongs to that package, and the description does not read it |
| A tag union whose row nothing closed | it stands for many unions, and a description is monomorphic |
| A custom `from_interpolation` that returns early with `?` or is generic in its item type | the walk runs the first stage where the literal stands, and a `?` can leave the row it is walked in |
| `dbg`, and any effect | out of scope by design (sections 7.8 and 13) |

The tests, in layers. The counts were taken at the time of writing.

| Layer | Where | What it catches |
|---|---|---|
| Normal-form unit tests | `src/reify/` (160 `test` blocks) | a rule that fires wrongly, a pass that breaks a verifier invariant |
| Reifier tests through the checker | `src/compile/test/code_reifier_test.zig` (181 tests) | a walk that describes a body wrongly |
| Staging cases, from checker to translator | `src/eval/test/eval_staging_tests.zig` (116 cases) | the same, for calls into other modules and builtins |
| CLI fixtures | `test/cli/Staged*.roc` (48 files), run by `src/cli/test/parallel_cli_runner.zig` | a described value or a report that changed |
| Fuzzers | `src/reify/fuzz_gen.zig`, `src/compile/reify_fuzz.zig`, `test/fuzzing/fuzz-reify.zig` | two spellings of one term that differ, or a normal form that computes what Roc does not |
| Examples | the three above | translator output that changed under a refactor |
| Rule derivation, offline | `zig build reify-rules`, `src/reify/derive/` (48 `test` blocks) | a normalization rule that is missing |

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
| The description | `Code.Graph` | Plain Roc records and tag unions, in a normal form |

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
   - a top-level value, in this module or one it imports. Its definition
     names only things the compiler fixes, so it describes as that definition
     written where the name stood. `limit = 7.0` read as `x > limit`
     describes as `x > 7.0`, and `limit = 7.0 * 2.0` as `x > 7.0 * 2.0`.
   - a value the surrounding block binds, when the lambda is written at the
     `Code` position inside that block. The binding is repeated at the head of
     the lambda's body, so it describes as a `Let`.
   - a named function, which describes by its body: inlined where it is
     called, or a `Call` of a row of its own where it is called from two
     places or recurses (section 4). A function of another package is the
     exception. It arrives as a named primitive and its body is not read.

   What it cannot read is a value that exists only once the program runs: a
   function parameter, a branch or loop binder, a `var`. That is timing rather
   than purity: the description is built before any such value exists, so a
   captured one could only arrive as an opaque pointer, which is what this
   feature exists to avoid. A translator that returns a `Code.Bound` opts in
   to such values as typed input slots of the description, and receives no
   value: the program receives the values next to the translator's result
   (section 10.1). A top-level value that computes a function,
   `doubler = make(2.0)`, describes as the definition it was written as, so
   the lambda of `make` is a row and its capture is the literal `2.0`. A
   computed value of another package is refused, because its body the
   description does not read. Each refusal names the value. Section 13
   carries what is left of this.

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
6. **Structural.** `Code` has `is_eq` and `to_hash` over a normal form, which
   gives translators common-subexpression detection and a stable cache key for
   compiled artifacts for free. The prototype has both (`src/build/roc/Builtin.roc:24196`,
   `:24200`). A normal form has no names: parameters and nodes are numbered, so
   two sites that differ only in the names of locals, parameters or helpers,
   or in the order of independent bindings, are equal and hash alike
   (`test/cli/StagedSites.roc`). Equality ignores the key of the site that
   built the value. It does compare the `Code.version`, so a value built under
   another version of the rules is not equal to one built under this version.
   The hash is the one a translator puts in the key of a cache.
7. **Compile-time constructible only.** No runtime constructor. With rule 3,
   the description in every `Code` value is fully determined at build time.
   A captured run-time value is a typed slot of the description, and its
   value never reaches the translator (section 10.1).
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
one read from a list. Those are the error cases, with a message that says so. A
function chosen by an `if` between known functions, or read out of a record
literal, does qualify: each branch is described, and the call becomes a
`Switch`.

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
	compile = |code| {
		root = code.graph().root_row()
		match root.nodes.find_first(|node| Kernel.has_no_form(node.op)) {
			Ok(node) => Err(BadCode(
				"this GPU translator cannot lower a ${node.ty.name()} here. Arithmetic, comparison, field access, tags and switches are supported; lists and loops are not."
			))
			Err(_) => Ok(Kernel.lower(root))
		}
	}

	has_no_form : Code.Op -> Bool
	has_no_form = |op| match op {
		List | Item | Loop(_) | ForList(_) => Bool.True
		_ => Bool.False
	}
}

job = Kernel.compile(saxpy)
```

This is the move the proposal turns on. The compiler learns one concept, and
every diagnostic a user ever sees about what a GPU, a query planner or an
incremental engine accepts is written in Roc by the author of that translator.

A refusal is an ordinary `Err`, and the program decides what to do with it.
`examples/reifying/glsl/main.roc` matches on the result; a `crash` on the `Err`
is reported as a compile-time crash at the call. A translator that wants the
compiler to report the refusal at the construct it refused calls
`code.refuse_at({ row, node }, message)` instead. Section 13 gives what that
does and what is still open.

### What a translator reads

`Code.graph : Code(f) -> Graph` gives the description as plain records and tag
unions, declared in `src/build/roc/Builtin.roc` from line 23625. It is a
normal form: a graph of definitions whose shape depends on what the body
computes and not on how the author wrote it. `roc-reify-normal-form.md` is the
design.

| Type | What it holds |
|---|---|
| `Graph` | `{ root, rows }`. `root_row`, `row(id)` and `rows` read it. `inputs` lists the fields of the root's one record parameter, and is empty where the root takes none |
| `Row` | One function: `id`, `params` and `result` as `Ty`, `nodes`, a `body` region, and `recursive` |
| `Node` | One operation: `op`, the values it reads in `args`, its `ty`, and `speculatable` (section 13) |
| `Val` | What a node reads: `Param`, `Node` (by index in the row), `Out` (one output of a node with several) or `Arg` (a parameter of a loop body or join) |
| `Region`, `End` | A body, a switch arm, a loop body or a join: its parameters, its nodes, and how it ends. The ends are `Value`, `Jump`, `Return`, `Continue`, `Break` and `Branch`, so control never travels as a tag |
| `Ty`, `Lit` | The checker's solved type of every node, and the literals. `Ty` has `children`, `numeric` and `name`, so a refusal can name a type. An `Int` or a `Frac` carries its type, so an `F32` prints as an `F32` |
| `Key` | The case of one `Switch` arm: `Tag`, `Lit`, `Len`, `AtLeast` or `Default` |
| `Tree`, `Graph.to_tree(id)` | One row as nested expressions, for a translator that emits expressions. A value read once is written where it is read. A value read more than once, or inside a loop body or lambda when it is built outside, stays a def, so shared work stays shared |

`Op` has 24 variants: `Lit`, `Prim`, `Call`, `Closure`, `Record`, `Tuple`,
`List`, `Tag`, `Wrap`, `Unwrap`, `Field`, `Index`, `Payload`, `Item`,
`OptField`, `Switch`, `And`, `Or`, `ForRange`, `ForList`, `Loop`, `Lambda`,
`Crash` and `Derived`. A builtin is a `Prim` named by its owner and method
apart, such as `Num.F32` and `sin`, so a translator keys its table by method
and reads the type from the node. The operator `+` and the method `.plus()`
arrive as the same `Prim`.

The normal form drops what a translator should not depend on:

| Written | Arrives as |
|---|---|
| a name of a local, a parameter or a helper | a number. Parameters are `p0`, `p1`; nodes are indexes |
| `a and b`, or `if a b else Bool.False` | one `And` node |
| `if`, `match`, `?`, `??`, an early `return` | a `Switch` over a canonical decision tree, with joins for the code after an exit |
| `for`, `while`, a tail-recursive helper | `ForRange`, `ForList` or `Loop`, with numbered state slots |
| the same value written twice, a binding read once, an unused binding | one node, placed where it runs, or no node |
| `{ ..r, y: 3 }`, a defaulted field | a full `Record` |

A body carries no source region and no name, which is what makes the first row
of the next table true. The compiler keeps a table from every node to the source
it came from, and `refuse_at` is its one reader. The price is that a translator
cannot put a line in a message of its own.

| A translator can rely on | Because |
|---|---|
| The same value after a rename, a reordered binding, a helper extracted or inlined, `x.f(y)` against `f(x, y)`, and every other refactor of `roc-reify-normal-form.md` section 7 | the walk builds the normal form and no syntax-shaped tree. `examples/reifying/*/refactored.roc` rename parameters and locals and reorder bindings, and print their `expected_output` byte for byte |
| Roc's result wherever Roc does not crash, and no evaluation of what Roc would not evaluate | rule C2 of the normal form. `Node.speculatable` is the flag it rests on |
| A version number that changes exactly when the rules, the builtin table or the speculatable list do | `Code.version`, with a test that pins the fingerprint of each released version (`src/reify/mod.zig:33-70`) |

### Calls and the two views

A call to a function of the same package is described by that function's body.
Which form the body takes depends on the view the translator declares.

| View | Declared as | What it keeps as a row |
|---|---|---|
| `graph` | a `Code(f)` parameter, read with `Code.graph` | the root, every recursive function, every helper called from two or more places, and every function a `Closure` names. A helper called from one place is inlined there |
| `inline` | a `Code.Inlined(f)` parameter, read with `.inline()` | the root and the recursive functions. Every other call is inlined however many calls there are, and a function value is a `Lambda` region where it is built. One exception stays: a function whose body can still end in a `Return` is a row until the rebuild turns each `Return` into a jump (`src/reify/views.zig:14-17`) |

The two descriptions of one function, from `test/cli/StagedInlinedView.roc`:

```
graph:  r0 = |U16| -> U16 r1(Num.U16.plus(r1(p0), 1)) ; r1 = |U16| -> U16 Num.U16.times(p0, 3)
inline: r0 = |U16| -> U16 Num.U16.times(Num.U16.plus(Num.U16.times(p0, 3), 1), 3)
```

So a translator meets a `Call` row for recursion, and in the `graph` view also
for a helper that two places share. A translator with no function form, such as
one that writes one expression, declares `Code.Inlined(f)` and meets `Call` for
recursion, and for the one exception in the table. The GLSL example is such a
translator. The SQL example reads the `graph` view and expands each `Call`. A
function of another package, and a builtin, is a `Prim` whose body is not read, so a library that belongs to the translator, such as
`Glsl.Vec3.scale`, is mapped by name. `src/reify/views.zig:3-6` states the
two rules. A third view that picks helper boundaries from the computation alone
is designed (`roc-reify-normal-form.md` section 5.3) and not built.

`Derived` is the one that needs a word here. A compiler-derived method such as
`parser_for` has no Roc body to describe, so the node names the method and the
type it derives over and stops. A translator that owns the target format expands
it in its own language; every other translator refuses it by name.

The real cost of the feature is that the normal form becomes a public API with a
versioning obligation. Section 7.6 argues that the right answer is to stabilize
it on the boundary of section 10, which is all of pure Roc the compiler has
fixed, rather than to track the language.

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

Section 14 works three of these through against the working examples: a shader,
a query pushdown and an incremental view. Its CUDA kernel is a sketch.

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
semantics, specialized to the types each site fixes, which is why `and` arrives
as an `And` node and not as syntax, why `21` arrives with the type it was solved
to, and why a polymorphic function arrives once per instantiation.

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
| Concepts added to the language | one derivation, at most | `Code(a)`, the public normal form (`Code.Graph` and the types in it), a placement rule, a compile-time trigger, a boundary rule with its own diagnostics |
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

### 7.6 The normal form becomes public API, forever

This is the decision that actually matters, and it is larger than the choice
between a DSL and a reifier.

If the normal form tracks the language, then every future Roc feature becomes a
two-place change forever, and Roc acquires a second definition of what an
expression is, which will drift.

If it stabilizes on the boundary of section 10, it covers all of pure Roc the
compiler has fixed and stops there whatever the language grows next. That is
C#'s twenty years, arrived at on purpose rather than by accident, and with the
boundary somewhere a reader can state.

Stabilizing is cheaper than it sounds, because Roc's pure expression forms
bottom out in a small set of shapes and 24 ops already cover them. Most of
what a language adds is sugar over shapes that exist: `?` is a `match`, a
destructuring binding is a field read, a `for` is a fold. The versioning
obligation is about the rare genuinely new shape, not about every feature.

The recommendation is the second, decided out loud rather than left to
accumulate: publish the rule, then publish the normal form with a declared
version, the way platforms are versioned. The prototype does this in three
parts. Every `Code` carries `Code.version`. A test pins the fingerprint of the
rule table, the builtin table and the speculatable list for each released
version, so a change to any of them fails until it takes a new version number
(`src/reify/mod.zig:33-70`). And the list of refactors that leave the value
unchanged is published and fuzzed (`roc-reify-normal-form.md` section 7). The
prototype is short of the rule and knows exactly where, which section 10
separates from the rule itself: the gap between what is describable and what a
release describes is a release note, not a language boundary. What stabilizing
buys is that the effort saved goes into the diagnostics of section 7.5, where a
user actually meets the boundary.

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
| The normal form gains ordering semantics | today independent nodes have no order beyond their data dependencies, so the compiler is free to share a computation, move it or drop one nothing reads, and a translator inherits that freedom. With effects the freedom is gone: dropping an unused binding silently changes meaning, and every translator inherits an obligation nothing checks it meets |
| The platform boundary moves | a reified `File.read!` either runs during `roc build`, which is then effectful and no longer reproducible, or is emitted into a target that performs I/O no platform authorized |
| Section 7.7 gets its worst case | `o.amount * 0.8` not meaning Roc's arithmetic is already the sharpest objection here. `db.write!(row)` not meaning Roc's effect is the same lie told about the guarantee Roc makes hardest |

The honest pull is a sequenced target: a migration, a stored procedure, a
compute kernel with a barrier. The answer there is the split Halide and Futhark
make. The reified function is the algorithm, pure and per-element, and the
ordering lives in the combinator library that consumes it, where Roc's effect
syntax works normally. `Glsl.fragment_330(post_process)` is already that shape,
with a trivial schedule.

### 7.9 An alternative: the translator owns the description

Everything above assumes one fixed normal form that the compiler builds and every
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
| 7.6: the normal form is public API forever | a new construct is a new method name, and a translator that lacks it refuses only programs that use it |
| 7.1: the DSL and the reifier compete | one type can carry both the methods a user calls and the methods the compiler calls |

It also stops the compiler from choosing a lowering for everyone. Today the
normal form picks one spelling. `a and b` arrives as an `And` node, which a SQL
translator maps to `AND` directly. But `p.title != "Gift card"` arrives as
`Bool.not` over `Str.is_eq`, and `o.quantity >= 10` as `Num.I64.is_lte(10,
o.quantity)`, so the SQL translator mirrors the comparison back
(`examples/reifying/sql/README.md`, "How it is built"). With a method per
construct, the target keeps the form it has.

The price is that information flows only upward: a method sees its children,
not its surroundings, and a translator that wants to read the whole body more
than once, to share subexpressions or optimize a circuit, has to build a tree
first. That path stays open, because today's `Code.Graph` becomes one such type,
supplied by the builtins, whose methods build the nodes. Existing translators
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

The feature is two commits on the `reify` branch over roc-lang/roc `main` at
`2664a27882`: `90a70ce708` reifies a pure Roc function, and `b46d3c1a55`
normalizes the result. The table is `git diff --stat 2664a27882 HEAD -- src/`
at `b46d3c1a55`. It covers `src/` only: the translator examples, the CLI
fixtures and the regenerated snapshots are beside it.

| File | Added | Removed | What it is |
|---|---|---|---|
| `src/check/code_reifier.zig` | 7183 | 0 | The walk from a checked body to the normal form |
| `src/reify/*.zig` (21 files) | 14017 | 0 | The normal form: IR, builder, verifier, rows, views, digests, evaluator, dump |
| `src/reify/rules/` (3 files) | 3123 | 0 | The normalization rule table and its ledger |
| `src/reify/derive/` (22 files) | 18977 | 0 | The offline rule-derivation tool. 12482 of the lines are `.zon` data. No compiler artifact depends on it |
| `src/compile/test/code_reifier_test.zig` | 2340 | 0 | Tests |
| `src/eval/test/eval_staging_tests.zig` | 1794 | 0 | Tests |
| `src/compile/reify_fuzz.zig` | 435 | 0 | The fuzz driver, shared by the fixed seeds and the AFL target |
| `src/build/roc/Builtin.roc` | 738 | 0 | `Code`, `Code.Inlined`, `Graph`, `Row`, `Node`, `Op`, `Val`, `Region`, `End`, `Key`, `Ty`, `Lit`, `Tree` and their methods |
| `src/check/Check.zig` | 598 | 3 | Recording each `Code` site and template, plus hooks in annotation checking |
| `src/check/checked_artifact.zig` | 777 | 22 | The single entry point, the foreign lookup, the provenance table, plus switch arms |
| `src/check/code_emit.zig` | 481 | 0 | Writes the normal form into the module's constant store as a `Code` value |
| `src/check/report.zig` | 276 | 0 | Refusal diagnostics |
| `src/postcheck/monotype/lower.zig` | 85 | 63 | Net 22 lines larger |
| `src/postcheck/boxy/lower.zig` | 61 | 23 | Net 38 lines larger |
| 47 further files | 751 | 37 | A few lines to 130 each |

Of 51636 added lines, 36117 are in `src/reify/`, and 12482 of those are data.
The walk and its two test files are 11317. The module is a bolt-on by
construction: the walk takes the module being published as `anytype`, reaches
the rest of the compiler through a `ForeignLookup` vtable, reads only const
views, mutates nothing but a `ConstStore` handed to it, and is called from
exactly one place (`reifyStagedCode` in `src/check/checked_artifact.zig`). `src/reify/` itself
depends on no compiler stage, so its tests build graphs without a checker
(`src/reify/mod.zig:1-4`).

### 9.3 How the reifier affects working on the Roc compiler

It adds some mechanical work, but doesn't couple much to the rest of the compiler.

Reification is inert unless a `Code(f)` appears in an annotation, so most work
on the compiler never has to reason about it. It adds one case to the checked
expression union, `code_from_lambda`, and nearly everywhere that case appears it
is a no-op sitting with its neighbours.

The mechanical cost comes from that same variant. It appears on 127 lines
outside the reifier, in five files (68 in `src/postcheck/monotype/lower.zig`,
24 in `src/check/checked_artifact.zig`, 23 in `src/postcheck/boxy/lower.zig`, 11
in `src/postcheck/boxy/plan.zig` and 1 in `src/postcheck/literal_demand.zig`),
and on 5 more lines in two test files. Some are one-line prong lists, such as the
47-variant one in `src/check/checked_artifact.zig` (the line that lists
`.pending, .code_from_lambda, .str_segment`), which is the worst shape a merge
conflict can have. The new builtin type declarations shifted every
type-variable number the snapshot tests print, so 343 snapshots changed and one
was added, and `CACHE_VERSION` is 146 (`src/compile/cache_config.zig:316`).
Every change to the stored form moves it.

The snapshot number says more about the snapshot format than about this feature.
Any future builtin addition will pay the same 343-file toll.

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
at every arm, so removal is mechanical and nothing can be silently missed.
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
| A function value nothing fixes: read from a list, or from a parameter of the described function | the compiler cannot say which function it is, so there is no body to describe. Defunctionalizing it would emit a dispatch table, and GLSL and SQL have no dispatch table. A function chosen by an `if` between known functions, or read from a record literal, is fixed: each branch is described, and the call becomes a `Switch` |
| An undetermined type: a type variable or a `where` variable that nothing fixes, and no numeric or row default settles | the body reads differently at each instantiation, so there is no one body to describe |
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

The defaults are the ordinary ones. In `|x| x * 2` at a `Code` position, `x`
takes `Dec`, as it would in a compiled function, and an open record or tag row
takes its row default. A default that does not fit its use, as in
`|x| x * 2.U8`, is refused with that reason. The checker commits none of this.
The walk seals each variable the way Monotype does (`defaultedVariable` in
`src/check/code_reifier.zig`).

Everything else in pure Roc describes: calls into other modules of the package
(a function of another package is a named primitive), recursive
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
| Needs a decision | a computed value of another package, whose body the description does not read; a custom `from_interpolation` that returns early with `?`, or is generic in the item type of its assembler. Derived `is_eq` on a function stays refused, because Roc has no equality on functions |

The mechanical kind is empty. A tag union whose row the checker left open
seals to the variants the definition names. An unset or omitted optional
field, a record update over a record with an optional field, a `.?` before
the last segment of a path, and a record pattern whose rest binds a name
describe with the nodes that already exist: a `Record` that lists the fields it
sets, `OptField`, and a `Switch` on the `Try` that `OptField` gives. A string
interpolation pattern describes as `Str.starts_with`, `Str.drop_prefix` and
`Str.split_first` with their tests. A literal of your own type whose
`from_numeral` or `from_quote` is a Roc function describes as a `Call` of that
row. Derived `is_eq` on an empty tag union, and through an opaque nominal that
derives it, describes as `Derived`.

`roc-reify-design.md` lists every construct, ticked or not, with the reason
line the compiler prints for each refusal.

The statements that leave or assign share one shape, which is why they closed
together. The normal form has no assignment and needs none: a branch that
returns hands its value back and a branch that does not runs the statements
written after it, so `if c { return a }` is a `Switch` whose other arm is the
rest of the body, and `x?` is that same rewrite around a binding, even when the
`?` is written inside an expression. A `var` is single assignment:
each write is a new node, and a node is read by its index, so no name remains. A loop is the fold it already was, carrying the `var`s its
body writes from one turn to the next in numbered slots.

Where an escape leaves is what decides its shape. What an early `return`
transfers to is written after it, so a branch says the whole of it. What a
`break`, and a `return` that crosses a loop, transfer to is the turns of the
loop that have not run, which no branch says, so those two end a region instead
of being a value: `Break` and `Continue` end a loop body, and `Return` ends a
row from any region. The end carries the value the author wrote rather than a
`[Continue, Break]` step result, so a target with its own `break` and `return`
emits them where they stand and a target that folds lowers them itself. The
split falls along target capability: a target with no loops at all, SQL or a
query plan, still takes `return` and `x?` and never meets a loop.

### 10.1 Captured run-time inputs

A lambda at a `Code` position can read a value that exists only when the
program runs: a parameter of the function around it, a branch or loop binder.
The description cannot hold that value, because the description is built
while the compiler runs. A translator can opt in to receive such a value as an
input slot. The description stays fixed at build time, and the translator
still runs once, at build time. The program receives the values at run time,
next to the translator's result, as a SQL driver receives the values of its
bind parameters.

```roc
Stage := {}.{
	## The result is a `Code.Bound`, so the lambda may read run-time values.
	render : Code(U16 -> U16) -> Code.Bound(Str)
	render = |code| {
		graph = code.graph()
		code.bound("${Stage.text(graph)} with ${graph.slots().len().to_str()} slots")
	}
}

scaled : U16 -> Str
scaled = |n| {
	k = n * 2
	bound = Stage.render(|x| x + k)   # the translator ran while the compiler ran
	match bound.inputs() {            # the values arrive when the program runs
		[Int(value)] => "${bound.value()}: n is ${value.to_str()}"
		_ => bound.value()
	}
}
```

The description of the lambda is `plus(p0, times(Input(0), 2))`, with
`Graph.slots` equal to `[U16]`. Slot 0 is `n`. The walk replays `k = n * 2` as
it replays every binding of the block around the site, so `k` is not a slot.

#### The rules

| Item | Rule |
| --- | --- |
| Opt-in | The translator's declared return type is exactly `Code.Bound(a)`. A translator that can fail returns `Code.Bound(Try(s, e))`. A translator with any other return type keeps the refusal, and the refusal names the opt-in. |
| What a slot is | A name that the walk cannot replay and that the compiler does not fix (a parameter, a branch binder, a loop binder), followed by the longest chain of `Field`, `Index` and `Unwrap` reads of it. `order.price` is one slot. `order` is a slot only where the body reads it whole. |
| In the description | `Code.Val.Input(k)` reads slot `k`, as `Param(k)` reads a parameter. `Code.Tree.Input(k)` is the same in a tree. Only the root row reads a slot. A lifted row receives a slot value as a `Closure` argument. |
| Slot types | `Graph.slots : Graph -> List(Ty)`, in slot order. |
| Slot order | The order in which the final root first reads each slot: its nodes in index order, each node's arguments and then the ends of the regions it holds, and the body's end last. A slot that normalization removes is not a slot. |
| Equality and hash | `slots` is part of the description, so `==`, `to_hash` and the cache key read it. The values never enter them. |
| The translator | Builds its result with `Code.bound : Code(f), a -> Code.Bound(a)` (or `Code.Inlined.bound`). The result holds no inputs while the compiler runs, because the values do not exist then. The translator emits one placeholder for each slot it reads, for example `?` in SQL. |
| The site | The call of the translator is a compile-time root. The lambda is a description, so the root does not depend on what the lambda reads at run time. The program reads that root's value, and the site sets `inputs` to one `Code.Value` for each slot, in slot order. |
| The program | Reads `bound.value()` and `bound.inputs()`. A SQL binder maps each `Code.Value` to a driver value with one `match`. |

#### `Code.Bound` and `Code.Value`

```roc
Code.Bound(a) :: { value : a, inputs : List(Code.Value) }

Code.Value := [
	Int(I128),                 # an integer of any type but U128
	U128(U128),
	Frac(F64),                 # an F32 or an F64
	Dec(Dec),
	Bool(Bool),
	Str(Str),
	Record(List(Code.Value)),  # one value per field, in the field order of the slot's Ty
	Tuple(List(Code.Value)),
	List(List(Code.Value)),
	Tag(Str, List(Code.Value)),
	Wrap(Code.Value),          # a nominal value: the value of its backing
]
```

A `Code.Value` follows the slot's `Code.Ty`:

| `Code.Ty` of the slot | `Code.Value` |
| --- | --- |
| an integer type other than `U128` | `Int(value)` |
| `U128` | `U128(value)` |
| `F32`, `F64` | `Frac(value)` |
| `Dec` | `Dec(value)` |
| `Bool` | `Bool(value)` |
| `Str` | `Str(value)` |
| `ListOf(t)` | `List(values)`, one per item |
| `Record(fields)` | `Record(values)`, one per field, in the order of `fields` |
| `Tuple(items)` | `Tuple(values)` |
| `TagUnion(variants)` | `Tag(name, payloads)` |
| `Named(name, backing)` | `Wrap(value of the backing)` |
| `Recursive(name)` | the value of the enclosing `Named` of that name |

A slot type that holds a shape no `Code.Value` expresses is refused at the
site, by name:

| Shape | Reason line |
| --- | --- |
| `Fn` | "a captured function value" |
| `Opaque` | "a captured value of an opaque type" |
| a record field marked `Optional` | "a captured record with an optional field" |

In debug builds, the site asserts that each `Code.Value` it builds matches its
slot type. In release builds a mismatch is unreachable.

#### What stays refused

| Case | Reason line |
| --- | --- |
| A translator that does not return `Code.Bound` | the capture refusal, with the line "A translator whose result is a `Code.Bound` receives such a value as an input slot." |
| A `var` | "a `var`, whose value at the call is not always the value the description reads" |
| A function value with no definition | as before: "a function value that names no definition" |
| A call whose other arguments are not fixed at build time | "a translator that receives captured inputs runs while the compiler runs, so the other arguments of its call must be fixed then" |
| A call that holds two sites with captured inputs | "a call that binds the inputs of two sites" |
| A call whose result type it does not fix | "a translator result whose type the call does not fix" |
| A translator result that holds a function, such as a query builder that keeps its clauses as closures | The call cannot be a compile-time root of its own, because a stored value holds no function, so the reason line is the one for a call whose arguments are not fixed. Return data, such as the rendered text, from a translator that receives captured inputs. |

#### Why these choices

| Choice | Reason |
| --- | --- |
| The opt-in is the return type | The program must receive the values from the call, and the call keeps the type that its signature declares. So the declared return type must hold a place for the values. A parameter type gives no such place. |
| A slot is a leaf with its projections, not the value the lambda captures | R (`roc-reify-normal-form.md:1509` and `:1514`) promises that binding a value once and writing the expression in place give one description, and that destructuring and reading fields give one description. A slot that is the captured name would break both. The projection chain keeps a slot a scalar where the body reads only a field of a record. |
| `List(Code.Value)` and not a typed tuple | The slots are a product of the walk, which runs after the solver. A typed tuple needs the solver to know the slots, which needs a new typing rule. `Code.Value` is an ordinary type. |

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

`examples/reifying/dbsp/` is the half that reification covers. Its translator
turns the lambdas of a circuit into the Rust closures of the `dbsp` crate and
prints one Rust program. The executor is not there: the Rust is not compiled by
the example or by CI, and some platform has to carry the crate, which is the rest
of this section.

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

**A runtime constructor for `Code`.** The description of every `Code` is
determined at build time, which is what makes rule 7 of section 3 hold and what
keeps a translator from needing a runtime. A value that exists only at run time
reaches the program next to the translator's result, through `Code.Bound`, and
never reaches the translator (section 10.1).

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
their domain. The prototype settles the part a translator can enforce.
`Node.speculatable` says that evaluating a node where the body would not can
neither crash nor diverge. It is exact: a builtin the normal form does not list
is not speculatable, and neither is a node over one. Float arithmetic, `_wrap`
arithmetic, comparisons, and reads of a record or tuple are. Checked integer
`+`, `-` and `*`, `//`, `%` and `crash` are not
(`src/build/roc/Builtin.roc:24014`, `roc-reify-normal-form.md` section 1.1). A
translator for a target without short-circuit evaluation, such as SQL's `AND`,
reads the flag on each operand to decide whether it may evaluate them eagerly.
The normal form itself never evaluates a node that is not speculatable where the
body would not (rule C2), so a translation does not crash where Roc does not.

What stays open is what a crash means in a target. A `crash` the author wrote
stays a `Crash` node, and a node that is not speculatable may crash or may only
be missing from the list. A translator that wants to reject every expression
that can crash can reject every node with the flag false, and one that defines a
crash for its domain still has to say so in Roc. The question comes from Roc's
own choices rather than any consumer's.

**`Dec` where a translator cannot run it.** `Dec` is 128-bit fixed point scaled
by 10^18, which most GPUs cannot do. This is much less of a problem than it
first looks, because the reified signature pins the arithmetic: inside
`scaled : F32 -> F32`, a bare `2.0` reifies as `F32`, and so does a `2.0` bound
to an unannotated local and used against an `F32`. A `Dec` reaches a translator
when the author asked for one, and the translator refuses it by name like any
other type it cannot honour. What is left open is only the quality of that
refusal, which is the section 7.5 point: a translator should say what it does
support rather than only what it does not.

**Naming a constant.** Mostly settled. A top-level value folds into the
description where the name stood, as the definition it was written as: a
literal or an aggregate of literals folds to that data, and a computed value,
`limit = xs.len()`, folds to the computation. It is not evaluated first, so
the order of compile-time evaluation does not change, and nothing is needed for
an opaque value. A template argument named by a value written as data folds the
same way; a value the block around a lambda binds is repeated at the head of
its body. What is still refused is a computed value of another package,
because its body belongs to that package, and a site that itself names a
top-level value computing a function, because the site's root needs a lambda.

A top-level value that computes a function, `doubler = make(2.0)`, was listed
here as needing a decision. The decision is that it folds by definition, the
same as a computed constant. The compiler evaluates the value after the
description is built, so an evaluated closure is not available to the walk, and
none is needed: the definition names the lambda and every capture. The checker
records the checked expression the binding was written as
(`CallableEvalTemplate.body`, `src/check/checked_artifact.zig:16986`), and the
walk builds it where the name stands (`src/check/code_reifier.zig`
(`computedFunction`)). A call on the name is one `Call` of the lambda's row
over the capture and then the argument, the name used as a value is a `Closure`
of the row, and a function the definition captures is a row of its own. No
node, no rule and no language surface changes, so `normal_form_version` stays
as it is.

Folded constants are
load-bearing in the alpha-equivalent normal form of rule 6, so two
instantiations of one template at different constants must not compare equal
or hash alike. Two constants written alike describe alike, which is the
by-value equality rule 6 asks for.

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

**Reification across a module boundary.** The prototype settled the case of one
package. A call to a function of another module of the package is described from
that module's published view, through the binding the checker recorded rather
than through an import, so a callee two modules away is reached. What the call
becomes depends on the view of section 4: the callee's body inlined, or a `Call`
of a row where the callee recurses or two places share it. The rows are in
`Graph.rows`, root first, so resolving a `Call` is `graph.row(id)` and not the
user's bookkeeping. A generic callee settled the same way: the compiler matches
the callee's scheme against the type the call fixes it to and writes one row per
instantiation, and rows are identified by a digest of their normal form, so
making a helper generic, or writing the copy at that type, changes nothing. A
function named at a `Code(f)` takes the same treatment from its site. What a
translator reads off a row is the row's own type, so the substitution stays
inside the compiler and section 7.6's question about what a `Code` value
contains does not move.

A function of another package, and a builtin, is a different case. It is a
`Prim` named by owner and method, and its body is not read. That fits the
library a translator owns, `Glsl.Vec3.scale` mapped to `*`, and does not fit a
dependency whose body the translator should read. The design lets a translator
declare which functions are its primitives and reads every other body
(`roc-reify-normal-form.md` section 3.8, the item `code_primitives`). The
prototype has not built that: `src/check/code_reifier.zig:17` is the rule today,
and milestone M13 of `roc-reify-normalization-plan.md` is the work. Until then
every function of another package is a primitive.

**A refusal as a compiler diagnostic.** Settled in kind, with gaps in use.
`Code.refuse_at(code, { row, node }, message)` names a node by its row's `id` and
its index in that row. While the compiler evaluates a top-level value, the
translator stops there, and the compiler reports `message` at every place in the
source the node came from, with the calls that reached it. A node that value
numbering merged has several places, and each one is reported
(`test/cli/StagedRefusal.roc`, run by the CLI case "a translator's refusal is reported at every source of the refused node" in `src/cli/test/parallel_cli_runner.zig`).
When the program runs instead, `refuse_at` is an ordinary crash with the
message. `Code.Inlined` has the same method. It is an ordinary method on `Code`,
so the question of fitting the well-known method table, which `from_quote` sits
in, no longer arises.

What stays open:

| Gap | Detail |
|---|---|
| Only the hello example uses it | `examples/reifying/hello/refused.roc` calls `refuse_at` and `roc check` reports the line. Each of the three larger translators returns an `Err`, because `refuse_at` stops the compile and an `Err` can be tested. Their messages name the construct and, in the DBSP example, the stage, and do not name a line |
| The value carries no region | The regions are in a table only `refuse_at` reads, so a translator cannot put a line in a message of its own. |
| Where it is reported | The report comes from the dev backend's evaluation. The interpreter's evaluation runs only where no problem store exists, so it never reports one (`roc-reify-normalization-plan.md`, the gaps M8a leaves) |

**Compile-time cost.** A translator that runs a real lowering executes inside
`roc check`. Roc already evaluates top-level values at compile time, so this is
more of the same in kind but not in degree, and it lands on editor latency.

**Higher-order code.** Settled for the first-order targets this proposal is
written for, and open past them. A function the compiler fixes is described by
naming its row, so a lambda written at a call site and a function passed as an
argument both describe today, and a function value nothing fixes is outside the
boundary of section 10. A function value that is a lambda is a `Closure` of a
row in the `graph` view and a `Lambda` region in the `inline` view, so a target
with closures has a form for it. What stays open is whether the normal form
should ever carry a node for applying an expression. It has one during
simplification only: a call through a function value is resolved once the value
is known, and a site that still holds one at the end is refused
(`roc-reify-normal-form.md` section 3.8). Keeping it would serve a target
holding closures of its own, a JavaScript backend or an interpreter, at the
price of every other translator having to refuse it.

**`dbg` and `expect` inside reified code.** The prototype refuses `dbg` and
passes over `expect`: an `expect` in a body describes as nothing, so adding or
removing one leaves the value unchanged. An assertion written for Roc's own test
run has no place in a target. `expect` could be more interesting: a translator
could discharge some statically and compile others into runtime checks, giving
reified code a property ordinary DSL predicates lack. That needs an `Op` for it,
and none exists.

---

## 14. Example usage

One per case in section 11. The shader, the query and the incremental view are the
working examples under `examples/reifying/`; the kernel is a sketch.

### 14.1 A fragment shader for roc-ray, case 11.1

roc-ray's `Draw.Shader.from_source!` already takes GLSL as a `Str`. A shader
translator changes nothing about the platform; it changes what language the
string was written in. `examples/reifying/glsl/` is the working version.
`Glsl.roc` is the translator, `main.roc` is the shader, and
`expected_output.glsl` is the text the translator emits for it. It is the shader
`roc-ray/examples/post_process` loads from `assets/post_process.fs`, written in
Roc instead.

```roc
Varyings : { fragTexCoord : Glsl.Vec2, fragColor : Glsl.Vec4 }
Uniforms : { texture0 : Glsl.Sampler, time : F32 }

# Ordinary Roc over ordinary numbers. Callable, testable, readable. (An excerpt.)
post_process : Varyings, Uniforms -> Glsl.Vec4
post_process = |frag, settings| {
	wave = (frag.fragTexCoord.y * 28.0 + settings.time * 2.0).sin() * 0.004
	shifted = Glsl.Vec2.({ x: frag.fragTexCoord.x + wave, y: frag.fragTexCoord.y })
	color = settings.texture0.texture(shifted) * frag.fragColor
	...
}

# An ordinary test (simplified): a Sampler holds a function, so a test supplies one colour.
expect post_process(frag, { texture0: flat(opaque_blue), time: 1.0 }).a == 1.0

# The translator. Runs during `roc build`; `fragment.source` is a Str constant.
#   Glsl.fragment_330 : Code(f) -> Try(Fragment, Error)
#   Fragment := { source : Str, bindings : List(Binding) }
Glsl.fragment_330(post_process)
#   #version 330
#   in vec4 fragColor;
#   in vec2 fragTexCoord;
#   uniform sampler2D texture0;
#   uniform float time;
#   out vec4 finalColor;
#   void main() {
#   	vec4 n20 = (texture(texture0, vec2((fragTexCoord.x + (sin(((fragTexCoord.y * 28.0) + (time * 2.0))) * 0.004)), fragTexCoord.y)) * fragColor);
#   	vec3 n36 = ((vec3(sin(time), sin((time + 2.1)), sin((time + 4.2))) * 0.08) + 0.92);
#   	finalColor = vec4((n20.r * n36.x), (n20.g * n36.y), (n20.b * n36.z), n20.a);
#   }
```

The two parameter records are the interface. The first holds the varyings, so
its fields become `in` lines; the second holds the uniforms, so its fields
become `uniform` lines; and the return type becomes `finalColor`. `bindings`
reports every one, so a renamed field fails the build and not the first
`Draw.Shader.uniform_f32!` call. Nothing new reaches the platform or the host.
`color` is read four times and `pulse` three, and each is one GLSL local,
because the description keeps shared work shared. The same shader as a library
DSL, `examples/reifying/shaders-without-reifying/`, emits the texture fetch four
times.

### 14.2 A CUDA kernel and a pushed-down query, case 11.2

The lowering is the same idea against a different text format. What differs is
that the output cannot run by itself: somebody has to own the driver, and a
driver is I/O, so the platform owns it.

The kernel is a sketch. The prototype has no CUDA translator, and its API is
whatever its author writes.

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
driver, and it is the clearest demonstration of what section 7.1 claims.
`examples/reifying/sql/` is the working version: a shop's schema, migrations,
seed rows and queries, every clause a Roc function over a plain record.

```roc
premium =
	Sql.from(products)
		.filter(|p| p.price >= 20 and p.title != "Gift card")
		.select(|p| { title: p.title, price: p.price, with_tax: p.price * 1.2 })
		.order_by(|r| r.price, Desc)
#   at compile time:
#   SELECT products.price AS price, products.title AS title, products.price * 1.2 AS with_tax
#   FROM products
#   WHERE (products.price >= 20.0) AND (products.title <> 'Gift card')
#   ORDER BY price DESC;
```

A named function works the same way. `bulk_lines` filters with `bulk_purchase`,
which calls `is_bulk`, and selects with `report_line`, which calls `line_total`.
The application calls the same functions on rows it holds, so one definition of
`line_total` has two executions and a test that they match. The example has no
database driver. `check.py` runs the printed script on SQLite and requires the
rows to agree with the ones Roc computes.

One predicate. It runs in the database when used in a query and in the process
when called directly, and there is exactly one definition to test. No ORM
expression builder, no string SQL, no second language.

### 14.3 An incremental view over DBSP, case 11.3

DBSP is an incremental view maintenance engine. A query is defined once over
collections, and the engine keeps its answer current under insertions and
deletions by computing the change rather than the answer again, at a cost
proportional to the change rather than to the data.

`examples/reifying/dbsp/` is the working version. `Dbsp.roc` holds the builder
and the translator, `main.roc` two views over sensor readings, and
`expected_output.rs` the Rust program they become. Every combinator that takes a
function takes it as a `Code(f)`, and a relation is a `Dbsp.Rel(row)`.

```roc
readings : Dbsp.Rel(Reading)
readings = Dbsp.input("readings")

# The translator lowers these lambdas; the combinators build the circuit.
alerts : Dbsp.Rel(Alert)
alerts =
	readings
		.filter(|r| r.celsius > 80.0)
		.key_by(|r| r.sensor)
		.count()
		.filter(|(_, n)| n >= 3)
		.map(|(sensor, n)| Alert.({ sensor, breaches: n }))

program : Try(Str, Dbsp.Error)
program = Dbsp.circuit([Dbsp.view("alerts", alerts), Dbsp.view("breaches", breaches)])
```

`Dbsp.circuit` returns one Rust source string: the struct of every row type with
the derives `dbsp` needs, and a `build_circuit` function. An excerpt:

```rust
let (readings, readings_handle) = circuit.add_input_zset::<Reading>();
let alerts = readings
    .filter(|row| row.celsius > F64::new(80.0))
    .map_index(|row| (row.sensor.clone(), row.clone()))
    .aggregate_linear(|_| 1i64)
    .map(|(key, n)| Tup2(key.clone(), *n))
    .filter(|row| row.1 >= 3i64)
    .map(|row| Alert { breaches: row.1, sensor: row.0.clone() });
```

The engine is a library with its own operators and its own way of describing a
circuit over them. The translator's job is to read the `Code(f)` of each lambda
and say the same thing in that vocabulary: the combinators fix the topology, and
reification supplies the expressions it is built out of. `main.roc` also has a
pure-Roc reference engine that calls the very functions the circuit was built
from, and checks the incremental answer of three batches, the last a deletion,
against a recomputation from scratch. A join, a helper function called by a
lambda, and four refusals each name the stage and the construct
(`examples/reifying/dbsp/README.md`).

The Rust is not compiled by the example or by CI, and every name it uses was
written from the crate's documented shape, with two assumptions the README
records. The executor is native and does not finish at build time the way a
shader compiler does, so some platform has to carry the engine. Reification
lowers the lambdas and stops there. Section 11.3 covers what carrying the engine
means, and why a platform extension mechanism would let any app use it rather
than only the apps built on a dedicated platform.

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

1. The normal form stabilizes on the boundary of section 10, declared as the rule it
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
