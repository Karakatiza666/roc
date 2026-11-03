# Intrinsics: Functions That Exist Only in Reified Code

Status: proposal. Baseline: branch `reify` at `781bffdce6`. Paths are relative
to the repository root. Probes ran with `zig-out/bin/roc` of that tree. The
probe files are in
`/tmp/claude-1000/-home-george-dev-Karakatiza666-roc/c5b3e2c3-6b59-4b5a-920a-94563ad8d06c/scratchpad/tonly/`
(`a/`, `g/`, `sur/misuse.roc`, `err.roc`).

Companion documents: `docs/langref/reifying.md` (the user page),
`roc-reify-opaque-proposal.md` (primitives of opaque types, `Code.prim`,
evidence), and design.md "Code Reification" (`design.md:23746`).

## 0. Summary

| # | Decision |
|---|---|
| D1 | An _intrinsic_ is a declaration with a full type signature and no Roc body, outside a platform module. It checks, infers, shows in the LSP and takes part in dispatch like any function. At every `Code` site it is a `Prim`, whatever the translator's cut says, and `Code.prim(f)` gives its id. |
| D2 | A body that is described and never run is _description-only_: the lambda written at a `Code` place, and the lambda a template returns. Only a reference outside such a body can run. |
| D3 | A definition is _reify-only_ when code of its that can run reaches an intrinsic: by naming one, by naming a reify-only definition, or by a method dispatch whose target is one. The rule is inferred and never annotated. |
| D4 | The generic case is decided where the checker already resolves each dispatch on a concrete type. Each constraint carries whether its source is description-only, and each `where` requirement of a scheme carries whether run-time code of the function uses it. A generic function is reify-only at an instantiation exactly when a requirement that it uses at run time resolves there to a reify-only target. |
| D5 | A program root that reaches a reify-only definition, at a reference outside a description-only body, is the compile error `exists only in reified code`. The roots are a provided entry point, a top-level constant and a top-level `expect`. The error is at the reference and names the chain to the intrinsic. Like any Roc error, a dev run continues and crashes only if it reaches the reference, and `roc build` exits 1. |
| D6 | All of it lives in the checker. It reads only the data checking already records, writes new bits into the checked artifact, and mutates no solved type. Post-check stages never see a reference to an intrinsic. |
| D7 | `Code.Op.Prim` gains `body : [Roc, Intrinsic]`. Translators bind intrinsics by id, as they bind builtins. `roc docs` and `roc check --intrinsics` list every intrinsic. |
| D8 | Surreal: the 64 `crash "… database only"` functions become intrinsics, and so do `Hit` and `Near`, whose backing becomes `[]`. `check.py` gets the columns that read an intrinsic from the translator and stops using `-- ignore:`. |

## 1. Problem

A translator target can have operations that Roc has no meaning for. In the
SurrealDB example, they are the search score and highlights (`Hit.score`,
`Hit.highlight`, `Hit.offsets`), the KNN distance (`Near.distance`), session
values (`Auth.access`, `Auth.expires`, `Table.auth`), database state
(`Table.rows`), the clock (`Time.now`) and randomness (`Rand.*`,
`Hash.argon2`). There are also pure SurrealQL functions that nobody has
written in Roc yet: `Text.is_email` and the other `string::` validators,
`Hash.md5`, `Math.median`, `Geo.*`, `Time.plus`. In total, 66 `crash "…runs in
the database only"` bodies over 65 functions (`examples/reifying/surreal/Surreal.roc:521-1210`).
`Analyzer.tokens` is a real function that crashes outside its domain, so it
stays as it is. That leaves 64.

Each of the 64 needs a body today, because an annotation without one is an
error at every reference (probe `nobody/`). So each has a `crash`, and misuse
fails only when the program runs:

| Use outside a clause | Today (probe `sur/misuse.roc`) |
|---|---|
| `Surreal.Text.is_email(s)` with a run-time `s` | no report. It crashes when reached. |
| `Surreal.Math.median([1.0, 2.0])` | `compile time crash`, only because the argument happens to be a constant |
| `expect` that calls one | fails when `roc test` runs it |
| The Mirror calling a clause that uses one | crashes. So the reference is written by hand and the column goes in `-- ignore:` (`search.roc:150`, `:186`). |

The ordinary functions that a translator reads by name also need an entry in
the cut (`Surreal.roc:3606`), because their types don't name an opaque type.

## 2. Facts the Design Rests On

### 2.1 A `Code` can't be run

| Probe | Result |
|---|---|
| `call_it = \|code, x\| code(x)` with `code : Code(I64 -> I64)` (`a/q.roc`) | `not a function`: "The code value is not a function, but it was given 1 argument" |
| The `Code` API (`src/build/roc/Builtin.roc:23625`) | `graph`, `version`, `is_eq`, `to_hash`, `bound` and `refuse_at` on a `Code`, plus `proxy`, `prim`, `type_id` and `ty_of`. There is no `run`. |

The lambda written at a `Code` place is never lowered either. Lowering
"restores the stored node as a constant … It walks no function"
(`design.md:23760`). A `Code.Bound` site (`select_where`, captured values)
computes only its inputs at run time. The translator runs once, at compile
time (`docs/langref/reifying.md`, "Captured Values").

### 2.2 The Mirror calls the named function

The Mirror runs the named Roc function that was also passed at the `Code`
place: `Surreal.Mirror.literal(seed_charts.map(measures))` (`search.roc`).
`Mirror.notices` takes plain `(row -> Bool)` and `(row -> out)` functions
(`monitoring.roc:540`, `DecodeTest.roc:217`). The GLSL `Interp.run(Code.graph(f), ..)`
is a translator of the graph, not a call. So "running a reify-only `Code`" is
always a run-time reference to a named function, and D5 reports it at that
reference.

### 2.3 Where reification errors are reported

The Description stage runs inside checked-artifact publication
(`reifyStagedCode`, `src/check/checked_artifact.zig:39310`, called from
`publishFromTypedModule`). That is after solving and before every post-check
stage. A refusal is a `staged_code` problem, and "its site becomes a
`runtime_error` exactly like one checking poisoned" (`design.md:23759`). That
includes reports at a use, such as `cannot bind inputs in a generic
function`. No user error is reported later. In particular, "no reference to a
valueless declaration survives checking" (`design.md:3887-3898`).

### 2.4 The checker resolves every dispatch on a concrete type, and already rejects a valueless target

When a static-dispatch constraint's dispatcher is a concrete nominal type,
the checker looks up the method (`lookupStaticDispatchMethodBinding`,
`src/check/Check.zig:49795`) and then calls `rejectValuelessMethodDispatch`
(`Check.zig:49838`, `:50106`, defined at `:34244`). For an annotation-only
target, that reports `annotation_only_value_use` at the constraint's source
expression and poisons the constraint. The checker records the selection as
dispatch evidence. Each generic instantiation site carries one
`CheckedEvidence` per method requirement, in scheme order (`design.md:7260-7267`).
Its resolution is `direct` (an exact target, with nested evidence),
`constraint` (forwarded to a requirement of the enclosing function), or
`structural` (a derived method), among others
(`src/check/static_dispatch_registry.zig:1614`). The reifier reads this
evidence and plans nothing (`src/check/code_reifier.zig:7403`).

Probes in `g/`, with `T := {}.{ now : T -> I64 }` (no body):

| Program | Report |
|---|---|
| `inner : a -> I64 where [a.now : a -> I64]`, `inner = \|x\| x.now()`, `outer = \|x\| inner(x) + 1`, and `outer(t)` in `main!` | `reference has no value` at `outer(t)`, the concrete site, through two generic functions (`g/p.roc`) |
| `U := {}.{ is_eq : U, U -> Bool }` (no body), and `[u] == [u]`, and `same = \|a, b\| { k: a } == { k: b }` called as `same(u, u)` | `reference has no value` at both: through `List`'s derived equality, and through a record's derived equality in a generic function (`g/s.roc`) |
| `Ops.count(\|t\| T.now(t) + 1)`, and `Ops.count(\|t\| inner(t) + 1 + T.ok(t))` | `reference has no value` inside both clauses (`g/d.roc`). This is what D3 changes. The second report points at `T.ok(t)` rather than at `inner(t)`, which is a region bug in today's report. |
| `Code.prim(T.now)` | `not a definition` (`g/c.roc`). D1 changes it. |

So the only point where a generic function's `where` requirement meets a
concrete method is already in the checker, before post-check. It covers
generic chains and derived methods, and it already knows the target is
bodyless.

### 2.5 How errors behave in each build mode

Probe `err.roc`, with a type error in a branch that runs only with six
arguments:

| Command | Behaviour |
|---|---|
| `roc check` | reports, exit 1 |
| `roc file.roc` | reports, runs, and crashes with `runtime error` and a backtrace only if it reaches the place. Exit 1. |
| `roc build --opt=speed` | reports, writes the binary, exit 1 |
| `roc test` | an `expect` with an error counts as failed |

## 3. Design

### 3.1 Intrinsics

An intrinsic is an annotation-only declaration (`e_anno_only`, `design.md:3887`)
in a module that isn't a platform's. A platform module's annotation-only
declaration stays hosted.

```roc
Text :: {}.{
	## `string::is_email`. An intrinsic: no Roc body.
	is_email : Str -> Bool
}

Hit :: [].{
	## `search::score(1)`: the BM25 score of the row.
	score : Hit -> F64
}
```

- **Checking.** The type is used as written. The warning `declaration has no
  value` isn't given for an intrinsic. The reference error `reference has no
  value` is replaced by D5.
- **Reification.** An intrinsic is a `Prim` at every site, whether or not the
  site's cut lists it. Listing one in `code_primitives` is the existing error
  `already a primitive`. Its `Prim` carries `id`, `evidence` (from its own
  `where` clause, if any) and `body: Intrinsic`. An intrinsic read as a
  value inside a clause (`xs.map(Text.is_email)`) is refused, as a function
  of an opaque type used as a value is today (reifying.md, "What Is Refused
  and Why").
- **Identity.** `Code.prim(Text.is_email)` gives its `Code.PrimId`, keyed by
  the declaration like any other.

### 3.2 Description-only bodies

A body is description-only when it is:

- the body of a lambda written at a `Code` place, or
- the body of the lambda a template returns,

and every lambda nested in one of those. The checker knows each before it
checks the body. A lambda at a `Code` place takes its parameter types from the
call before its body is checked (reifying.md, "How a Function Becomes a
Code"), and checking records the site (`CodeReificationSite`, `stagedCode` in
`src/check/Check.zig`).

A name written *as* the `Code` argument (`select(ranked)`) is also
description-only. It describes `ranked` and doesn't run it.

### 3.3 Reify-only definitions

A reference is _run-time_ when it is outside every description-only body.
These are the rules:

| Rule | A definition `d` is reify-only when |
|---|---|
| R1 | a run-time reference in `d` names an intrinsic |
| R2 | a run-time reference in `d` names a reify-only definition |
| R3 | a run-time dispatch in `d` on a concrete type selects an intrinsic or a reify-only method (section 3.4) |

A reference covers a call, a value use (`xs.map(helper)`, `{ f: helper }`)
and a method call. Within one group of mutually recursive definitions, the
bits are the least fixed point. Each reify-only definition records one
_witness_: the reference that made it reify-only. The message prints the
chain from these witnesses.

A reify-only definition that only description-only bodies reference is
fine. It is walked by its body like any helper, and nothing lowers it. A
reify-only definition that nothing references is dead code, which is no
error.

### 3.4 The generic case

A `where` requirement is only matched to a method when a use fixes the
dispatcher's type. The rule follows the requirement to that point. Two bits,
both computed at constraint generation and carried with the data they
describe:

| Bit | On | Set when |
|---|---|---|
| `described` | each static-dispatch constraint | its source expression is in a description-only body, or it was instantiated from a requirement whose `runtime` bit is clear, or at an instantiation site that is itself described |
| `runtime` | each scheme requirement of a generic definition | at least one constraint generalized into it is not `described` |

At the resolution point of section 2.4, where `rejectValuelessMethodDispatch`
stands today, the checker has the constraint, the selected target and the
site's definition:

- If the target is an intrinsic, or a reify-only definition, and the
  constraint isn't `described`, the definition of the site becomes reify-only
  (R3), with this dispatch as its witness.
- If the constraint is `described`, nothing happens. The reifier will read the
  same evidence, and the target becomes a `Prim`.
- If the dispatcher is still a type variable, the constraint generalizes into
  a requirement of the definition. Its `runtime` bit carries the decision to
  the next use, exactly as the requirement itself is carried.

A target's own requirements, and a derived method's component methods, are
resolved at the same point (verified for `List` and record equality in
section 2.4). They inherit `described` from the constraint that reached them.

Why this is exact for generic functions:

- A generic function is reify-only *at an instantiation* when, and only when,
  a requirement it uses at run time resolves there to a reify-only target.
- Its other instantiations are unaffected. A clause that is generic over a row
  or a context type runs in the Mirror at a type whose methods have bodies.
- A requirement that the function uses only inside a description-only body
  (the lambda of a query fragment, say) never makes a run-time use reify-only.

This needs no step after checking. The selection is the checker's, made where
`missing method` and `reference has no value` are reported today. How
publication later stores nested evidence (`EvidenceNested.from_callable`,
`static_dispatch_registry.zig`) doesn't matter, because the decision has
already been taken.

| Case | Result |
|---|---|
| `hot = \|s\| Text.is_email(s)`, used only inside clauses | `hot` is reify-only. Every reference to it is description-only, so there is no error. |
| `hot(name)` in `main!` | error at `hot(name)` |
| `select(ranked)`, where `ranked` uses `hit.score()` | fine: the argument is description-only |
| The Mirror: `seed.map(ranked)` | error at `ranked` |
| `outer(t)` in `main!`, where `outer` calls the generic `inner`, which calls `x.now()`, and `T.now` is an intrinsic | error at `outer(t)`. The chain is `outer`, then `inner`, then `T.now` on a `T`. |
| `Ops.count(\|t\| outer(t))` | fine: the constraint is `described` |
| `outer(m)` with a type `M` whose `now` has a body | fine |
| A query fragment `named_only = \|q\| q.filter(\|x\| Text.is_email(x.e))` called at run time | fine: the reference is in a description-only body, and each use is described as today |
| A fragment whose row requirement (`x.t.now()` inside the filter lambda) resolves to an intrinsic at `named_only(pets)` | fine: the requirement's `runtime` bit is clear |
| A template `add_k = \|k\| \|x\| x.now() + k` | the returned lambda is description-only. A reference in the template body outside it runs during compile-time evaluation, so it counts as run time. |
| `before = \|c\| Surreal.select_where(t, \|e\| e.at < Surreal.Time.now() and e.n > c)` | fine: only `c` is computed at run time |
| `limit = Text.is_email(x)` outside the lambda, captured by it | error at `Text.is_email`: the capture is computed at run time |
| `[h] == [h]` with `h : Hit`, if `Hit.is_eq` were an intrinsic | error through the derived `List` equality, at the `==` |
| `doubler = make(2.0)`, with `make = \|k\| \|x\| Text.is_email(x)` | `make` is reify-only, so the top-level constant is an error, although evaluating it calls nothing. See open question 2. |

### 3.5 Roots and the error

A _root_ is a definition whose code runs whatever references it: a provided
entry point or platform requirement (`main!`), a top-level constant (which
compile-time evaluation runs), and a top-level `expect`. A run-time reference
or dispatch in a root that reaches a reify-only definition or an intrinsic is
the error. It is reported at that reference, and the expression is poisoned
as `annotation_only_value_use` poisons it today. So the reference lowers to a
crash, and nothing behind it is lowered.

```
── ✗ exists only in reified code ──────────────────────────── main.roc:13:11

This call runs when the program runs, but it reaches an intrinsic, which has
no Roc body:

    echo!("${outer(t).to_str()}\n")
             ^^^^^^^^

    outer calls inner at main.roc:6:13
    inner calls now on a T at main.roc:4:13
    T.now is an intrinsic at T.roc:2:2

An intrinsic exists only inside a function that a translator describes. Pass
the function where a Code is expected, or give T.now a Roc body.
```

For the Mirror, the first line says `ranked is used here as a value`, and the
chain ends at `Surreal.Hit.score`.

### 3.6 Build modes

The error is an ordinary error in every mode (section 2.5). `roc check`
exits 1. A dev run continues and crashes only if it reaches the reference.
`roc build` writes the binary and exits 1. `roc test` counts the `expect` as
failed.

### 3.7 Where the checks live

| Piece | Stage | Reads | Writes |
|---|---|---|---|
| Intrinsic | canonicalization | the declaration has no body, outside a platform | the existing `e_anno_only` |
| Description-only bodies | checking | `Code` places and template results, before the body is checked | `described` on each constraint generated in them |
| R1, R2 | checking, after each group of mutually recursive definitions | lookups and their `described` positions | the definition's `reify_only` bit and witness |
| R3 and requirement bits | checking, at dispatch resolution (`Check.zig:49838`, `:50106`) and generalization | the constraint, the selected target, the target's `reify_only` bit | the definition's bit, and `runtime` on each scheme requirement |
| Cross-module | checked artifact | the bits above | exported with each definition, and with each requirement in the imported scheme (the scheme cache copies requirements with the type, `design.md:7280-7289`) |
| Roots | checking | entry points, constants, `expect`s | `exists only in reified code`, and a poisoned expression |
| `Prim` | Description (`code_reifier.zig`) | `e_anno_only` target | `Prim` with `body: Intrinsic` |

This fits AGENTS.md and design.md:

- Every input is data that an earlier step recorded explicitly. Nothing is
  guessed from names or shapes.
- The bits are side data on constraints, requirements and definitions. No
  solved type, redirect or dispatch plan changes, so "Solver-Mutating
  Rewrites" doesn't apply and no `RedirectRule` is needed.
- The error is reported before post-check, and the poisoned reference is the
  one form post-check sees.
- Two compiler invariants, each a debug assertion in debug builds and
  `unreachable` in release builds:
  1. Monotype lowering never reaches an intrinsic.
  2. The reifier never asks for an intrinsic's body.

## 4. Translators and Tools

**Binding.** A translator binds an intrinsic as it binds a builtin, by id in its
extension table:

```roc
{ prim: Code.prim(Text.is_email), form: Function({ surql: "string::is_email", random: Bool.False }) }
```

An intrinsic that no extension binds is an unknown `Prim`, which the
translator refuses by name. That is the same rule as for every other `Prim`.
`body: Intrinsic` on the `Prim` tells a translator that a column has no Roc
meaning (section 5.2). A graph interpreter, such as the GLSL `Interp`, uses it
to refuse with a precise reason.

**Listing.** The declaration is the marker, so every listing is exact:

| Tool | Gives |
|---|---|
| `roc docs` | each intrinsic badged "intrinsic: no Roc body" |
| `roc check --intrinsics` | each intrinsic of the checked modules, with its file and line. This is a plain flag, so it needs no environment variable. |
| A translator's coverage test | the intrinsics its extension table doesn't bind, from the `Prim`s with `body: Intrinsic` in its test sites |
| The LSP | the same badge on hover |

Giving an intrinsic a body later is a local change. Its id stays, because it
is keyed by the declaration. Its callers stop being reify-only, and their
Mirror calls compile. The Roc meanings can then be written one at a time, from
the listing.

## 5. Surreal Migration

### 5.1 The package

| Change | Where |
|---|---|
| Delete the `crash` body of each of the 64 functions. Change "Database only" in their docs to "An intrinsic: SurrealDB computes it". | `Surreal.roc:521-1210` |
| `Hit :: []` and `Near :: []`. The pair `(row, Hit)` stays, because it carries which search the row came from. | `Surreal.roc:1071`, `:1091` |
| Remove the intrinsics from `cut`. They are primitives everywhere, and listing one is `already a primitive`. | `Surreal.roc:3606` |
| No change to rendering. The ids come from the same declarations, and the extension table already binds them. | `Surreal.roc:3700-3713` |
| The rule that `rand::` appears only in a default, a computed field or an update stays in the translator. | `Translate.roc` (`random`), `SchemaTest.roc:182-183`, `:794` |
| Update the README rows that say "a `crash` in Roc". | `README.md:1223` and the function tables |

Clauses don't change. A named clause that uses an intrinsic can no longer be
passed to the Mirror, which is now a compile error. The blocks that use
intrinsics already compare with handwritten literals.

### 5.2 `check.py`

1. The translator knows which output columns read a `Prim` with `body:
   Intrinsic`. `Prepared` exposes them as `intrinsic_columns()`.
2. `block` writes `-- intrinsic: score, marked` from that list.
3. `check.py` drops a listed column that the literal leaves out, and compares
   one that the literal has. So `marked` (a highlight written by hand) stays
   compared.
4. A literal that leaves out a column that isn't listed is a failure, so no
   column is ever ignored silently.

`-- ignore:` and its two uses (`search.roc:150`, `:186`) are deleted.

## 6. Staging

| Stage | Work | Tests |
|---|---|---|
| 1 | Compiler: intrinsics, `Code.prim` of one, the `Prim` classification with `Prim.body`, description-only bodies, R1-R3, the two bits, roots, `exists only in reified code`, the exported bits, the two invariants. A new "Intrinsics" section in `docs/langref/reifying.md`, with the new report in "Every Report", and the invariants in design.md "Code Reification". | CLI tests for both sides of each row of the table in section 3.4, in one module and across a package |
| 2 | Tools: `roc docs` badge, `roc check --intrinsics`, LSP hover | snapshot of the listing |
| 3 | Surreal package (section 5.1) | the example's tests; misuse probes as checked failures |
| 4 | `check.py` (section 5.2) | a run against SurrealDB |
| 5 | Roc bodies for the pure SurrealQL functions (`median`, `Time.plus`, the `string::` validators), one at a time, from the listing. Low priority. | each one's Mirror block |

## 7. Open Questions

1. **The marker.** A bodyless declaration outside a platform becomes an
   intrinsic. A body that was simply forgotten is then still caught at every
   run-time use, but no longer at the declaration. Is that acceptable, or
   should the module also list its intrinsics (for example in a
   `code_intrinsics` item)?
2. **A function-valued constant.** `doubler = make(2.0)` is an error when
   `make` returns a closure over an intrinsic, although evaluating it calls
   nothing. The definition-level rule over-approximates here, and reports
   an error for a program that would have worked. Making it exact needs
   reify-only-ness on function types, as effects are on `=>`. Is the
   over-approximation acceptable for the first version? The workaround is to
   write the closure where it is used.
3. **Intrinsics in an app.** Should an app module be allowed to declare one, or
   only a package?
