# Opaque Types in Code Reification

Status: proposal, revision 2. Baseline: branch `reify` at `7c2194ddca`. All
`path:line` references are relative to the repository root at that commit.
Probes ran with a debug compiler built from `f0e659f0` (same branch, two
commits earlier).

Companion documents: `roc-reify-proposal.md`, `roc-reify-normal-form.md`,
`roc-reify-normalization-plan.md`, and design.md "Code Reification"
(`design.md:23589`).

Revision 2 applies four decisions from the user. The first three replace the
matching parts of revision 1. The fourth (constrained generic primitives,
section 3.7) is new:

| Revision 1 | Revision 2 |
|---|---|
| Builtins and package opaque types share a concept but keep two code paths. The consumer's `code_primitives` declares which opaque operations it knows (`Prim` versus a new `Undeclared` op). | One mechanism. An opaque type declares its own primitives, as `Builtin.roc` does for `Str`. The consumer's `code_primitives` no longer lists operations of opaque types. No `Undeclared` op. |
| A captured opaque value needs an explicit `Code.input(x)`. | No user annotation. The translator states, on its `Code` parameter, the encoding format it needs. The checker requires that format's `encoder_for` of each capture while it checks the site. |
| A glue type declares a translator's cut. | A translator accepts extensions at run time. An extension names a primitive by the function itself (`Code.prim(Time.is_before)`) and an opaque type by a type identity. |
| (not covered) | A generic primitive with a `where` constraint can be listed, and its call carries the method the checker chose for each constraint. |

## 0. Summary

| # | Decision | Ships in |
|---|---|---|
| D1 | A primitive is an operation of a type that hides its representation. The builtin module declares its primitives (every builtin function, as today). A package opaque type declares its primitives implicitly: every function or constant of its module whose checked type mentions it. One classification step serves both. | Stage 1 |
| D2 | Laws stay builtin-only. A package primitive is uninterpreted: no folding, no law, not speculatable. | Stage 1 |
| D3 | `code_primitives` stays, for functions that are not primitives of their type: items of transparent nominals and free functions (the GLSL `Vec3.scale` case). Its entries become `Code.prim(f)` and the item a `List(Code.PrimId)`, so a generic entry with a `where` is legal. Listing a builtin or an opaque operation is a compile error. | Stage 1 |
| D4 | Every primitive and every opaque type has an exact identity. `Code.Op.Prim` gains `id : Code.PrimId`; `Code.Ty.Opaque` gains a `Code.TypeId`. Builtin `Prim` names do not change. Internally the IR keys on the declaring module's identity, so two packages' `Time` never merge. | Stage 0 (internal), Stage 1 (API) |
| D5 | A translator that binds captures writes its parameter as `Code.Binds(Code(f), fmt)`. For each capture read in the lambda, the checker adds the ordinary requirement `t.encoder_for : fmt -> (t, List(U8) -> Try(List(U8), []))` while it checks the site. An opaque capture becomes an input slot whose run-time value is `Code.Value.Encoded(bytes)`. A transparent capture is described and bound as today. This is a typing rule, implemented by constraint generation; "Solver-Mutating Rewrites" does not apply (section 3.5.6). | Stage 2 |
| D6 | Third-party extension: `Code.prim : f -> Code.PrimId` and `Code.type_id : Code.Proxy(t) -> Code.TypeId` give exact identities from the function or type itself. A translator that allows extensions takes a list of them at run time and matches `Prim.id` and `Opaque` type ids against it. | Stage 1 (API), Stage 3 (example) |
| D7 | A call of a constrained generic primitive (builtin `List.sort`, `Dict.get`; a package `Time.max_in(zone)`; a cut member) carries `evidence`: for each `where` requirement of its scheme, the method the checker chose at this call, as a primitive id, a row of the graph, or a derived method. The walk reads the checker's recorded evidence; it plans nothing. | Stage 1 |

Thesis points from the first task, and where they ended:

| Thesis claim | Result |
|---|---|
| The opaque boundary is an implicit cut | Holds, with the module and signature rule (D1). Ownership alone fails: void modules are opaque types (`docs/langref/modules.md:96-102`). |
| `Prim` identity is (package, module, type, method) | Holds as an exact identity value (D4), not as text. Roc has no stable package name (`src/check/checked_artifact.zig:279-287`). |
| A captured opaque value is an abstract bound value handled through `where` | Holds in a changed form: the translator names a format; the checker requires `encoder_for` in it (D5). A run-time handle needs an existential type, which Roc does not have. |
| `Code.Ty` carries the identity | Holds (D4). `where` evidence cannot flow through `Ty`, which is data at compile time. |

## 1. Problem and Evidence

A `Code(f)` parameter makes the compiler describe a lambda as a `Code.Graph`.
A translator reads the graph. Today a type has two answers: show the structure,
or refuse. An opaque type (`::`) hides its structure, so most uses refuse. A
package author who wants reified code to use the type must expose the
representation with `:=`.

Concrete case: date and time packages (roc-time, gregorian) use opaque types.
An ORM filter `|r| r.at < cutoff` with a captured `cutoff` is refused.

### 1.1 Probe Results

Probe: a type module `Time :: { nanos : I128 }` with `from_nanos`, `to_nanos`,
`is_lt`, `is_before`, `is_eq`, a constant `epoch`, a constant `days_in_week : U8`,
and a derived `encoder_for`. A printer like the one in
`test/cli/StagedNominalMethods.roc:9-104` shows each description.

| Written (`r : { id : I64, at : Time }`) | Result today |
|---|---|
| `\|r, c\| r.at < c` | `Time.is_lt(p0.at, p1)` |
| `\|r, c\| r.at.is_before(c)` | `Time.is_before(p0.at, p1)` |
| `\|r, c\| r.at == c` | `Time.is_eq(p0.at, p1)` |
| `\|r\| r.at` | `p0.at`, type `Time` |
| `\|r\| r.at.to_nanos()` | `Time.to_nanos(p0.at)` |
| `\|r, c\| Time.is_before(r.at, c)` (direct call) | refused: "a record of this type" |
| `\|r\| r.at < cutoff`, top-level `cutoff = Time.from_nanos(5)` | refused: "a record of this type" |
| `\|r\| r.at < Time.from_nanos(7)` | refused: "a record of this type" |
| `\|r\| r.at < Time.epoch` | refused: "a record of this type" |
| `Binder.bind(\|t\| t < limit)` at a `Code.Bound` site, `limit : Time` captured | refused: "a captured value of an opaque type" |
| `x.a < y.a and x.b < y.b`, `a` from package `pa`, `b` from package `pb`, both type modules `Time` | `and(Time.is_lt(p0.a, p1.a), Time.is_lt(p0.b, p1.b))`, both types spelled `Time` |
| nested `Cal.Time` and `Clock.Time` | `Cal.Time.is_lt(..)`, `Clock.Time.is_lt(..)` |
| `\|x\| Util.double(x) + 1`, `Util :: [].{ double }` | walked: `Num.I64.plus(Num.I64.times(p0, 2), 1)` |
| `\|d\| d.get("a") ?? 0`, `d : Dict(Str, I64)` | `Dict.get(p0, 'a')`, type `Builtin.Dict(Str, I64)` |
| `\|s\| s.contains(3)`, `s : Set(U8)` | `Set.contains(p0, 3)`, type `Builtin.Set(U8)` |
| `\|b\| b.unbox() + 1`, `b : Box(I64)` | `Box.unbox(p0)`, type `Box(I64)` |
| `code_primitives = (Lib.max_by, ..)`, `max_by : List(a), (a -> k) -> Try(a, [Empty]) where [k.is_lt : k, k -> Bool]` | checker error at the entry: "missing method. This is_lt call is on a value of type k, which never resolved to a concrete type" (`Cut.roc:5:21`); the whole cut is then lost, so `first_of` in the same list is walked |
| `\|xs\| Lib.max_by(xs, \|x\| x)` with no cut | compiler crash: "code reifier invariant: normalization broke an invariant of the normal form" (`src/check/code_reifier.zig:8670`, from `src/reify/driver.zig:788`) |
| `\|xs\| xs.sort()` at `I64`, at `Time` (opaque, written `order_relative_to`), at `Pt := { x : I64 }` whose written order is reversed | `List.sort(p0)` in all three; nothing says which order |
| `\|xs\| xs.sort_with(\|a, b\| a.order_relative_to(b))` | `List.sort_with(p0, closure r1())`, `r1 = Num.I64.order_relative_to(p0, p1)` |
| `\|d, k\| d.get(k) ?? ""`, `d : Dict(Time, Str)` | `Dict.get(p0, p1)`; the `is_eq` and `to_hash` it uses are not in the description |

### 1.2 Defects Found

| # | Defect | Evidence | Severity |
|---|---|---|---|
| F1 | Method-call form and direct-call form of one opaque operation differ: `t.is_before(c)` is a `Prim`, `Time.is_before(t, c)` is walked and refused. `roc-reify-normal-form.md:724-728` says the two forms give one `Prim` for a cut member. | probe rows 2 and 6 | inconsistency |
| F2 | Two distinct opaque types with one short name have one `Ty` and one `PrimId`. `Types.opaqueTy` interns by name text (`src/reify/types.zig:228-237`). `Builder.namedPrimWithRole` keys by owner and method text (`src/reify/builder.zig:1174-1187`). The digest hashes the text (`src/reify/digest.zig:464-469`). Value numbering (N5) can merge two calls of different packages' functions, and `Code` equality can call two different descriptions equal. | two-package probe | correctness |
| F3 | A cut or opaque `Prim` first consults the builtin table by name (`prims.findNamed`, `src/reify/prims.zig:318-326`, called from `src/reify/builder.zig:1175`). A package function whose owner and method spell a builtin entry would get the builtin's laws. | code reading | latent correctness |
| F4 | A refusal inside another module's body is reported at the same offsets in the site's module. Headerless app: the report names a file of the Echo platform. Package app: `main.roc:1:73` underlines the app header. design.md says a frame in another module names that module (`design.md:23704-23709`). | probes p1, p2 | diagnostics |
| F5 | Builtin opaque types are spelled two ways in `Ty`: `Builtin.Dict(..)`, `Builtin.Set(..)`, `Builtin.Hasher`, but `Box(..)`. Their `Prim` owners are `Dict`, `Set`, `Box`. | probe rows 14-16, `src/cli/test/parallel_cli_runner.zig:3457` | consistency |
| F7 | A generic function with a `where` cannot be listed in `code_primitives`. The item is an ordinary value: the tuple is checked as an expression, a value binding is not generalized (design.md "Value Bindings Generalize By Expression"), so the entry's requirement stays on an unsolved variable and the checker reports "missing method" at the entry. The reifier itself needs only the reference (`moduleCuts` reads the checked lookups, `src/check/code_reifier.zig:8894-8960`). No message with the text "sort constraint" exists in the checkout; this is the refusal the user saw. The SurrealDB example records the effect: "`Array.sort` is not available" (`examples/reifying/surreal/README.md`, findings table, at `2a442ad8fa`). | probe `max_by` | limitation |
| F8 | A call of a constrained generic primitive drops the checker's evidence. `List.sort` over `I64`, over an opaque `Time` and over a reversed `Pt` give one description, so a translator that maps `List.sort` to `ORDER BY` sorts `Pt` the wrong way and gives no error. `callExpr` returns the `Prim` (`src/check/code_reifier.zig:4600-4607`) before it reads the site evidence (`:4620`), which it reads only for a callee it walks. | probe `sort` | correctness |
| F9 | Walking `Lib.max_by` (a `fold` whose closure compares `key(best) < key(x)`) crashes the compiler with a broken normal-form invariant. Independent of the cut. The walk breaks the invariant, not a normalization rule: the checker's `row_coerce` lifts the fold's structural result `[Err([Empty]), Ok(I64)]` into `Try(I64, [Empty])`, and `exprAt` returned the value at its own type with no `Wrap`, so the verifier found a row whose value does not conform to its result. Every producer whose type is fixed elsewhere (a parameter, a local, a `Prim` result, a call, `[False, True]` read as `Bool`, a user nominal) had the same defect. | probe `max_by` | compiler crash |
| F6 | `docs/langref/reifying.md:250` says opaque types describe. Most uses are refused. The same sentence says captured run-time values are refused, but a `Code.Bound` site binds them (`design.md:23757-23796`), and the langref page does not document `Code.Bound`. | probes | docs |

## 2. Current Behavior

### 2.1 How the Walk Classifies a Callee

```
call in a described body
        |
        v
  builtin module? ---- yes ---> Prim, owner from export name
        |                       (Builtin.Num.I64.plus -> Num.I64 / plus)
        no                      except a first stage that walks a builtin
        |                       which hands back a function
        v
  method call whose receiver is a non-builtin opaque nominal?
        |  (dispatch path only)
        +---- yes ---> Prim, owner = short type name  [checked BEFORE the cut]
        no
        v
  in the site's explicit cut (code_primitives)?
        +---- yes ---> Prim, owner = qualifiedName
        no
        v
  walk the body, in any package (N8l)
        |
        v
  construction or backing read of an opaque nominal --> refused
```

| Step | Direct call path | Method call path |
|---|---|---|
| Entry | `callExpr`, `src/check/code_reifier.zig:4570-4620`; `calleeTarget` `:4962`; `resolvedTarget` `:5076` | `dispatchTarget` `:5543-5560`; `methodTargetCallee` `:5576-5630` |
| Builtin | `:5111-5116` (`providedName` `:5289`) | `:5596-5607` (`.provided`, `.here_builtin`) |
| Opaque receiver | none | `:5588-5594`: `nominal.is_opaque and nominal.builtin == null` gives `.foreign` with `typeNameText(nominal.name)` |
| Explicit cut | `:5117` (`inCut`) | `:5611` (`inCut`) |
| Walk | `:5120` onward | `:5612-5629` |

Derived methods on an opaque type are not walked either: a derived `==` gives a
`Derived` node (`nominalEq`, `:6046-6050`), and a derived `to_hash` stops
(`hashOver`, `:6164`).

### 2.2 How the Explicit Cut Resolves

| Stage | What it does | Where |
|---|---|---|
| Publication of the translator's module | For each `code_primitives` item of a nominal the module declares: each entry must be a lookup of a function defined as a lambda, listed once. Records the checked lookups in `CodeCutTable`. | `moduleCuts`, `src/check/code_reifier.zig:8894-8960`; problems `not_a_function`, `listed_twice` at `:8869-8885` |
| Resolve an entry | Follows aliases to the function's module, body and definition | `cutMember`, `:4413-4470` (imported case `:4459-4469`) |
| Site start | Finds the translator function the site is an argument of, its owning nominal, and that nominal's cut. Maps `(artifact, body)` to a name. | `Walk.useCut`, `:8539-8552`; `translatorFunction`, `:4478-4501` |
| Lookup | `(artifact, body)` key | `CutKey`, `:4404`; `inCut`, `:4563-4565`; `Walk.cut`, `:8391` |
| Name | The nominal the function is an associated item of and the item; for a non-item, the module and the definition | `qualifiedName`, `:4546-4559`; `ownerOf`, `:4532-4541` |

The cut is exact: it is keyed by the function's body, not by its name. Only the
name the translator sees is text.

### 2.3 How a `Prim` Is Named and Stored

| Item | Behavior | Where |
|---|---|---|
| `Code.Op.Prim` | `Prim({ owner : Str, method : Str })` | `src/build/roc/Builtin.roc:23974`; docs `:23931-23936` |
| Builtin table | Fixed entries with laws, speculatable flag, identities | `src/reify/prims.zig` |
| Named prim | Anything else: interned by `"owner\0method\0role"`, after a lookup in the builtin table by the same text | `src/reify/builder.zig:1167-1187`; `src/reify/ir.zig:544-549` |
| Name read back | `Store.primName` | `src/reify/ir.zig:695-699` |
| Speculatable | Named prims are not speculatable | `src/reify/builder.zig:2619-2623`; verifier `src/reify/verify.zig:374` |
| Rules | Laws, folding and evaluation read only table entries | `src/reify/laws.zig:206`, `:397`, `:418`; `src/reify/eval.zig:357` |
| Digest | Hashes owner and method text | `src/reify/digest.zig:464-469` |
| Emit | Writes `Prim({ method, owner })` | `src/check/code_emit.zig:249` |
| Builtin owner text for scalar `==` | `primitiveOwnerText` | `src/check/code_reifier.zig:7645-7680` |

### 2.4 How a Type Is Converted

| Checked type | `Code.Ty` | Where |
|---|---|---|
| builtin scalar, `Str`, `List` | its own constructor | `nominalTy`, `src/check/code_reifier.zig:6456-6474` |
| builtin `Try` | `Named` with backing | `:6470-6472` |
| builtin `Dict`, `Set`, `Box`, `Iter`, `Hasher`, SIMD, crypto | `Opaque(name, args)` | `:6473-6493` |
| user nominal with `::` | `Opaque(name, args)`; backing never read | `:6496-6498` |
| user nominal with `:=` | `Named(name, backing)`, or `Recursive(name)` | `:6499-6534` |
| `Opaque` interning | key is `(11, name text, args)` | `src/reify/types.zig:228-237` |
| `Opaque` emit | `Opaque(Str, List(Ty))` | `src/check/code_emit.zig:418`; `src/build/roc/Builtin.roc:23685-23691` |

`opaqueTy` names the type with `typeNameText(nominal.name)`
(`src/check/code_reifier.zig:6625-6629`). The checked nominal already carries
`origin_module` and `source_decl`, which `nominalInstanceKey` hashes
(`:6569-6582`). The exact identity exists. The `Ty` does not use it.

### 2.5 How a Value Is Described

| Source of the value | Description | Where |
|---|---|---|
| parameter, field of a parameter | `Param`, `Field` | ordinary walk |
| top-level constant | its definition, walked where the name stands | `foldedConstant`, `src/check/code_reifier.zig:2824-2844` |
| run-time capture at a `Code.Bound` site | `Input(k)` slot | `unboundRef`, `:2695-2711`; `inputSlot`, `:2719-2735` |
| run-time capture elsewhere | refused (`capture`) | `:2711` |
| value of an opaque type built in the body | refused: "a value of an opaque type" | `nominalExpr`, `:2617-2628` |
| opaque record literal in the type's own body | refused: "a record of this type" | `recordExpr`, `:2370-2384` |
| capture whose type holds an opaque type | refused: "a captured value of an opaque type" | `slotShape`, `:8003-8025` |

The program fills slots at run time. Lowering builds one `Code.Value` per slot
with a generated helper per Monotype type (`boundCodeValue`,
`src/postcheck/monotype/lower.zig:37039`; `codeValueBody`, `:37238-37300`). The
debug shape check uses `CodeValueShape` (`src/check/checked_artifact.zig:2529`).
`Code.Value` (`src/build/roc/Builtin.roc:24388-24403`) has no form for an opaque
value. Lowering can see an opaque backing (`codeValueBody` unwraps every
`.named`), so the refusal is a policy of the walk, not a limit of lowering.

### 2.6 Builtins Today

Builtins are a special case in three ways:

| Aspect | Builtin | Package opaque type |
|---|---|---|
| Boundary | always, except a first stage walks a builtin that hands back a function (`walksInline`, `:1524`; `open_builtins`) | dispatch form only (`:5588-5594`) |
| Name | export name minus `Builtin.` (`src/reify/prims.zig:334-347`) | short type name, or `qualifiedName` |
| Laws and folding | table entries (`src/reify/prims.zig`) | none |
| Uniqueness | one `Builtin` module, so unique | not unique (F2) |
| `Ty` | `Opaque("Builtin.Dict", ..)`, but `Opaque("Box", ..)` (F5) | `Opaque("Time", ..)` |

The SQL example keys rows on these names: `"Str.concat"`, `"List.map"`,
`"Try.is_ok"` (`examples/reifying/sql/Sql.roc:816-841`, `:848`). Its operator
table keys on the method alone for any owner (`Sql.binary`, `:894-901`;
`Sql.operator`, `:924-949`). So today `Prim({ owner: "Time", method: "is_lt" })`
silently becomes SQL `<`, whatever `Time` stores.

## 3. Design

### 3.1 D1: One Primitive Mechanism

A builtin is an opaque type whose operations the compiler already knows. A
package opaque type is the same thing with operations the compiler does not
know. Both are boundaries for the same reason: the walk must not read a
representation the type hides. So one step classifies every callee:

```
primitiveOf(definition) ->
  | the builtin module defines it                 -> primitive  (names: export name, unchanged)
  | it is an operation of a non-builtin opaque N  -> primitive  (names: qualifiedName)
  | otherwise                                     -> not a primitive

callee classification, the same in the direct-call, method-call and constant paths:
  primitive                       -> Prim { owner, method, id }
  in the translator's explicit cut -> Prim { owner, method, id }
  otherwise                       -> walk (in any package)
```

Operation of an opaque type. A function or constant `F` is an operation of `N`
when all of these hold:

| Condition | Data it reads |
|---|---|
| `N` is a nominal declared with `::` and is not a builtin | the declaration's opaque flag; `CheckedNominalType.builtin` |
| `F` is defined in the module that declares `N` | the module of the resolved definition (`cutMember`, `src/check/code_reifier.zig:4413-4470`; `methodDefinition`, `:5640`) |
| `F`'s checked type mentions `N` at any depth, including type arguments and function types | the checked type of `F`'s template |

How a type declares its primitives:

| Option | Decision |
|---|---|
| Implicit, by the rule above | Chosen. Every published opaque package works with no change, roc-time and gregorian included. An operation outside the rule (a void-module helper, `Time.days_in_week : U8`) is walked; if its body reads the representation, the walk refuses there, exactly as today. |
| Explicit list in the type's module (`Time :: ...{ code_primitives = (..) }`) | Rejected as the source of truth. A package that declares nothing would have no primitives, so every use would be refused. An operation left out that reads the representation is refused anyway. The one gain is a smaller vocabulary: an operation written through others (`is_gt = \|a, b\| b.is_lt(a)`) could be walked down to `is_lt`. That is an optional later narrowing (Q7), not the base rule. |
| Ownership only (every associated item) | Rejected: cuts every void-module helper. The probe shows `Util.double` is walked today. |

What the builtin module does under the same rule. It declares its primitive
set explicitly, by being the builtin module: every builtin function is a
primitive, as today. The first stage that walks a builtin which hands back a
function (`walksInline`, `src/check/code_reifier.zig:1524`) stays. It is part
of the builtin module's declaration: those bodies are compiler-owned and read
only types the normal form has (`Str`, `List`, `Try`). A package opaque
operation that hands back a function gets no such walk, because its body reads
the hidden representation (Q4).

Consequences:

| Case | After D1 |
|---|---|
| `Time.is_before(r.at, c)` and `r.at.is_before(c)` | one node, `Prim` (fixes F1) |
| top-level `cutoff = Time.from_nanos(5)` read in the body | the constant folds to its definition, `Prim from_nanos(5)` |
| `Time.epoch : Time` | `Prim` with no arguments |
| `Time.days_in_week : U8` | walked |
| `Util.double` in `Util :: [].{..}` | walked (unchanged) |
| `Cal.parse : Str -> Cal.Time` in namespace `Cal :: {}` | primitive (module `Cal` declares `Cal.Time`) |
| `Time.(..)` built in a body the walk reads | refused, with a message that names the fix (call one of the type's functions) |
| a primitive used as a value (`xs.map(Time.to_nanos)`) | refused, as a builtin used as a value is today (`src/check/code_reifier.zig:2767`); see Q5 |
| method path order | the explicit cut is no longer consulted for opaque operations; `:5588-5594` is replaced by `primitiveOf` |

### 3.2 D2: Laws

| Question | Decision | Reason |
|---|---|---|
| Can a package declare laws for its primitives? | No, in this proposal. | A law is a rewrite the normalizer trusts. A wrong package law gives a wrong description and no error. Builtin laws are derived and tested against the reference evaluator (`roc-reify-rule-derivation.md`; `src/reify/eval.zig`). A package claim has no such check. |
| What does a package primitive get? | Nothing: not in the builtin table, so no folding (N13), no law (layer L), no result range (N8k), not speculatable. Value numbering (N5) still merges two identical calls, which is exact for a pure function. | `src/reify/laws.zig:206`, `:397`, `:418`; `src/reify/eval.zig:357`; `src/reify/builder.zig:2619-2623` already treat a non-table prim this way. |
| Builtins | Unchanged: `src/reify/prims.zig` holds their table and laws. | |

A future declared-law form (associativity, commutativity, a derived order) is
Q8.

### 3.3 D3: What `code_primitives` Is For

| Function kind | Before | After |
|---|---|---|
| builtin | primitive; listing it is ignored (the builtin path runs first) | primitive; listing it is a compile error `already_primitive` |
| operation of an opaque type | primitive only in the method-call form; listing it made the direct form a `Prim` too | primitive in every form; listing it is a compile error `already_primitive` |
| item of a transparent nominal, or a free function | walked unless listed | unchanged: walked unless listed |
| generic function with a `where` | cannot be listed: "missing method" at the entry (F7) | listed as `Code.prim(f)`; calls carry evidence (section 3.7) |

The item's form changes from a tuple of references to
`code_primitives = [Code.prim(Vec3.scale), Code.prim(Vec3.plus)]`, a
`List(Code.PrimId)` (section 3.7.2).

`code_primitives` keeps its original purpose (`roc-reify-normal-form.md:713-724`):
a translator keeps a function with a visible body as a primitive because its
target has the operation natively (GLSL `Vec3.scale` as `*`, a math
library's `lerp` as `mix`). The check runs in `moduleCuts`
(`src/check/code_reifier.zig:8894-8960`); the new problem kind joins
`not_a_function` and `listed_twice` (`:8879`).

A translator keys a cut member as it keys any primitive: by name, or exactly by
`Code.prim(Vec3.scale)` (D6).

### 3.4 D4: Identity

#### 3.4.1 Internal Identity

| Item | Today | Proposed |
|---|---|---|
| `NamedPrim` (`src/reify/ir.zig:544-549`) | owner, method, role | add `identity: [32]u8`, the declaring module's `stable_hash` and the definition |
| Builder key (`src/reify/builder.zig:1176`) | `owner\0method\0role`, after a builtin-table lookup by the same text | identity and role; the builtin table is consulted only for builtins, through their export names (fixes F3) |
| `Types.opaque_` (`src/reify/types.zig:105`, `:228-237`) | name, args | add the nominal identity (`origin_module` and `source_decl`, as `nominalInstanceKey` hashes them, `src/check/code_reifier.zig:6569-6582`) |
| Digest (`src/reify/digest.zig:464-469`) | owner, method text | also the identity |

The identity is a content hash of the declaring module. A change to that module
already changes the artifact key of every importer
(`src/check/checked_artifact.zig:289-315`), so the identity adds no cache
invalidation. Two packages' `Time` types get two identities, so value
numbering never merges their calls and their `Code` values are not equal
(fixes F2).

#### 3.4.2 Identity a Translator Sees

```roc
## The identity of a primitive: a builtin, an operation of an opaque type, or a
## function in a translator's cut. Two primitives are equal exactly when they
## are the same definition in the same build.
PrimId :: { bits : U128 }.{
	is_eq : _
	to_hash : _
}

## The identity of a nominal type, without its type arguments.
TypeId :: { bits : U128 }.{
	is_eq : _
	to_hash : _
}

Op := [
	Lit(Lit),
	Prim({ owner : Str, method : Str, id : PrimId, evidence : List(Evidence) }),
	# ... the other ops are unchanged; `Evidence` is in section 3.7.3
]

Ty := [
	# ... unchanged constructors
	Opaque(Str, TypeId, List(Ty)),
]
```

| Field | Meaning | Keys a translator may use |
|---|---|---|
| `Prim.owner`, `Prim.method` | the name as today (export name for a builtin, `qualifiedName` otherwise) | none: names are for messages. A package type can take a builtin's name (it only warns, "builtin type shadowed"; `examples/reifying/sql/Bool.roc`), so a builtin name does not identify a builtin. Key on `Prim.id`. A nested type's owner carries its parent (`Cal.Time`). |
| `Prim.id` | `bits` of a hash of the exact identity | always safe |
| `Opaque` `TypeId` | same, for the nominal | always safe |

`Code.Digest` already uses a `U128` the same way (`src/build/roc/Builtin.roc`,
`Digest :: { bits : U128 }`). The compiler never compares by these bits; it
compares the full identity. A translator compares bits, which is sound for the
types and primitives of one build (Q11).

#### 3.4.3 What Changes for Builtins

| Item | Change |
|---|---|
| `Prim` names (`Str.concat`, `Num.Dec.times`, `Dict.get`, ...) | none |
| `Prim` record | gains `id` and `evidence` (a constrained builtin such as `List.sort` or `Dict.get` lists the methods its call uses, section 3.7) |
| builtin opaque `Ty` (`Dict`, `Set`, `Box`, ...) | `Opaque` gains its `TypeId`; named as its `Prim` owner (`Dict`, `Hasher`), Q10 |
| builtin table, laws, iterator roles | none |
| first-stage walk of function-returning builtins | none |
| code path | `.provided` (`src/check/code_reifier.zig:5111-5116`, `:5596-5607`) becomes the builtin case of `primitiveOf` |
| `code_primitives` that lists a builtin | compile error `already_primitive` (today silently ignored) |

### 3.5 D5: Captured Opaque Values

#### 3.5.1 How the Translator Spells the Requirement

```roc
select_where : Table(row), List(Sql.Extension), Code.Binds(Code(row -> Bool), Sql.Param) -> Code.Bound(Try(Str, Error))
```

`Code.Binds(code, fmt)` is a builtin transparent alias of `code`:

```roc
## A `Code` position whose run-time captures the program binds: each capture
## the description reads is encoded with its type's `encoder_for` in `fmt`.
Binds(code, _fmt) : code
```

| Choice | Reason |
|---|---|
| A transparent alias, not a new parameter on `Code` | A transparent alias of a `Code` is already a `Code` position, read off the written annotation (`design.md:23667-23672`; `stagedCode`, `src/check/Check.zig:27574-27618`). `Code(f)` and its three views keep their arity, so no existing signature changes. Any view combines with it: `Code.Binds(Code.Lawful(f), fmt)`. |
| On the parameter, not on `Code.Bound` | The requirement is about the lambda the parameter receives, and the checker reads the parameter's type when it checks that lambda. |
| A format type, not a list of methods | Roc's `where` constrains one type variable. A requirement on every capture's type is a schema over types no signature names, so the language fixes its shape (`encoder_for` in `fmt`) and the translator picks `fmt`. |

A phantom alias parameter (`_fmt`) must be legal for this spelling (Q1).

The format value. The encoder needs a value of `fmt`. The program builds it at
the bound call, without the translator, so it comes from the type. The checker
plans one type-rooted dispatch per site, `fmt.default : () -> fmt`, as it plans
`Shape.encoder_for(..)` (`test/cli/EncoderForTags.roc:20-28`). This is the
existing builtin convention, not a new method: `Iter.sum` requires
`item.default : () -> item` (`src/build/roc/Builtin.roc:3456`), and every number
type defines `default` (`src/build/roc/Builtin.roc:13033`). A format type
writes `default = || Default` (Q2).

#### 3.5.2 The Typing Rule "Bound Capture Encoding"

Declared in design.md "Code Reification":

> Let a lambda `L` stand at a position whose written type is
> `Code.Binds(c, fmt)`. A capture read of `L` is a maximal expression in `L`'s
> body of the form `x`, `x.a`, `x.a.b`, `x.0`, ... where `x` is a lookup of a
> binder in `L`'s closure captures. For each capture read `R` of type `τ`, the
> checker introduces the static-dispatch requirement
> `τ.encoder_for : fmt -> (τ, List(U8) -> Try(List(U8), []))`. It introduces
> `fmt.default : () -> fmt` once for the site. It solves and plans them as
> it solves and plans any other method requirement, and records each read with
> its plan on the site.

| Question | Answer |
|---|---|
| When does the checker know the captures? | Before checking: canonicalization records them on the closure (`e_closure.captures`, `src/canonicalize/Expression.zig:738-746`). Capture reads are syntax over the lambda body. Nothing about them waits for solving. |
| When does the checker know the position is `Code.Binds`? | When it checks the lambda against its expected type, the same moment it decides the lambda is at a `Code` position today (`stagedCode`). For a method-call translator that moment comes after the dispatch is planned (`design.md:23681-23690`), and the argument is checked then, so its requirements are introduced then. |
| Why every capture read, not only opaque ones? | Which reads are opaque is known only after solving. Requiring only those is a probe over solved types that gates new dispatch plans (section 3.5.6). The unconditional rule needs no probe. |
| Generic captures | A read whose type is a variable `t` gets `t.encoder_for : ..`. If `t` generalizes, the requirement enters the enclosing definition's scheme, like any method requirement, and each caller discharges it at its type. An opaque type that appears only after instantiation is therefore covered with no special case. (A bound site whose slot type is not closed is still refused, as today: `design.md:23774-23778`.) |
| Error row `[]` | The bound call has no error path for an input. A format whose encoder can fail does not fit; the checker reports the mismatch as an ordinary type error. |

#### 3.5.3 How the Walk Uses It

| Slot leaf | Description | Run-time value |
|---|---|---|
| transparent (`I64`, a record field, a `:=` nominal) | `Input(k)` of its structural `Ty`, as today | structural `Code.Value`, as today; the plan is not used |
| opaque, and its path is a capture read | `Input(k)` of type `Opaque(name, id, args)` | `Code.Value.Encoded(bytes)` through the read's plan |
| opaque, reached any other way (destructured from a capture, `{ at } = order`) | refused; the message names the fix: read it as `order.at` | none |

The walk changes in `inputSlot` (`src/check/code_reifier.zig:2719-2735`) and
`slotShape` (`:8003-8060`): an opaque leaf on a capture-read path gets the new
shape `encoded` instead of the refusal at `:8025`.

#### 3.5.4 How the Value Reaches the Translator

```roc
Value := [
	# ... unchanged variants
	Encoded(List(U8)),
]
```

| Concern | Answer |
|---|---|
| Who encodes | The program, at the bound call. Lowering builds the slot by calling the planned `encoder_for` on `fmt.default()`, applying it to the value and `[]`, and wrapping the `Ok` bytes. Monotype: `boundCodeValue`, `src/postcheck/monotype/lower.zig:37039`; Boxy: the same slot builder (`design.md:23790-23796`). Both read the plan the checker recorded; neither plans a dispatch. |
| What the translator sees at compile time | `Input(k)` with type `Opaque("Time", id, [])`. It emits a placeholder as today. |
| What it sees at run time | `bound.inputs()` holds `Encoded(bytes)` for that slot, in its own format. |
| Reference counting | The bytes are an ordinary `List(U8)` built by ordinary lowered Roc. The ordinary pipeline emits `incref` and `decref`; backends only follow LIR (AGENTS.md). No handle to the opaque value survives the call. |
| `Code.Value` equality and hash | `Value` derives `is_eq` and `to_hash` (`src/build/roc/Builtin.roc:24388-24403`); a `List(U8)` payload keeps both derivable. Two encoded values are equal when their bytes are. |
| Debug check | `CodeValueShape` (`src/check/checked_artifact.zig:2529`) gains `encoded`; lowering asserts each encoded slot gets bytes. |

#### 3.5.5 Transparent Captures

Description and value: unchanged. Typing: at a `Code.Binds` site only, each
capture read must have `encoder_for` in `fmt`. Structural types and builtins
have it. A `:=` nominal needs `encoder_for : _` or a written one. A translator
that keeps `Code(f)` without `Binds` sees no change at all. Q3 asks whether
this cost is acceptable.

#### 3.5.5a Format Coverage

A derived `encoder_for` calls one method of the format per shape:
`encode_record`, `encode_str`, `encode_i64`, ... (`design.md:7514-7517`;
`test/cli/EncoderForMissingStrMethod.roc`). A method lives in the module of
its type, so the translator package owns the format's methods.

| Who | Can do | Cannot do |
|---|---|---|
| Translator package | Give the format a method for each value its target accepts. Leave out the rest (for a target with no floats: no `encode_f32`, `encode_f64`). | |
| App | Make its own types encodable: `encoder_for : _`, or an `encoder_for` written by hand from the format's methods (a `Celsius := F32` written as `encode_i64` of a scaled value, for example) | Add a method to the format, or `encoder_for` to a type of another package |
| Package of an opaque type | Give the type `encoder_for` (derived or written) | |
| Glue package | Name primitives and types for the translator (D6) | Add `encoder_for` to the type it glues |

A format method left out costs nothing until a capture needs it. A requirement
of a missing method is an error only at an instance that uses it, so an app
that captures no float compiles. A captured `F32`, or a captured record with
an `F32` field, is a type error at the app's lambda: the format has no
`encode_f32`. The message names the format method, not the target (Q20). A
float that is not captured (a parameter, a literal) is not encoded, so the
format is not involved; the translator refuses it with `Code.refuse_at` if its
target has no float.

#### 3.5.6 Does "Solver-Mutating Rewrites" Apply?

No, with the reason stated so a reviewer can check it:

| Test from `design.md:9622-9646` | This rule |
|---|---|
| Mutates the solved graph or restamps plan metadata outside ordinary unification | No. It introduces requirements through the checker's ordinary method-requirement path, before they are solved. It writes no `dangerousSetVarRedirect` and restamps no plan. |
| A probe over solved types gates the mutation | The only probe is the existing `Code`-position detection (`stagedCode`), which already decides how the lambda is checked and recorded. The rule reads the written alias at that point. It does not inspect the capture types. |
| Changes which programs typecheck | Yes, for `Code.Binds` positions only, which do not exist yet. That makes it a typing rule of a new type, declared in design.md like any typing rule, with tests on both sides. |

Design.md "Rewrite Inventory" (`design.md:13018`) gets one line saying this rule
is constraint generation and not a rewrite, so the next reviewer does not have
to rederive it.

The alternative that does need the section. Requiring `encoder_for` only for
captures whose solved type is opaque is a probe-then-mutate rewrite. It would
need this declared rule, an inventory entry and tests on both sides:

> Opaque Capture Encoding (policy). After a site's lambda is solved, for each
> capture read whose solved type's head is an opaque nominal, introduce and plan
> `τ.encoder_for : fmt -> (τ, List(U8) -> Try(List(U8), []))`. A read whose type
> is still a variable at that point is rejected.

It is rejected here: it cannot cover a generic capture (the variable is open
when the rule runs, so the rule must reject it), and it adds a policy rewrite
for a cost (Q3) that the unconditional rule avoids.

#### 3.5.7 Rejected Alternatives for Captures

| Alternative | Reason |
|---|---|
| `Code.input(x)` marker (revision 1) | Rejected by the user: the author must not annotate captures. |
| Builtin format `Code.Encoding` producing a tree | The translator would decode a format it does not own. A translator-owned format writes bytes the translator already understands (for SQL: its bind encoding). |
| `Value.Encoded(state)` with the format's own state type | `Value` is one closed type; a per-format state needs a type parameter on `Value` and `Bound`. Bytes are the common denominator. |
| Run-time handle | Needs an existential type; a closure handle breaks `Value`'s derived `is_eq`/`to_hash`. |
| `Wrap` of the backing | Breaks the package's abstraction. |

### 3.6 D6: Third-Party Extension of a Translator

#### 3.6.1 Why Run-Time Data

A glue package (`TimeSql`) cannot add methods to `Time`: methods live in the
type's own module. It cannot change the translator's source either. So the
translator, if its author allows it, takes extensions as ordinary values. The
values name primitives and types by exact identity, which the compiler
computes from the function or type itself.

#### 3.6.2 The Identity API

```roc
## The identity of the primitive `f` names. `f` must be a reference to a
## top-level function or constant: `Code.prim(Time.is_before)`,
## `Code.prim(Str.concat)`.
prim : f -> PrimId

## A value that stands for type `t`.
Proxy(_t) :: {}
proxy : Proxy(t)

## The identity of `t`, which must be a nominal type, fixed at the call.
type_id : Proxy(t) -> TypeId
```

| Function | Checking | Value |
|---|---|---|
| `Code.prim(x)` | The checker records intrinsic `code_prim`. The argument must be a lookup of a top-level or imported definition (the same test `cutMember` applies, `src/check/code_reifier.zig:4413-4470`); anything else is a compile error at the argument. The reference is not instantiated, so a `where` of the referenced scheme adds no requirement (section 3.7.2). | a constant: the hash of the definition's identity, the same hash `Prim.id` carries |
| `Code.type_id(p)` | The checker records intrinsic `code_type_id`. The argument's type `Proxy(t)` must be closed at the call and `t` a nominal; otherwise a compile error at the call. This reads the solved type of the argument and writes nothing. | a constant: the hash of the nominal's identity |

`Proxy` follows the phantom-parameter pattern `Code(_fn)` already uses. Roc
has no type-level arguments, so an annotated constant carries the type:

```roc
time_proxy : Code.Proxy(Time)
time_proxy = Code.proxy

time_type = Code.type_id(time_proxy)
```

`Code.prim` of a function that is not a primitive at a site (a walked helper)
is legal: its id never appears in that site's description. It is useful for a
translator's own cut members.

#### 3.6.3 How a Translator Matches

The extension type belongs to the translator; the compiler does not define it.
A SQL sketch:

```roc
Extension := {
	prims : List({ prim : Code.PrimId, render : { args : List(Str), evidence : List(Code.Evidence) } -> Try(Str, Str) }),
	types : List({ type : Code.TypeId, column : Str }),
}
```

| Node | Translator step |
|---|---|
| `Prim({ owner, method, id, evidence })` | Builtin it knows: its own table, by id (a package type can take a builtin's name, so the name does not identify a builtin), checking `evidence` where the builtin is generic. Otherwise find `id` in the extensions' `prims`, translate the arguments, call `render` with the arguments and the evidence. Otherwise refuse. |
| `Opaque(name, id, args)` in a type position (a column) | find `id` in `types`; otherwise refuse. |
| `Input(k)` of an `Opaque` type | a placeholder, as for any input; the run-time value is `Encoded(bytes)` in the translator's format |

Uncovered primitive. The translator calls `Code.refuse_at(code, at, msg)`
(`src/build/roc/Builtin.roc`, `refuse_at`), so the compile error stands where
the call was written, with the inlined call frames. Suggested text:
"`Time.is_before` has no SQL form. Pass an extension that covers it, such as
`TimeSql.extension`."

#### 3.6.4 Interaction With Captures (D5)

The format belongs to the translator (`Sql.Param`). The glue package does not
change it. `Time.encoder_for` must be generic over the format and must use
only format methods that `Sql.Param` implements; a derived `encoder_for : _`
uses the standard set (`design.md:7288-7298`). The checker reports a missing
format method at the capture, as any missing method. The glue package
supplies what the translator cannot know: the column type, and the SQL form of
each operation, which asserts that `Time`'s order matches the stored encoding.

#### 3.6.5 Versioning

| Event | Effect |
|---|---|
| any edit of `Time`'s module | new identities; glue and app are compiled in the same build, so `Code.prim(Time.is_before)` and the `Prim.id` agree. Ids are never stored across builds. |
| glue and app depend on two different `Time` packages | two different types and ids; the app's operations are uncovered and the translator refuses at the site. Correct: they are different types. |
| `Time.is_before` renamed or removed | the glue fails to compile at `Code.prim(Time.is_before)`, an ordinary missing-name error |
| a new operation used by the app | uncovered primitive error at the site, naming it |
| `Time.is_before` keeps its name and changes its meaning | silent, as for any library upgrade (Q12) |

### 3.7 D7: Constrained Generic Primitives

Many primitives are generic with a `where`: `List.sort` (`where [item.Sort]`,
which is `item.order_relative_to`, `src/build/roc/Builtin.roc:3894`),
`Dict.get` (`k.is_eq`, `k.to_hash`), the `Set` operations, a package
`Time.max_in : List(Time), z -> Time where [z.offset : ..]`, and a translator's
own cut member such as `max_by`. Under D1 they are all one kind of thing, so
the fix is one fix.

#### 3.7.1 Why It Fails Today

| Need of a `Prim` call | Today |
|---|---|
| A reference to the definition, with no instance | The cut entry is checked as a value. The tuple is not generalized, so the reference is instantiated and its requirement (`k.is_lt`) never resolves: "missing method" at the entry (F7). The reifier never needed the instance. |
| The solved instance at the call | Present: every node carries closed argument and result types. Every scheme variable of a closed call appears in them. |
| The method that satisfies each `where` requirement at the call | Recorded by the checker as site evidence (`CheckedEvidence`, `src/check/static_dispatch_registry.zig:1614-1660`; read through `siteEvidence`, `:2748`, and `nestedEvidence`, `:2711`). The walk drops it for a `Prim` (F8). |
| A monomorphic type | Present at a site: types are sealed as Monotype seals them (`design.md:23611-23626`). |

So the reifier has every fact it needs. The listing fails in the checker, and
the description loses one fact the checker recorded.

#### 3.7.2 Listing a Generic Primitive

`code_primitives` entries become `Code.prim(f)`, and the item is a
`List(Code.PrimId)`:

```roc
Surreal :: [].{
	code_primitives = [Code.prim(Surreal.Array.sort_by), Code.prim(Surreal.Text.is_email)]
}
```

| Rule | Reason |
|---|---|
| The argument of `Code.prim` is a reference that is not instantiated. The checker resolves it to a definition, records it on the intrinsic `code_prim`, and gives the argument no type. A requirement of the referenced scheme is never introduced. | An identity has no instance. This is a typing rule of a new builtin, like `Str.inspect`'s; it introduces no constraint, so it is no solver rewrite. |
| `moduleCuts` reads the recorded references of `code_prim` uses in the item, not an evaluated value. | Same explicit data as today's checked lookups (`src/check/code_reifier.zig:8894-8960`). |
| The old tuple form is a type error (a tuple is no `List(Code.PrimId)`), with a hint to wrap each entry in `Code.prim`. | One spelling, no compatibility path. |

This joins D3 and D6: one identity function names a primitive for a cut, for an
extension and for comparison with `Prim.id`. The SurrealDB example's six cut
lists (69 names) become `List(Code.PrimId)` values; one list can be shared by
reference, which also removes the `check_cuts.py` comparison the example needs
today.

#### 3.7.3 Describing the Call

`Prim` carries the evidence of its call:

```roc
Op := [
	Prim({ owner : Str, method : Str, id : PrimId, evidence : List(Evidence) }),
	# ...
]

## The method the checker chose for one `where` requirement of a primitive's
## scheme, at one call. `method` is the required method's name, `ty` the type
## it dispatches on at this call.
Evidence := { method : Str, ty : Ty, target : Target }.{
	is_eq : _
	to_hash : _
}

Target := [
	## A primitive: a builtin, an opaque type's operation, or a cut member.
	## Its own evidence is nested, for a target that is itself constrained.
	Prim({ owner : Str, method : Str, id : PrimId, evidence : List(Evidence) }),
	## A method the walk read: row `id` of the graph is its body.
	Row(U32),
	## A method the compiler derives, over `ty`, as the `Derived` op names it.
	Derived(Str),
	## No value of `ty` can reach the dispatch.
	Unreachable,
]
```

| `CheckedEvidence.Resolution` | `Target` | Reason |
|---|---|---|
| `direct` | classified as a callee is (section 3.1): a primitive or cut member is `Prim`; a walked method is `Row`, built at the evidence's instance like any callee | the checker's node names the method target |
| `constraint` | the answer the enclosing walked call supplied (`supply`, `src/check/code_reifier.zig:5791`), then as above | the evidence forwards to the caller's, as Monotype reads it |
| `structural` | `Derived(method)` | the compiler writes it |
| `unreachable` | `Unreachable` | the checker proved it |
| `from_callable`, `from_scheme` | refused by name: "a call whose `where` evidence the compiler did not record" | the walk does not guess an answer the checker left to another stage |
| none: the compiler's own derivation reached the call | the method registry's answer for the dispatcher the receiver fixes, by the checker's rule (`receiverEvidence`, see the 1.10 notes) | the checker plans no call for a derivation, so it records nothing by construction |
| `checked_error` | not reached: the site is already an error | |

Order: the evidence list follows the callee scheme's requirements in their
checked order, a constraint alias (`item.Sort`) expanded. The order is data
the checker already fixed, so two spellings of one call give one list.

Probe rows under D7:

| Written | Description |
|---|---|
| `xs.sort()`, `xs : List(I64)` | `List.sort(p0)`, evidence `[order_relative_to @ I64 -> Prim Num.I64.order_relative_to]` |
| `xs.sort()`, `xs : List(Time)` | evidence `[order_relative_to @ Time -> Prim Time.order_relative_to]` |
| `xs.sort()`, `xs : List(Pt)` | evidence `[order_relative_to @ Pt -> Row r1]`, and `r1` is the reversed comparison |
| `xs.sort()` over a record | evidence `[order_relative_to @ { .. } -> Derived order_relative_to]` (if records derive it) |
| `d.get(k)`, `d : Dict(Time, Str)` | evidence `[is_eq @ Time -> Prim Time.is_eq, to_hash @ Time -> Prim Time.to_hash]` |
| `Lib.max_by(xs, f)` with `Code.prim(Lib.max_by)` in the cut | `Prim Lib.max_by(p0, closure r1)`, evidence `[is_lt @ I64 -> Prim Num.I64.is_lt]` |

Alternatives:

| Alternative | Reason rejected |
|---|---|
| Evidence as extra arguments (dictionary passing: `List.sort(p0, closure r1)`) | Changes the arity of every constrained builtin `Prim` that translators match today (`Dict.get`, `List.sort`). A primitive target would be a primitive used as a value, which is refused (Q5). |
| Encode the evidence in the instance `Ty` | A type does not say which method was chosen (a transparent `Pt` with a written order). |
| Keep dropping it; translators assume the natural order | That is F8: a wrong translation with no error. |
| Refuse every constrained primitive whose evidence is not a builtin | Refuses `List.sort` over `Time`, the motivating case. |

#### 3.7.4 Composition With D5 and D6

| With | Behavior |
|---|---|
| D5 captures | Evidence depends on types only, never on run-time values, so it is static per site. An encoded slot carries no evidence; a primitive call whose argument is `Input(k)` of type `Time` carries its evidence as any call does. The encoder plan of a capture read is evidence of the same kind, and the checker records it the same way. |
| D6 extensions | An extension entry may cover a generic primitive at all instances (it ignores `evidence`) or at some (it matches evidence target ids). `render` receives the evidence: `render : { args : List(Str), evidence : List(Code.Evidence) } -> Try(Str, Str)`. A translator can also treat `Prim List.sort` as `ORDER BY` exactly when the order evidence is a primitive it or an extension vouches for (`Num.I64.order_relative_to`, or `Time.order_relative_to` from `TimeSql`), and refuse a `Row` or `Derived` order by name. |
| D1 builtins | Builtins get evidence too. `List.sort(p0)` keeps its name and arguments and gains the evidence field. |

#### 3.7.5 AGENTS.md

| Rule | How D7 meets it |
|---|---|
| No guessing | Every `Target` comes from a `CheckedEvidence` entry; an entry with no recorded answer is refused, never reconstructed. The one exception is a call the compiler's own derivation reached, which has no entry by construction: its `Target` is the registry's answer for the dispatcher its receiver fixes, by the rule the checker applies to that type, and a case that rule does not answer exactly is refused. |
| Dispatch-plan metadata | Read only. No plan is created or restamped, so "Solver-Mutating Rewrites" does not apply. `Code.prim`'s argument rule introduces no constraint at all. |
| Invariants | Debug assertions: the evidence list has one entry per requirement of the callee scheme; a `Row` target's row exists in the graph. |

### 3.8 Worked Example

The date package (`roc-time`, unchanged except for an encoder it may already have):

```roc
Time :: { nanos : I128 }.{
	from_nanos : I128 -> Time
	from_nanos = |n| { nanos: n }

	is_lt : Time, Time -> Bool
	is_lt = |a, b| a.nanos < b.nanos

	encoder_for : _
}
```

The ORM (`Sql`), sketch of what changes:

```roc
Sql :: [].{
	## Bind parameters, written as bytes the SQL driver binds.
	Param :: [Default].{
		default : () -> Param
		default = || Default
		# encode_i128, encode_str, encode_record, ... write the bind encoding
	}

	Extension := {
		prims : List({ prim : Code.PrimId, render : { args : List(Str), evidence : List(Code.Evidence) } -> Try(Str, Str) }),
		types : List({ type : Code.TypeId, column : Str }),
	}

	select_where : Table(row), List(Extension), Code.Binds(Code(row -> Bool), Param) -> Code.Bound(Try(Str, Error))
}
```

The glue package (`TimeSql`):

```roc
TimeSql :: [].{
	time_proxy : Code.Proxy(Time)
	time_proxy = Code.proxy

	extension : Sql.Extension
	extension = Sql.Extension.({
		prims: [
			{ prim: Code.prim(Time.is_lt), render: TimeSql.binary("<") },
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

The application:

```roc
recent! = |cutoff| events.select_where([TimeSql.extension], |e| e.at < cutoff)
```

| Step | What happens |
|---|---|
| checking | `e.at < cutoff` dispatches to `Time.is_lt`. `cutoff` is a capture read at a `Code.Binds(.., Sql.Param)` position, so the checker requires `Time.encoder_for : Sql.Param -> (Time, List(U8) -> Try(List(U8), []))` and plans it. |
| walk | `Prim({ owner: "Time", method: "is_lt", id })(p0.at, Input(0))`; slot 0 is `Opaque("Time", tid, [])`, encoded. |
| translator, compile time | `Time.is_lt` is no builtin; `id` matches the extension; renders `(events.at < ?1)`. |
| program, run time | the bound call encodes `cutoff` with `Time.encoder_for` in `Sql.Param`; `inputs` is `[Encoded(bytes)]`; the ORM binds the bytes to `?1`. |
| without `TimeSql.extension` | the translator refuses at `<` with "`Time.is_lt` has no SQL form ...". |

### 3.9 Interactions

#### Normalization and Laws

| Rule family | Effect |
|---|---|
| N5 value numbering | identical package primitive calls merge (pure functions); after D4 calls of different packages never merge |
| placement, hoisting | package primitives are not speculatable, never hoisted |
| N13 folding and known values | none for package primitives; `a == a` over an opaque type is not folded (a written `is_eq` may be anything, `test/cli/StagedNominalMethods.roc:107-110`) |
| layer L | builtin table only |
| N14 | an opaque value never splits |
| N18 input slots | an encoded slot is an ordinary `Input(k)` leaf |
| verifier (`src/reify/verify.zig`) | add a debug assertion: `Wrap`/`Unwrap` never target an opaque type |

#### Generic Types, Nesting, Recursion

| Case | Behavior |
|---|---|
| generic opaque `Interval(t)` | `Opaque("Interval", id, [ty of t])`; one `PrimId` per definition, the node's types give the instantiation; the operation's own `where` obligations are resolved inside it and never read |
| builtin generic `Dict(k, v)` | `Opaque(name, id, [k, v])`, `Prim` owner `Dict` |
| opaque inside a record, list or union | the `Ty` nests it; field reads work as today; a captured `List(Time)` read as a whole is one encoded slot |
| recursion | an opaque type is never expanded; `anyRecursive` already reads opaque arguments (`src/reify/types.zig:560`) |

#### Cache

Rows are keyed by what each walk built (`design.md:23696-23698`). Identities
are content hashes, so they change only when the declaring module changes,
which already invalidates importers. `normal_form_version`
(`src/reify/mod.zig:39`) is bumped in Stage 0 (digests) and Stage 1 (op and
type shape).

#### Evaluation of the Described Function

A described function that also runs as Roc is unchanged: primitives are
ordinary calls, and no capture is rewritten. The only new run-time work is the
encoder call at a bound call.

### 3.10 AGENTS.md Constraints

| Constraint | How the design meets it |
|---|---|
| No fallbacks, heuristics or guesses | `primitiveOf` reads three explicit facts. Identities come from resolved references. Capture reads are syntax. The walk uses the plan the checker recorded. |
| Consume explicit data | Lowering reads the slot kind and the recorded plan. `Code.prim` and `Code.type_id` read the resolved reference and the solved type. |
| Invariants as debug assertions | encoded slot has a plan; `Wrap`/`Unwrap` never target an opaque type; an id the walk emits equals the one `Code.prim` gives for the same definition. User failures (missing `encoder_for`, a bad `Code.prim` argument, `already_primitive`, an uncovered primitive) are reported errors. |
| Solver-Mutating Rewrites | Not applicable (section 3.5.6). The rejected conditional variant would need the rule given there. D7 only reads recorded evidence; `Code.prim` introduces no constraint (section 3.7.5). |
| Backends follow LIR `incref`/`decref` | No backend change. |
| No JSON | Encoded bytes are in the translator's own format. |

## 4. Documentation Fix: `docs/langref/reifying.md:250`

The current fix is unchanged from revision 1, because the langref describes
the language as it is. Remove ", and opaque types" from the sentence that ends
at `crash`, and add a row to the "Some limits exist today" table
(`docs/langref/reifying.md:260-263`):

| Limit | Effect |
| --- | --- |
| An [opaque type](types#opaque-nominal-types) from a `::` declaration | A method call on a value of the type, such as `t.is_before(c)` or `t < c`, arrives as a `Prim` named by the type and the method, and a value you read from a parameter or a field arrives with the type's name and no fields. Everything else that touches the type's own code is refused: a call written as `Time.is_before(t, c)`, a constant whose definition calls one of the type's functions, a value of the type built in the function, and a captured value of the type. Two types with the same name from different packages arrive with the same name. |

After Stage 1 the row goes, and the "Builtin calls" row of the node table
(`docs/langref/reifying.md:180`) says: "A builtin, a function of an opaque type,
or a function in the translator's `code_primitives`. `id` identifies it
exactly; `Code.prim(f)` gives the same id for `f`." The `code_primitives`
section (`:110-123`) says that functions of opaque types are already
primitives. After Stage 2 a new section explains `Code.Binds` and
`Value.Encoded`, and one on extensions explains `Code.prim` and
`Code.type_id`.

Related, outside this proposal's scope: the same paragraph says captured
run-time values are refused, but a translator that returns `Code.Bound` binds
them, and the page doesn't document `Code.Bound` yet.

## 5. Staged Implementation Plan

```
Stage 0  internal identity + diagnostics fixes      (no API change)
   |
Stage 1  one primitive mechanism, PrimId/TypeId,     (API change; version bump)
         Code.prim, Code.type_id, code_primitives check
   |
Stage 2  Code.Binds: typing rule, encoded slots, lowering
   |
Stage 3  SQL example with extensions and a glue package; langref
```

### Stage 0: Defects Independent of the Design

| Item | Files | Tests (each validated by reverting the fix) |
|---|---|---|
| 0.1 Key named prims by identity; builtin table only for builtins (F2, F3). Done. | `src/reify/ir.zig:544-549`, `src/reify/builder.zig:1167-1187`, `src/reify/digest.zig:464-469`, call sites `src/check/code_reifier.zig:2199`, `:4605`, `:5487`, `:6123` | two modules with one type name give two prims and unequal digests; CLI test with two path packages each exporting `Time` checks `Code` inequality |
| 0.2 Key opaque `Ty` by nominal identity (F2). Done, and `Named` also (Q13). | `src/reify/types.zig:105`, `:228-237`, `:780`, `:825`; `opaqueTy` `src/check/code_reifier.zig:6625-6629` | same |
| 0.3 Report a refusal in another module's body at that module (F4). Done. | `rejectError` `src/check/code_reifier.zig:6719`; `src/check/report.zig` | CLI test: `ATime.from_nanos(3)` in a lambda; the report names `pa/Time.roc` |
| 0.4 Fix the normal-form invariant crash when `Lib.max_by` is walked (F9), by rule L: a lift into a nominal is a `Wrap`. Done. | `exprAt` and `liftTo` `src/check/code_reifier.zig:1955`, `:2701` | `code_reifier_test.zig`: the `max_by` body describes; the "F9" and "L3 F9" tests |
| 0.5 Bump `normal_form_version`. Done. | `src/reify/mod.zig:39` | fingerprint test |

Done (0.1, 0.2, 0.3, 0.4, 0.5):

| Item | What was done | Where |
|---|---|---|
| 0.1 | A function of a package is a `Prim` keyed by `ir.Definition`: the artifact key of its module and its `CIR.Def.Idx`, the pair every path to a callee already resolves it to. `NamedPrim` and `PrimName` carry `origin: PrimOrigin` (`builtin` or `declared`). `Builder.declaredPrim` keys by the definition and never reads the builtin table. `namedPrim` and `namedPrimWithRole` are for builtins only. The digest hashes the definition. | `src/reify/ir.zig:541-575`; `src/reify/builder.zig:1182-1196`; `src/reify/digest.zig:484-491`; `ForeignName.definition` `src/check/code_reifier.zig:4401`, set by `qualifiedName` (`:4548`) and the opaque method path (`:5600`); call sites `:2199`, `:4610`, `:5491`, `:6131` |
| 0.2 | `Ty.nominal` and `Ty.opaque_` carry `origin: types.Origin`: `builtin`, or an index of a `types.Declaration` (the content identity of the declaring module and `source_decl`, as `foreignNominal` names it). Interning keys, the canonical spelling labels, `widens` and the content digest read it. `Recursive(name)` keeps its name: the reifier closes a nominal only under its own instance. | `src/reify/types.zig:34-46`, `:212-223`, `:260-272`, `:354-361`; `Content.origin` `src/reify/digest.zig:329`; `nominalOrigin` `src/check/code_reifier.zig:6642` |
| 0.3 | A walk refusal carries the module whose source holds its region (`Rejection.module`: the artifact key and the env). The walk records that module where it enters a module's body or expression (`Walk.body`, `Reifier.enter`, set in `describeDefinition`, `inlineBody`, `exprAt`, `exprAs`, `templateSite`, and at each site); no offset is read to find it. Publication turns a refusal in another module into `StagedCode.foreign`: that module's file path, the lines and the 1-based span. The report shows that excerpt first, so the header names the other file, then the site in the reporting module. The file path is `ModuleEnv.source_path`, workspace information the coordinator records beside `qualified_module_name`. Call frames of a translator refusal (`RefusalCall`) already named their own module; a probe with a two-level helper shows `Helpers.triple(x) (in Helpers, line 7, column 13)`. | `src/check/code_reifier.zig:63-110`, `:6773-6798`, `:8455`, `:8574`; `foreignRefusalPlace` `src/check/checked_artifact.zig:38784`; `StagedCode.Foreign` `src/check/problem/types.zig:383`; `src/check/report.zig:5963`; `Document.addSourceExcerpt` `src/reporting/document.zig:575`; `src/canonicalize/ModuleEnv.zig:1023`; `src/compile/coordinator.zig:4390`, `:5081` |
| 0.4 | Rule L (`roc-reify-normal-form.md`, after the `Wrap` paragraph of 3.13; `roc-reify-tag-names.md` 2.4). `exprAt` builds a producer that fixes its own type (a parameter, a local, a `Prim` or `Apply` result, a projection, a loop result) at that type and calls `liftTo`: a widening adds no node, a lift into a nominal is `Wrap`, a lift below a tag payload or a nominal's backing is a `Switch` whose arms rebuild each tag at the destination, and `[False, True]` read as `Bool` is a `Switch` to the two literals. A `Call` is built at the union `liftReach` gives, never at a nominal its row's result only lifts into. `conformed`, which wrapped only a value whose type was exactly the backing, is removed: `liftTo` covers it. A pair outside the reach is a compiler invariant; a lift of a recursive type is refused. `normal_form_version` 26, `CACHE_VERSION` 191. | `src/check/code_reifier.zig:1944-1994`, `:2694-2805`; `src/reify/mod.zig:97-100`, `:230-234`; `src/build/roc/Builtin.roc:23965-23974` |
| 0.5 | `normal_form_version` 25 with a new fingerprint entry; `CACHE_VERSION` 190, because the inline digests of sites that read a package function or a declared nominal change. The CLI `version 24` expectations are now `version 25`. | `src/reify/mod.zig:39`, `:225`; `src/compile/cache_config.zig` |

Tests, with both sides:

| Test | Pins |
|---|---|
| `src/reify/builder.zig:3758` "F2, F3: a package function is keyed by its definition, never by a builtin's names" | two definitions of one name are two prims and two nodes; one definition is one prim and one node; `Num.I64.plus` of a package does not fold over literals, the builtin does (F3) |
| `src/reify/types.zig:1016` "F2: two nominals of one name and one structure are two types when two modules declare them" | `Named` and `Opaque`; `widens` is false between them |
| `src/reify/digest.zig:613` "F2: two packages' types and functions of one name have two digests, and one of each has one" | content digests across stores |
| CLI `test/cli/StagedForeignRefusal/` (`src/cli/test/parallel_cli_runner.zig:3451`) | F4: a lambda at a `Code` site calls `ATime.from_nanos`, whose body builds an opaque record; the report header is `pa/Time.roc:5:23` and the report names the site `main.roc:19:23`. A refusal in the site's own module keeps `main.roc:22:27` |
| CLI `test/cli/StagedOpaqueIdentity/` (`src/cli/test/parallel_cli_runner.zig:3449-3450`) | two path packages each export `Time` (opaque) and `Point` (transparent); the `inline_digest` of `x < y` and of `[x]` differs between the packages and is equal for two functions of one package |
| `src/compile/test/code_reifier_test.zig` "F9: a generic max_by, whose fold state is a structural union, describes" and "L3 F9: a fold's structural result read at Try is a Wrap of the fold" | 0.4: `n3 = List.fold(p0, n1, n2) : [Err([Empty]), Ok(I64)]`, then `n4 = wrap(n3) : Builtin.Try` |
| `code_reifier_test.zig` "L3 F9" tests: a local, a parameter at `Try`, a narrower parameter at `Try(I64, Str)`, a user nominal, `[False, True]` at `Bool`, an `if` branch, a forwarding helper (graph and inline views), a recursive helper | 0.4: every producer kind the walk returns at its own type |
| `code_reifier_test.zig` "L3 F9: a lift below a tag payload ..." and "... in a nominal's argument ..." | 0.4: the nested lift equals the `match` written by hand with each payload passed through `lift = \|t\| t` |
| `code_reifier_test.zig` "F9: a widening below a tag payload adds no node"; `src/reify/types.zig` "F9: a tag union never widens to a nominal, only to its backing"; `src/reify/verify.zig` "F9: a row whose result is a nominal and whose value is the structural backing does not verify" | 0.4, rejected side: a widening stays conformance, and the verifier keeps rejecting a missing `Wrap` |

Notes:

- The CLI test compares `inline_digest`, not `Code.is_eq`. `Code.is_eq` compares the emitted graph, which has no identity until Stage 1 (`Prim.id`, `TypeId`). Two functions of two packages also have two `Code` types, so `is_eq` cannot compare them.
- The probe with the compiler before the change printed `two primitives: False` and `two types: False`.
- 0.3: the probe with the compiler before the change reported the opaque record of `pa/Time.roc` under the header `main.roc` at the offsets of `Time.roc`, which underline unrelated text of `main.roc`. A headerless app that imports a sibling module now names `./Time.roc:5:23`, the path the coordinator records for that module.
- 0.4: the probes of the design note crashed with the compiler before the change ("normalization broke an invariant of the normal form"). The design note expected the nested lift to equal `Some(t) => Some(t)`. It does not: in that `match` the checker unifies the parameter's payload with `Try`, so the parameter type differs. A `match` that rebuilds the payload by hand (`Ok(v) => Ok(v)`) is a `Switch` per level and differs too. The tests compare with the `match` that passes the payload through a function whose body is the root lift, and rule L says so. The tests were not validated by reverting the fix (the brief forbids it); the crash before the fix is the probe output.
- 0.4: no source reached a `row_coerce` directly over a `Call` of a walked row: in every probe the checker lifts the fresh copy of the callee's result into the nominal, so the row is keyed at the nominal and its body does the root lift. `liftReach` (the `Call` built at the backing) has no test that reaches it.
- 0.3 changes no rule, no description and no cached result, so `normal_form_version` and `CACHE_VERSION` do not change. `ModuleEnv.source_path` is runtime-only and is not serialized.
- One definition is one primitive, and the name of the first path that reaches it names it. Today a method of an opaque type that a cut also lists can be reached as `typeNameText` (method form) and as `qualifiedName` (direct form). Stage 1 (`primitiveOf`, item 1.1) gives one name.
- Two modules with equal module names and equal source bytes have one content identity. The checker makes them one module, so the reifier does the same.

### Stage 1: One Primitive Mechanism, Identity and Evidence (D1 to D4, D6 API, D7)

| Item | Files |
|---|---|
| 1.1 `primitiveOf(reader, def)`. Done. | `src/check/code_reifier.zig` near `ownerOf` (`:4532`) |
| 1.2 Use it in the direct path, the method path and constant lookups. Done. | `resolvedTarget` `:5076-5130`; `methodTargetCallee` `:5576-5630` (replaces `:5588-5594` and the `.provided` arms); `unboundRef`/`foldedConstant` `:2695-2844` |
| 1.3 `already_primitive` problem; constants allowed in a cut. Done. | `moduleCuts` `:8894-8960`, `ModuleCuts.Problem` `:8879`; `src/check/report.zig` |
| 1.4 `PrimId`, `TypeId`, `Prim.id`, `Opaque(Str, TypeId, List(Ty))`, `Proxy`, `prim`, `type_id`; `Ty.children`/`numeric`/`name` arms. Done. | `src/build/roc/Builtin.roc:23632-23811`, `:23931-23936`, `:23972-24000` |
| 1.5 Intrinsics `code_prim`, `code_type_id` (checking, constant lowering). Done. | the checker's intrinsic table (as for `str_inspect`, `calleeIntrinsic` `src/check/code_reifier.zig:6223`); Monotype and Boxy constant lowering |
| 1.6 Emit ids. Done. | `src/check/code_emit.zig:249`, `:418` |
| 1.7 Refusal messages. Done. | `nominalExpr` `:2626`, `recordExpr` `:2384` |
| 1.8 Version bump, docs. Done for 1.1-1.3 and 1.7 (normal form 27), and for 1.4-1.6 and 1.9 (normal form 28). | `src/reify/mod.zig:39`; design.md "Code Reification"; `roc-reify-normal-form.md:713-728` |
| 1.9 `code_primitives : List(Code.PrimId)`; `Code.prim` argument not instantiated; `moduleCuts` reads the recorded references (D7, F7). Done. | the checker's intrinsic handling for `code_prim`; `moduleCuts` `src/check/code_reifier.zig:8894-8960`; migrate `examples/reifying/glsl/Glsl.roc:122`, `examples/reifying/surreal/` (six lists), `test/cli/StagedCut/lib/Expr.roc`, `test/cli/StagedCutRefused.roc` |
| 1.10 `Evidence`, `Target`, `Prim.evidence`; the walk reads site and nested evidence for every `Prim` callee (F8). Done. | `src/build/roc/Builtin.roc` (`Op`); `callExpr` `src/check/code_reifier.zig:4600-4620`, `methodTargetCallee` `:5576-5630`, `supply` `:5791`; IR: `src/reify/ir.zig` (evidence on a prim node), `src/reify/digest.zig` (evidence in the digest), `src/check/code_emit.zig:249` |

Stage 1 tests (both sides, each checked by reverting):

| Test | Pins |
|---|---|
| direct and method calls of `Time.is_before` give one node with one `id` | F1 |
| `cutoff = Time.from_nanos(5)` folds to `Prim from_nanos(5)` | constants |
| `Time.epoch` is a `Prim` with no arguments | constant operations |
| `Time.days_in_week : U8` and `Util.double` are walked | signature and module rule, rejected side |
| `Cal.parse : Str -> Cal.Time` is a primitive | module rule |
| `Code.prim(Time.is_before)` equals the node's `id`; `Code.prim` of a local value is a compile error | identity API |
| `Code.type_id(time_proxy)` equals the `Opaque` id; an open `Proxy(t)` is a compile error | type identity |
| a cut that lists `Str.concat` or `Time.is_lt` is `already_primitive` | D3 |
| builtin names unchanged: existing `Staged*` expectations for `Str.concat`, `Num.I64.is_lt`, `Dict.get` hold | builtins |
| new `test/cli/StagedOpaque/` with a path package | end to end |
| `code_primitives = [Code.prim(Lib.max_by)]` with `where [k.is_lt ..]`: no error; the call is `Prim Lib.max_by` with evidence `is_lt @ I64 -> Num.I64.is_lt` | F7 fixed, accepted side |
| the old tuple form `(Lib.max_by,)`: type error with the `Code.prim` hint | rejected side |
| `xs.sort()` at `I64`, `Time`, reversed `Pt`: three different evidence lists (`Prim`, `Prim` with `Time`'s id, `Row` holding the reversed body) | F8 fixed; revert the evidence read and the `Pt` test must fail |
| `d.get(k)` at a `Time` key: two evidence entries in scheme order | multi-requirement order |
| a generic walked helper that calls `List.sort` at `I64`: evidence resolved through `supply` | `constraint` resolution |
| a primitive call whose evidence is `from_callable`: refused by name | no guessing, rejected side |
| direct and method forms of one constrained call: equal evidence | spelling independence |

Done (1.1, 1.2, 1.3, 1.7, and 1.8 for these items):

| Item | What was done | Where |
|---|---|---|
| 1.1 | `primitiveOf(def, ty)` is asked of the reader of the module that defines the definition, with the definition's checked type in that reader's store (a procedure's `checked_fn_root`, a constant's top-level pattern type). A function of the builtin module is `.builtin`; a builtin constant is none, so it folds as before. Otherwise the definition is `.operation`, named by `qualifiedName`, when its type mentions a nominal with `is_opaque`, no `builtin` origin, and an `origin_module` equal to the module's content identity (`ModuleEnv.contentIdentityHash`). `mentionsOpaqueOf` reads function parameters and results, record fields, tag payloads, tuple items, nominal arguments, alias backings and `where` method types, never a nominal's backing. A constant's definition comes from `TopLevelValueTable.lookupByPattern` of its template's owner pattern, so `Reifier.Sources` and `ImportedModuleView` now carry `top_level_values`. | `src/check/code_reifier.zig:4763-4830`; `constantNamed` `:2970`; `Sources.top_level_values` `:574`; `ImportedModuleView.top_level_values` `src/check/checked_artifact.zig` |
| 1.2 | The direct path (`resolvedTarget`, `:5347`) and the method path (`methodTargetCallee`, `:5850`) both switch on `primitiveOf` before the cut: `.builtin` keeps the export name and the first-stage walk of `open_builtins`; `.operation` is a `foreign` callee. The opaque-receiver arm (`typeNameText` of the dispatcher) is removed, so the method path no longer needs `method` or `dispatcher_ty`, and `writtenMethodCall` no longer takes the method's name. `foldedConstant` (`:2994`) makes a primitive constant, or a constant in the cut, a `Prim` with no arguments at the use's type; the callers lift it as any `Prim` result. One definition has one name in every path, so the Stage 0 note (two spellings of an opaque method that a cut also lists) no longer applies: such a cut entry is now `already_primitive`. | `src/check/code_reifier.zig` |
| 1.3 | `moduleCuts` resolves an entry with `listedMember`: a function, as `cutMember` resolves it, or a top-level constant. An entry of the builtin module, or one `primitiveOf` classifies, is the problem `already_primitive` (`primitive_already_primitive`, report "Already A Primitive"). `Walk.useCut` reads constants the same way. | `moduleCuts` `src/check/code_reifier.zig:9214`; `src/check/problem/types.zig:455`; `src/check/report.zig:5958`, `:6059` |
| 1.7 | `nominalExpr` and the opaque arm of `recordExpr` refuse with one text that names the fix: "a value of an opaque type, built from its fields. The type hides its fields from a description: build the value by calling one of the type's functions, which a description names as a primitive". | `opaque_built` `src/check/code_reifier.zig:2664` |

Done (1.4, 1.5, 1.6, 1.9, Q10, and 1.8 for these items):

| Item | What was done | Where |
|---|---|---|
| 1.4 | `Code.PrimId` and `Code.TypeId` are `:: { bits : U128 }` with a written `is_eq` and `to_hash`. `Prim` is `Prim({ owner, method, id : PrimId })` and `Opaque` is `Opaque(Str, TypeId, List(Ty))`; the `Ty.children`, `numeric`, `name` and record-field arms read the new arity. `Proxy(_t) :: {}`, `proxy`, `prim` and `type_id` are in `Code`. `proxy` is a function, `proxy : () -> Proxy(_t)`, not the constant `proxy : Proxy(t)` of D6: a value binding does not generalize, so one constant cannot be a proxy of two types. A user writes `time_proxy : Code.Proxy(Time)` and `time_proxy = Code.proxy()`. `Named` has no `TypeId` yet (Q13). | `src/build/roc/Builtin.roc:23698`, `:23986`, `:24254-24292`; `BuiltinIndices` `src/canonicalize/CIR.zig` |
| 1.5 | `code_prim` and `code_type_id` are intrinsics with an annotation and no body (`src/canonicalize/BuiltinLowLevel.zig:43-46`, `:91`). The checker does not check or instantiate the argument of `Code.prim`; it only resolves an associated lookup, so a generic function with a `where` clause is named, not used. An argument that is no lookup of a top-level or imported definition is `prim_not_a_definition`, and an identity intrinsic read as a value is `identity_not_called`. Each call is recorded in `NodeStore.code_identity_uses` (`src/canonicalize/NodeStore.zig:974`, `:1597`). Publication (`moduleIdentities` `src/check/code_reifier.zig:9419`, called from `src/check/checked_artifact.zig:38730`) computes each call's id and stores it as the call's `code_from_lambda` constant node (`record[u128]`), so Monotype and Boxy restore it as any other constant and their lowering is unchanged. A proxy whose type is not a nominal fixed at the call (a type variable, a record, a tag union, a function) is `type_id_not_nominal`, found at publication; no solver mutation is needed. | `codeIdentityCallee`, `checkCodePrimReference`, `rejectCodeIdentityValueUse` `src/check/Check.zig:33233-33273`; `primIdentity`, `typeIdIdentity` `src/check/code_reifier.zig:6913-6934`; `src/check/report.zig` |
| 1.6 | The emitter writes `Prim.id` and the `TypeId` of `Opaque` with the same functions as the intrinsics: `src/reify/identity.zig` hashes a builtin primitive by owner and method, a package primitive by `ir.Definition`, a builtin nominal by its name and a declared nominal by `types.Declaration` (Blake3, 128 bits). | `src/check/code_emit.zig:250`, `:419-436`; `src/reify/identity.zig` |
| 1.9 | `finishDef` unifies a `code_primitives` item with `List(Code.PrimId)` under the context `code_primitives_item`, so the tuple form is a type error with the hint "Wrap each entry in Code.prim and write the entries as a list". `moduleCuts` reads the list, directly or through a same-module constant, and each entry's recorded `Code.prim` argument (`primReferences`); an item that is no list is `primitives_not_a_list`. Migrated: `examples/reifying/glsl/Glsl.roc`, the six lists of `examples/reifying/surreal/`, `test/cli/StagedCut/lib/Expr.roc`, `test/cli/StagedCutRefused.roc`, the cut strings of `src/compile/test/code_reifier_test.zig`. | `src/check/Check.zig:18490`; `moduleCuts` `src/check/code_reifier.zig:9274-9297` |
| Q10 | See the Q10 row of section 6. A nominal of the builtin module that the checker marks as no builtin (`Hasher`, `Code.PrimId`) is a builtin type too, found by the role of its declaring module through `ForeignLookup.resolve_builtin_module` (normal-form version 29). | `opaqueName`, `isBuiltinNominal`, `typeIdentity`, `nominalOrigin` `src/check/code_reifier.zig`; `ForeignStagedLookup.resolveBuiltinModule` `src/check/checked_artifact.zig`; `Lookup.resolveBuiltinModule` `src/compile/reify_fuzz.zig` |

Tests:

| Test | Pins |
|---|---|
| CLI `test/cli/StagedIdentity.roc`, run with Monotype and with `--specialize=no` | `Code.prim(Time.is_before)` equals the `id` of the node; `Code.prim(Tr.twice)` of a cut function and `Code.prim(Str.concat)` of a builtin equal their nodes' ids; `Code.type_id` of a `Time` and a `Dict(Str, I64)` proxy equals the `Opaque` id; `[Code.prim(Lib.max_by)]` with a `where` clause gives no error and the call is `Prim Lib.max_by`; the builtin names `Str.concat` and `Dict(Str, I64)` |
| CLI `test/cli/StagedIdentityRefused.roc` | rejected side: the tuple form is a type mismatch with the hint and no missing-method error (F7); `Code.prim` of a local value; `Code.prim` passed as a value; `Code.type_id` of an open `Proxy(t)` and of a record proxy |
| `src/reify/identity.zig` test | one definition is one id; two definitions, and two builtins whose names concatenate to the same text, are two ids |
| `src/check/code_emit.zig` test | `Prim` is the record `{ id, method, owner }` |

Notes:

- No rule of the normal form changed: an id is a function of the definition a node names already. Normal form 28 is a new version because every `Prim` and `Opaque` a translator reads has a new shape.
- A call of `Code.prim` or `Code.type_id` is a constant, so its argument is never evaluated. An argument with an effect, such as a `dbg`, does not run.
- The surreal example's own translator code matches `Prim({ owner, method })` and `Opaque(name, args)` and expects `Builtin.Dict` in one `expect` (`TypesTest.roc:271`). Those are outside the six lists, so they were not changed and those files do not compile until their owner updates them.
| 1.8 | `normal_form_version` 27 with a new fingerprint entry; `CACHE_VERSION` 192 with new `module_env_layout` golden bytes; the CLI `version 26` expectations are `version 27`. design.md "Code Reification", `roc-reify-normal-form.md` (the cut paragraph) and `docs/langref/reifying.md` (the cut section, the `Prim` row, the opaque limit row, and ", and opaque types" removed from the "describes" sentence) describe the classification. | `src/reify/mod.zig`; `src/compile/cache_config.zig`; `src/compile/cache_versioning.zig` |

Tests:

| Test | Pins |
|---|---|
| `src/compile/test/code_reifier_test.zig` "D1 F1: a direct call and a method call of an opaque type's function are one Prim" | F1: both forms give `n2 = Lib.is_before(n0, n1)` and equal dumps; the type is in package `lib` |
| "D1: a top-level constant that calls an opaque type's function folds to that Prim" | constants: `Lib.from_nanos(n1)` with `n1 = 5` |
| "D1: a constant of an opaque type is a Prim with no arguments" | constant operations: `n0 = Lib.epoch()` |
| "D1: a function or constant of the type's module whose type names no opaque type of it is walked" | signature rule, rejected side: `double` and `days_in_week` are their bodies, no `Lib.` in the dump |
| "D1: a function of another module over an opaque type is walked to the type's primitives" | module rule, rejected side: the app's `later : Lib, Lib -> Bool` is walked to `Lib.is_before(n0, n1)` with swapped operands |
| "D1: a function that names a nested opaque type of its module is a primitive" | module rule, accepted side: `Lib.parse(n0) : Lib.Cal` |
| "D3: a constant in the cut is a Prim with no arguments, and outside it folds" | `Tr.limit()` in the cut, `3` without a cut |
| CLI `test/cli/StagedCutRefused.roc` | D3: `Str.concat` and `Stamp.from` (an opaque type's function) are "already a primitive"; `Tr.limit` (a constant) is accepted; `5` and the repeated `Tr.twice` stay refused |
| CLI `test/cli/StagedOpaque/` (path package `pt`: `Time`, `Cal`, `Util`), Monotype and Boxy | end to end: direct, method and operator forms; `cutoff` folds to `Time.from_nanos(5)`; `Time.epoch()`; `days_in_week` folds to `7`; `Util.double` walked; `Cal.parse(p0)`; nested `Cal.Time.is_lt`; an app helper over `Time` walked |
| CLI `test/cli/StagedForeignRefusal/` | 0.3 kept: `ATime.from_nanos` is now a primitive, so the fixture calls `ATime.shifted : I64 -> I64`, whose body builds the opaque record; the report header is `pa/Time.roc:12:34` and the text names the 1.7 fix |
| existing `Staged*` CLI expectations, `code_reifier_test.zig` "an opaque nominal's own method is named, not walked" | builtin names and same-module opaque methods unchanged (`Sealed.is_eq`, `Str.concat`, `Dict.is_eq`) |

Notes:

- The tests were not validated by reverting the change (the brief forbids it). Before the change the direct form of an opaque function, a constant that calls one and an opaque constant were refused ("a record of this type", probe rows 6-9), so the accepted-side tests fail on the old compiler by construction.
- A top-level value that computes a function (`cmp = make_cmp(..)`) in an opaque type's module is still read through `computedFunction`, not classified. No probe reached it.
- A primitive used as a value (`xs.map(Time.to_nanos)`) is refused, as a builtin used as a value is (Q5).

Done (1.10, D7, F8, and 1.8 for this item):

| Item | What was done | Where |
|---|---|---|
| 1.10 API | `Code.Evidence := { method : Str, ty : Ty, target : Target }` and `Code.Target := [Prim({ owner, method, id, evidence }), Row(U32), Derived(Str), Unreachable]`, both with derived `is_eq` and `to_hash`; `Op.Prim` gains `evidence : List(Evidence)`. Both nominals are in `builtin_type_specs`. | `src/build/roc/Builtin.roc` (`Op`, `Evidence`, `Target`); `src/canonicalize/CIR.zig` |
| 1.10 walk | `Provided` and `ForeignName` carry `PrimEvidence`: the callee template's evidence params (`evidenceParams`, the scheme's requirement order with a constraint alias expanded) and what the call recorded. The direct path reads `siteEvidence` of the callee reference (`callRecorded`), the method path the edge's `nestedEvidence` (`methodTargetCallee`), and `supply` answers a forwarded entry. `evidenceEntries` maps each entry by the table of 3.7.3: `direct` through `methodTargetCallee` to a `Prim` (with its own evidence, recursively) or a `Row` (`calledRow`, at the edge's instance); a `constraint` that `supply` leaves because it is `independent_callable` reads the slot it names (`sharedTarget`): the checker shares the slot's target identity with the use, so a target with no nested evidence, a derivation or `unreachable_value` is the answer when the target is a primitive, and a walked target there is refused, because its row's instance is the use's own callable, which no table records; `structural` to `Derived(method)`; `unreachable_value` to `Unreachable`; `constraint` that no walked call answers, `from_callable`, `from_scheme`, an edge whose nested evidence is `from_callable`, and a call no edge recorded (a derivation-reached method) are refused with "a call whose `where` evidence the compiler did not record"; `checked_error` is an invariant. A debug assertion checks one entry per requirement. | `src/check/code_reifier.zig` (`PrimEvidence`, `primEvidence`, `evidenceEntries`, `foreignPrim`, `providedPrimAt`) |
| 1.10 IR | The evidence is a prim node's `aux` words (`ir.EvidenceWords`): count, then per entry `method`, `ty`, kind and target, a nested count after a `prim` target. So hash-consing keys it. A row it names is an edge of the `references` graph, `mergeInto` renames it, N8f gives it a convention row as for a closure that captures nothing, `number.siteRows` reaches it, tail-call and outline treat it as a closure. Equality pairs its rows (`equal.sameAux`), the digest names them as a `Call` names its row (`evidenceImmediates`), the verifier checks a `Row` target exists and is not merged, the dump prints `where [method @ Ty -> target]`. | `src/reify/ir.zig`, `builder.zig` (`primWith`), `rows.zig`, `number.zig`, `equal.zig`, `digest.zig`, `verify.zig`, `dump.zig`, `loops.zig`, `views.zig` |
| 1.10 emit | `Prim` is `{ evidence, id, method, owner }`; an evidence `Row` is the row's index in the graph. | `src/check/code_emit.zig` (`primRecord`, `evidenceList`) |
| 1.8 | `normal_form_version` 30 with a new fingerprint entry; `CACHE_VERSION` 194 with new `module_env_layout` golden bytes; the CLI `version 29` expectations are `version 30`. design.md "Code Reification", `docs/langref/reifying.md` (the `Prim` row, an "Evidence" section) and `roc-reify-normal-form.md` (the `Prim` shape, `Evidence`, `Target`, the resolution table) describe it. | |

Tests:

| Test | Pins |
|---|---|
| `src/compile/test/code_reifier_test.zig` "D7 F8: List.sort at I64, at an opaque type and at a reversed nominal carries three evidence lists" | F8: `Num.I64.order_relative_to`, `Lib.order_relative_to` (package opaque type), and `r1` whose body is the reversed comparison |
| "D7: Dict.get at an opaque key carries is_eq and then to_hash, in the order of its where clause" | multi-requirement order |
| "D7: the direct and the method form of one constrained call carry equal evidence" | spelling independence |
| "D7: a generic helper's List.sort is answered by the evidence its caller supplied" | `constraint` resolution through `supply`; the dump equals the direct call's |
| "D7 F7: a call of a generic cut member carries the method its where clause resolved to" | `Lib.max_by(p0, n0) where [is_lt @ I64 -> Num.I64.is_lt]` |
| "D7: a derived == reaching List.is_eq carries the evidence its receiver fixes" | derivation-reached evidence: `List.is_eq(n0, n1) where [is_eq @ U16 -> Num.U16.is_eq]` |
| "D7: a derived == reaching Dict.is_eq and Try.is_eq carries the evidence its receiver fixes" | the same for `Dict` and for `Try`'s two requirements |
| "D7: a derived == over nested containers carries nested evidence" | `List(List(U16))` nests `List.is_eq [is_eq @ U16 -> ..]`; a record element is `derived is_eq` |
| "D7: a derived == over a list of a type that writes is_eq names that method" | a transparent nominal's written `is_eq` is `r1`; a local opaque type's is `Sealed.is_eq` |
| "D7: a derived == reaching List.is_eq at a package's opaque type is refused by name" | rejected side: the registries the walk reaches declare no `is_eq` for a package's opaque `Lib`, as a derived `==` on `Lib` itself is refused (`nominalEq`) |
| `src/check/code_emit.zig` "D7: a Prim's evidence is a list of { method, target, ty }, ..." | the emitted shape, and a row only evidence names is emitted |
| CLI `test/cli/StagedEvidence.roc`, Monotype and Boxy | end to end: `List.sort` at `I64` and at a reversed `Pt` (`row 1`), `Dict.get` at `Str`, and a recursive `Tree` whose `is_eq` names its own row inside `List.is_eq`'s evidence |
| CLI `test/cli/StagedEvidence.roc` (after 1.10) | `==` derived for a record holding a `List(U16)`, a `Dict(U16, Str)`, a `Try(U16, Str)`, a `List({ tags : List(Str) })` (`derived is_eq`) or a `List(List(Tree))` (nested `List.is_eq`, then `row 1`) carries the registry's evidence. `StagedEvidenceRefused.roc` is removed. |

Notes:

- Translator-visible change beyond the plan: a `==` or `to_hash` the compiler derives over a record or tag union reaches a builtin container's own method (`List.is_eq`, `Dict.is_eq`, `Try.is_eq`) with no dispatch plan, so the checker records no evidence for its `where`. Before 1.10 these described as `List.is_eq(..)` with no evidence; 1.10 first refused them by name.
- Decided after 1.10: derivation-reached evidence comes from the registry lookup. The checker is not changed. `methodTargetCallee` gives a primitive reached with `.receiver` fixing a `PrimEvidence.receiver`, and `evidenceEntries` then calls `receiverEvidence` (`src/check/code_reifier.zig`): `receiverInstantiation` fixes the template's quantified variables from the receiver, each requirement's dispatcher is the variable its `EvidenceParamRecord.slot` names, and `receiverEntry` resolves it by the rule of `resolveObligationStep` (`src/check/checked_artifact.zig`), which Monotype applies to the same derivation (`synthesizeComponentEvidenceAtNodeForPurpose`, `src/postcheck/monotype/lower.zig`). The lookup is `dispatchTarget`'s (`receiverMethod`, then `methodTargetCallee` with `.receiver` fixing), so no second lookup exists.

  | Dispatcher the receiver fixes | `Target` |
  |---|---|
  | nominal, registry target is a procedure | `Prim` (with its own evidence, recursively) or `Row`, as `methodTargetCallee` classifies it |
  | nominal, registry target is structural | `Derived(method)` |
  | record, tuple, tag union, `{}`, function, where the requirement is equality or hash | `Derived(method)` |
  | nominal with no registry target in reach | refused: "a `where` requirement whose method no module in reach declares, reached by a derivation" |
  | type variable | refused: "a `where` requirement on a type variable, reached by a derivation" |
  | requirement with no `slot` (a composite dispatcher) | refused: "a `where` requirement on a composite type, reached by a derivation" |
  | structural shape, requirement is a codec or a map, or permits no derivation | refused: "a `where` requirement on a structural type that permits no derived equality or hash, reached by a derivation" (Monotype then reads inhabitedness, which the walk does not) |

  A site with recorded evidence never takes this path: only `.receiver` fixing sets `receiver`, and only a derivation (`nominalEq`, `hashOver`, `inspectExpr`, `dispatchTarget`'s derivation-reached branch) fixes by the receiver. A checker-recorded form of this evidence (the checker planning the derivation's calls and recording their evidence) is a post-merge refactor; the description does not change with it. `normal_form_version` 31 (a new fingerprint entry) and `CACHE_VERSION` 195 (new `module_env_layout` golden bytes) mark the change; the CLI `version 30` expectations are `version 31`.
- A generic walked helper that calls `List.sort` forwards `item.Sort` as an `independent_callable` constraint. 1.10 described it where the order is a primitive (`I64`, an opaque type's `order_relative_to`), and refused it where the order is a method the walk would read (a `Pt` with a written order), because the row's instance is the use's own callable relation, which no table records.
- Gap closed after 1.10 (no checker change): the shared slot names the target, and the use's callable relates it to the requirement's callable, whose first parameter is the dispatcher. So `evidenceEntries` builds a shared slot's target with `.receiver` fixing at the dispatcher under the helper's substitution, and `receiverInstantiation` fixes the row's instance. `receiverInstantiation` now leaves a row variable unbound, as `instantiationOf` does (no description names one): the open return union of a written `order_relative_to` is one. A non-row variable that only the rest of the callable fixes is still refused by name ("a generic method this receiver does not fix"). No source reaches that refusal: an annotated generic helper that forwards such a requirement (`a.mix : a, c -> a` to a `Bx.mix : Bx, y -> Bx`) is reported "Cannot Reify A Polymorphic Function" by the checker first, and an unannotated one records the exact relation, so `supply` answers it through the edge. `sorted(xs)` at `List(Pt)` and at `List(Bx(Str))` now describe as `xs.sort()` does (tests "D7: a generic helper's List.sort at a nominal with a written order names the order's row, as the direct call does" and "... at a generic nominal's written order builds the row at the receiver's instance"; CLI `StagedEvidence.roc` line `helper rows 2: ..`). `normal_form_version` 32 and `CACHE_VERSION` 196 mark the change.
- No source in the probes produced `from_callable` or `from_scheme` evidence at a primitive call: a top-level alias `my_sort = List.sort`, a nested `List.sort` under `List.map`, a `Dict` of lists, and a recursive written `is_eq` all record `direct` evidence. The derivation-reached case that first pinned the rejected side now carries the registry's evidence (see the decision note above), so no source pins this refusal.
- The tests were not validated by reverting the change (the brief forbids it). Before the change the dumps had no `where` part, so each accepted-side test fails on the old compiler by construction.

What ships first: Stage 0 and Stage 1. They fix filters that compare against a
parameter or a constant, give translators exact keys, and need no lowering
change beyond two constant intrinsics.

### Stage 2: Captured Opaque Values (D5)

| Item | Files |
|---|---|
| 2.1 `Code.Binds`, `Value.Encoded` | `src/build/roc/Builtin.roc` near `:24388-24420` |
| 2.2 `stagedCode` returns the format; capture reads; requirements; site records reads and plans | `src/check/Check.zig:27574-27618`, `CodeReificationSite` |
| 2.3 Walk: encoded slots, new refusal for an opaque leaf off a capture read | `inputSlot` `src/check/code_reifier.zig:2719-2735`, `SlotSource` `:7983-7991`, `slotShape` `:8003-8060` |
| 2.4 Publication: slot kind and plan; `CodeValueShape.encoded` | `src/check/checked_artifact.zig:2529-2560`, `bindCodeInputs` `:38786` |
| 2.5 Monotype lowering | `boundCodeValue` `src/postcheck/monotype/lower.zig:37039`, `codeValueBody` `:37238` |
| 2.6 Boxy lowering | the `Code.Bound` slot builder (design.md "`.boxy` Runtime Lowering") |
| 2.7 design.md: the typing rule in "Code Reification"; the inventory note at `design.md:13018` | design.md |

Stage 2 tests:

| Test | Pins |
|---|---|
| `\|e\| e.at < cutoff`, `cutoff : Time` captured, `Code.Binds(.., Fmt)`: one slot, `Opaque` type, `Encoded` bytes equal `Time.encoder_for` in `Fmt` (Monotype and Boxy) | main case |
| same with `Code(f)` (no `Binds`): refused as today | rejected side |
| captured transparent `I64` and record field: structural values as today | transparent unchanged |
| captured `:=` nominal without `encoder_for` at a `Binds` site: type error | typing rule, rejected side |
| generic helper capturing `t`: the requirement appears in its scheme; a caller at `Time` works, a caller at a type without the encoder fails | generic captures |
| `{ at } = order` then `at < x`: refused with the "read it as `order.at`" message | path rule |
| format with a fallible encoder: type error | error row `[]` |
| debug: a structural value built for an encoded slot trips the shape assertion | invariant |

Done (2.1 to 2.7):

| Item | What was done | Where |
|---|---|---|
| 2.1 | `Value` has `Encoded(List(U8))`. `Code.Binds(code, fmt) : code` is a transparent alias with a phantom parameter (Q1): a named phantom parameter is legal, and `stagedCode` reads the alias arguments. The format value is `fmt.default()`, from the existing `default : () -> fmt`; there is no `code_format`. | `src/build/roc/Builtin.roc`; `BuiltinIndices.code_binds_type` `src/canonicalize/CIR.zig` |
| 2.2 | Typing rule "Bound Capture Encoding": `introduceBoundCaptureEncoding` gives each capture read (`x`, `x.a`, `x.0` of a closure capture) of a lambda typed `Code.Binds(c, fmt)` the requirement `t.encoder_for : fmt -> (t, List(U8) -> Try(List(U8), []))`, and the site once `fmt.default : () -> fmt`. This is constraint generation, not a rewrite. The site is recorded in `ModuleEnv.bound_capture_encodings`. A missing method is the report "Cannot Bind Captured Value" (Q20). | `src/check/Check.zig`; `src/canonicalize/ModuleEnv.zig`; `src/check/report.zig` |
| 2.3 | A slot whose type holds an opaque type and whose path is a capture read is `encoded`. An opaque leaf off a capture read, inside a captured nominal, or at a site with no `Binds` is refused with a message that names the fix. | `captureReads`, `opaqueSlotRefusal`, `Walk.useCaptureReads` `src/check/code_reifier.zig` |
| 2.4 | Publication makes the checked exprs `fmt.default()` and `T.encoder_for(default)` with ordinary static dispatch plans (Q2), and stores the encoder in `CheckedCodeSlot.encoder`. `CodeValueShape.encoded`. | `src/check/checked_artifact.zig`; `src/check/static_dispatch_registry.zig` |
| 2.5 | `encodedSlotValue` calls the encoder with the value and an empty list and builds `Encoded` from `Ok`. | `src/postcheck/monotype/lower.zig` |
| 2.6 | `lowerEncodedSlotInto` does the same in Boxy; `plan.zig` types the encoder expr. | `src/postcheck/boxy/lower.zig`, `src/postcheck/boxy/plan.zig` |
| 2.7 | design.md: the typing rule in "Code Reification" and the Rewrite Inventory entry. `docs/langref/reifying.md` "Captured Values"; `roc-reify-normal-form.md` encoded slots. | design.md |

Notes:

- `normal_form_version` is not changed: no rule of the normal form changed (Q15). `CACHE_VERSION` is 197.
- Decision (follow-up): a captured function is exempt. An `encoder_for` of the new constraint origin `bound_capture` whose dispatcher is a function type is satisfied, and the site drops its record of that read, so the walk describes the function as code as before Stage 2. The test is the read's own checked type: a record that holds a function still needs an encoder. `exemptFunctionBoundCapture` `src/check/Check.zig`; `ModuleEnv.removeBoundCaptureEncoding`.
- Decision (follow-up): the copy of a requirement that instantiation makes of a generic function keeps the origin `bound_capture`, and `noteBoundCaptureCopy` notes it when the drain enters it, so its failure (and the failure of what it derives) has the "Cannot Bind Captured Value" text with the type and the format. A requirement of the rule on a type with no methods (a function inside a captured record) has the same text.
- The invariant test (a structural value for an encoded slot) is not added: only a crash test can show it.

### Stage 3: Extension Example and Docs

| Item | Files |
|---|---|
| 3.1 SQL: `Extension`, `Param` format, `select_where` with `Binds` and extensions; operator table keyed on builtin owners only (today it keys on the method alone, `examples/reifying/sql/Sql.roc:894-949`); `captured_value` gets an `Encoded` arm | `examples/reifying/sql/Sql.roc` |
| 3.2 A path package with an opaque timestamp and a glue package; `main.roc` filter with a captured timestamp; `check.py` binds the bytes | `examples/reifying/sql/` |
| 3.3 Langref sections | `docs/langref/reifying.md` |

Done (3.1, 3.2):

| Item | What was done | Where |
|---|---|---|
| 3.1 | `Sql.Extension` (`prims` keyed by `Code.PrimId`, `types` keyed by `Code.TypeId`) and its constructor `Sql.extension`. `select_where : Table(row), List(Extension), Code.Binds(Code(row -> Bool), Param) -> Code.Bound(..)`. `Sql.Param` is an order-preserving byte format (integers big-endian with the sign bit flipped, `Dec` as attos, `Str` with `0` escaped, a record as its fields in name order). `captured_value` maps `Encoded` to the new `Value.Blob`, written `X'..'`. The operator table and the `Bool.not`/`negate` arms apply only to a builtin (first by owner name in `Sql.is_builtin`, now by id in `Sql.builtins`, see 3.2); any other `Prim` is matched by `id` against the extensions, and is refused when none covers it. `Table.create_with` gives an `Opaque` column the extension's SQL type. `main.roc` prints a blob parameter as `{"blob": hex}` and `check.py` binds it as bytes. | `examples/reifying/sql/Sql.roc`; tests in `examples/reifying/sql/extensions.roc` over `examples/reifying/sql/Stamp.roc` |
| 3.2 | Path package `time` (opaque `Time :: { nanos : I128 }` with `from_nanos`, `from_seconds`, `is_eq`, `is_lt`, `is_gt`, a derived `encoder_for`) and glue package `time_sql` (`TimeSql.extension`: `is_lt`, `is_gt`, `is_eq` as `<`, `>`, `=`, and `Time` as `BLOB`). `main.roc` and `refactored.roc` are apps over `sql`, `time` and `time_sql`; migration `004_events`, seed rows and the query `events_before` with a captured `Time`. One encoding serves binds and inserts: `Table.insert_one : Table(row), Code.Binds(Code({} -> row), Param) -> Code.Bound(..)` builds the row from captured values, so a `Time` field is bound as the same `Sql.Param` bytes a filter binds; `Table.insert` (`RowEncoding`) has no `encode_i128`, so a row with a `Time` does not type-check there. `check.py` binds a `{"blob": hex}` parameter as bytes and compares a blob column as the same hex; `events_before` agrees with Roc. `Sql.param_bytes` gives the bytes in Roc. `extensions.roc` checks that `Param` bytes of `Dec`, `I128`, `Str` and a record sort as the values do. `Sql.is_builtin` matched owner names, but a package type can take a builtin's name (`examples/reifying/sql/Bool.roc` has its own `Bool.not`). `Sql.builtins` replaces it: an `Extension` keyed by the `Code.prim` ids of the builtins, so one lookup by `id` serves builtins and extensions, and `extensions.roc` checks that the module's own `Bool.not` is not the builtin's. | `examples/reifying/sql/time/`, `examples/reifying/sql/time_sql/`, `examples/reifying/sql/Sql.roc`, `main.roc`, `refactored.roc`, `check.py`, `expected_output.sql`, `extensions.roc` |

Done (3.3):

| Item | What was done | Where |
|---|---|---|
| 3.3 | One combined langref pass with the structural proposal (its 0.8 and 4.4). The node table and "Evidence" were already there from Stage 1, and "Captured Values" from Stage 2. "Identities" now says which reports `Code.prim` and `Code.type_id` give (`not a definition`, also for a derived `is_eq` of a type that is no builtin; `call this function`; `not a nominal type`). The new section "Extending a Translator" shows the `time_sql` glue package: the translator keys `Prim` nodes and `Opaque` types by id, a name can repeat and an id cannot, an id does not live across builds, and the translator cannot check what a glue package claims. "Captured Values" shows `select_where` with its extension list. The new section "Every Report" lists each report of reification with its cause | `docs/langref/reifying.md` |
