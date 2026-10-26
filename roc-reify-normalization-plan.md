# Normalization: implementation plan

This plan implements the normal form that `roc-reify-normal-form.md` defines.
It decides the architecture, lists every normalization step as a unit of work,
and designs the tests that land with each step. It does not restate how each
step works; the normal-form document owns that, and every step below cites its
section there.

| Question | Answer | Section |
|---|---|---|
| Where does normalization run? | at checked-artifact publication, where the reifier runs today, and only for modules that have a `Code` site | 1.1 |
| Does `Code.Ir` become a MIR? | no. The reifier walk builds the normal-form IR directly, through smart constructors. No syntax-shaped tree is built at any stage | 1.2, 1.3 |
| Does it reuse the post-check pipeline? | no, because the normal form must depend on the language version, not on the optimizer. It reuses two post-check algorithms as libraries | 1.2, 1.6 |
| What does it cost at compile time? | nothing for modules without a site; near linear in the reached body size for modules with one; cached with the artifact | 2 |
| Which steps, in which order? | 117 steps in 19 milestones. The core answers `roc-reify-refactor-safety.md` and adds loops and rule derivation at k = 6 and 7; the extensions come after it | 3, 4 |
| What does a reified body promise about crashes, floats and `and`/`or`? | C2: Roc's result wherever Roc does not crash, and no speculation; floats fold through Roc's own deterministic math; `and` and `or` are n-ary nodes | 1.9 |
| What else changes when the plain `Ir` goes? | eight complications, each with a design answer, steps and tests | 1.10 |
| What does a translator get besides the graph? | a fixed set of built-in utilities, `to_tree` among them, written in Roc over the value unless they need the normalizer | 1.8 |
| How is it tested? | seven test layers, and each step lands with its own tests in them | 5 |

---

## 1. Architecture

### 1.1 Where it runs

The reifier runs once per module, while the checked artifact is published
(`src/check/checked_artifact.zig:37882-37887`), because "the walk reads checked
bodies and solved types, neither of which exists while the checker runs". A
module with no `Code` site returns before any work happens
(`src/check/code_reifier.zig:6419`). The result is a `ConstStore` node attached
to the site's checked expression, serialized with the artifact, and restored
when compile-time evaluation runs the translator.

Normalization runs in the same place, for the same reasons:

| Property | Consequence |
|---|---|
| the walk already reads the explicit data normalization needs: solved types, static dispatch plans, instantiations, resolved references | normalization consumes explicit data from earlier stages and reconstructs nothing, as `AGENTS.md` requires |
| a module without a site does no work | the feature costs nothing to programs that do not use it |
| the output is part of the checked artifact | normalization runs only when the module's artifact key changes, and a cache hit replays the stored normal form |
| the translator reads the normal form during compile-time evaluation | no new pipeline stage, no new cache boundary |

### 1.2 Four representations, compared

The choice is what the reifier builds and what normalization reads.

| Option | Reifier builds | Normalizer reads | Verdict |
|---|---|---|---|
| A. post-process the value | `Code.Ir` values in `ConstStore`, as today | the same `ConstStore` values | rejected |
| B. `Code.Ir` becomes a MIR | a native Zig tree shaped like `Code.Ir` | that tree, lowered into a normal-form IR | rejected |
| C. build the normal form directly | the normal-form IR, through smart constructors | the same IR, in later passes | chosen |
| D. reuse the post-check pipeline | nothing new: Monotype, Lambda Mono or LIR of the reached procedures | that IR | rejected |

Why each rejected option loses:

| Option | Clarity and modularity | Compile time | Fatal problem |
|---|---|---|---|
| A | every rule matches on `ConstValue` tags whose names are strings (`src/check/const_store.zig:434`), with types as nested `Ty` values | each rule compares text; no hash-consing, so value numbering needs a second index; every pass allocates new store nodes that are never freed from the artifact | the store is the serialized output format, and using it as a working IR bloats the artifact with every intermediate |
| B | a clean split: walk, then lower | one extra allocation and one extra traversal per node, for a tree whose only reader is the lowering | the tree records exactly what the normal form erases: names, nesting order, `Let` chains, syntax variants. A stage that exists to hold information the next stage deletes adds a pass and a representation, and gives nothing back |
| C | one IR with two invariant levels, raw and normal; every rule is written once and runs during the walk, after inlining, and in the fixpoint | one traversal of the checked body, with rules applied as nodes are built | none: see 1.3 |
| D | reuses specialization, lambda lifting, pattern lowering, join scalarization and the range prover | lowers every reached procedure through Monotype, lambda solving and LIR per site, which is the most expensive part of the compiler | the normal form would change whenever the optimizer changes: safe against refactors, unsafe against compiler upgrades, the D1 problem of `roc-reify-whole-design-alternatives.md`. LIR also erases what translators need: builtin identities become low-level ops, nominal types become layouts, and arithmetic is already committed (`design.md:13491`) |

Option D's algorithms are still worth having. Section 1.6 lists the two that
normalization reuses as libraries, without depending on the pipeline around
them.

### 1.3 The chosen shape

```
checked body ──walk──▶ builder ──▶ raw rows ──simplify, finalize──▶ normal rows ──emit──▶ ConstStore
 (TypedCIR)   (code_reifier)  │                 │                          (Code value)
                              │                 └──▶ provenance ─────────▶ artifact side table
                              └── smart constructors: every local rule, applied on construction
```

Three decisions define it.

1. One IR. The normal-form IR is the only IR. "Raw" and "normal" are
   invariant levels of one data structure, checked by one verifier (5.2).
   The walk produces raw rows: every local rule has already run, but global
   steps, such as row identity, placement and numbering, have not.
2. Rules are smart constructors, declared in one table. `builder.field(x, "f")`
   returns the component when `x` is a `Record`; `builder.switch(t, arms)`
   takes the arm when a dominating fact decides `t`. Each rule of the
   normal-form document's simplify phase is one row of a table: the op at its
   root, the patterns of its arguments, its side condition and its result. The
   constructors dispatch on the table, and a rule builds its result only
   through the constructors, so a result that is itself a redex is rewritten at
   once. The walk, inlining and the fixpoint all build through the same
   constructors, so rules cannot diverge between phases, and the confluence
   tests, the knockout switch and the version fingerprint all read the same
   table. Braun et al. (2013) build SSA form from an AST in one pass with
   on-the-fly simplification in the same way; Cranelift declares its rewrite
   rules as data in ISLE for the same reasons.
3. The fixpoint is a rebuild. A simplify round copies a row through the
   builder, walking from the row's terminators, so a node nothing reads is
   never copied and N6 costs nothing. The row rules (N7, N11, N12, N14) are
   hooks on the rebuild, so what they enable fires in the same round. A round
   that changes nothing ends the phase, and a later round copies only the
   regions whose inputs changed. There is no worklist to maintain, and a rule
   has no ordering hazard between rounds.

The pipeline, which is the one definition of what runs when. Normal-form 3.0
states the same phases:

| Stage | Runs | Scope | Steps |
|---|---|---|---|
| walk | once | per module, every row the module's sites reach | construct steps of 3.2, with every smart constructor of 3.3 |
| rows | once | per module | N8e: the call graph and its components, which order the next two stages |
| simplify | to a fixpoint | per component, callees first | the rebuild with late scheduling (3.3), with the row rules of 3.4 marked "fixpoint" as hooks |
| finalize | once per component | as soon as its fixpoint ends, before any caller | the component checked again, and split parts simplified callee-first; N8f, N8g, identical rows merged (3.5) |
| number | once | per row | N5b hoisting, N9 |
| views | once | per site | V1, then V2 or V3 if the site's type asks for them, each followed by the simplify stage on the rows it changed and by 3.5 |
| emit | once | per module | I8, with rows shared across sites by digest |

Three rules govern the simplify stage:

| Rule | Why |
|---|---|
| a caller is simplified once, after its callees are finalized; a row created during simplification, a specialization or a part of a split component, is simplified and finalized on demand | a caller sees each callee as it will be emitted: its canonical row, its final parameters and its `speculatable` flag. Work is the sum over components of rounds times size, and no caller is simplified twice for a callee's sake |
| value numbering is canonical in the rebuild: it visits a region's own nodes before the regions nested in it, in dominator pre-order; the per-scope lookup during the walk is a fast path, not the definition | a lookup at construction depends on whether the walk met the outer or the nested copy first, so two orders of independent bindings could give two normal forms |
| the rebuild schedules late: before each round, each node gets its latest region, the innermost that encloses all its uses, at no deeper loop depth than the source's; it is built there, under that region's facts | the facts that apply to a node depend on its uses, not on where the source wrote it. Rules that compare regions compare a region's end and its dependencies structurally (`src/reify/equal.zig`). Hoisting out of loops (N5b) runs after the fixpoint and changes no region's contents |

Rejected within C: an e-graph with extraction (egg, Cranelift's aegraph) as the
engine. An e-graph keeps every equivalent form and extracts one. Extracting the
least term under a fixed well-order would be canonical, and that order is the
reduction order completion needs anyway, so extraction is not the obstacle.
Saturation is: it has no general bound, and the rules here read context, such
as dominating facts and loop depth, which an e-graph's congruence closure does
not model. An e-graph is used instead as the test oracle of 5.7.

### 1.4 Which `Code.Ir` constructors change representation during the walk

"Straight away" is the rule for everything that is spelling. The walk never
emits the left column; it calls the builder for the right one.

| `Code.Ir` today (`src/build/roc/Builtin.roc:22843-23018`) | The walk builds | Step |
|---|---|---|
| `Lambda(params, body)` | a row with positional params | N2, N8 |
| `Param(Str)`, `Local(Str)`, `Let(Str, bound, rest)` | a reference to a param or node; no binder node | N2, N3, N4 |
| `Lit(Lit)` | `Lit`, one per value and type, hash-consed | N1, N5 |
| `Binop(Str, a, b)`, `Unary(Str, a)`, `Call(builtin, args)` | `Prim(PrimId, args)`, `PrimId` interned from the export name and carrying owner and method apart | N1 |
| `Call(user function, args)` | `Call(RowRef, args)`; the name goes to provenance | N8 |
| `Call` of a function in the site's cut | `Prim` by qualified name; the body is not walked | N8h |
| `Field`, `OptField`, `Index` | the same ops, through smart constructors | N13 |
| `MakeRecord`, `MakeTuple`, `MakeList`, `MakeTag` | `Record` in the type's field order, `Tuple`, `List`, `Tag` | N1, N9 |
| record update `{ ..r, f: v }` | a full `Record` of `Field(r, g)` reads | N1 |
| `If(c, t, e)` | `Switch` on a `Bool`, with one output per value it delivers: the `if`'s value, and each `var` an arm assigns | N1 |
| `and`, `or` | n-ary `And`, `Or`, each operand after the first a region | N1, N15 |
| `Match(x, branches)` with `Pattern`s | a cascade of `Switch` nodes in source order, first match wins, which N7 turns into the canonical tree (phase 1 at M4, phase 2 at M5) | N7 |
| `Crash(msg)` | `Crash`, not speculatable | N1 |
| `Derived(method, ty, args)` | `Derived`, unchanged | none |
| `Range(a, b, end)` | no node: the `ForRange` that reads it carries its bounds | N11 |
| `For`, `While`, `Break`, `Return` | `ForRange`, `ForList` or a general `Loop`; `Continue`, `Break` and `Return` as region terminators, not values; the code after an exiting statement as a join | N11 |
| a call through a function value the walk does not know | `Apply(f, args)`, resolved by simplification, or refused once every component is final | N8i, N8j |
| `Meta { ty, region }` on every node | an interned `TyId` on the node; the region goes to provenance | N10, I2 |

The Roc-side `Code.Ir`, `Code.Pattern` and `Code.Branch` unions are removed
from `Builtin.roc`. `Code`'s backing (`Builtin.roc:22491`) becomes the
normal-form value of normal-form section 10.1, and `Code.ir` and
`Code.definitions` (`Builtin.roc:23121-23134`) are replaced by the views of 1.5.
The examples and fixtures that read `Code.Ir` (`examples/reifying/glsl`,
`examples/reifying/sql`, `test/cli/Staged*.roc`) are ported in the same
milestone (M1), so no stage emits both forms.

### 1.5 Views: computed only where a site asks for one

`graph` is cheap. `inline` can grow exponentially with call depth, and
`outline` runs over `inline`. Roc is strict and a `Code` value is a constant, so
a view cannot be computed lazily when a translator first reads it. Three
choices:

| Choice | Cost | Problem |
|---|---|---|
| compute all three views for every site | `inline` and `outline` for every site, used or not | pays the most expensive step for translators that read `graph` |
| a compile-time intrinsic that computes a view on demand | only what is read | a `Code` constant can reach run time, and every backend would then need the normalizer |
| the site's declared type selects the view | only what is read | two more opaque types in `Builtin` |

Chosen: the declared type. `Code(f)` carries `graph`; `Code.Inlined(f)` carries
`inline`; `Code.Outlined(f)` carries `outline`. The site rule, which already
recognizes a `Code(f)` parameter, recognizes the three, and the reifier reads
which one the checker resolved. That is explicit data from the checker, not an
inference. `inline_digest` is computed from `graph` rows without materializing
`inline` (normal-form 4.3), so it is available in every view.

### 1.6 Modules

A new Zig module, `reify`, owns the IR and every pass. It depends on `base` and
`collections` and on nothing in `check`, so its tests build graphs directly,
without a checker, in milliseconds.

| File | Holds | Depends on |
|---|---|---|
| `src/reify/ir.zig` | rows, regions with their terminators, nodes, value refs; struct-of-arrays pools with `u32` ids | none |
| `src/reify/types.zig` | interned `TyId`: aliases expanded, fields and tags in canonical order, nominals by name | `ir` |
| `src/reify/prims.zig` | the builtin table: per `PrimId`, owner and method, speculatable or not, associativity, identity and absorber, law membership | `ir` |
| `src/reify/builder.zig` | smart constructors dispatching on the rule table, hash-consing, the dominating-fact stack, late scheduling, provenance recording | `ir`, `types`, `prims`, `rules/*` |
| `src/reify/rules/table.zig` | the rule table: per rule, its root op, argument patterns, side condition and result, as data the builder matches and instantiates; sequence variables stand for runs of `And`, `Or` and chain operands; the knockout switch in test builds | `ir`, `prims` |
| `src/reify/rules/ledger.zig`, `ledger.zon` | the rule-derivation tool's record (`roc-reify-rule-derivation.md` 3.6): the rows it admitted, and the equations it kept out of the table, each with its reason and witness | none |
| `src/reify/match.zig` | N7 decision trees | `builder` |
| `src/reify/driver.zig` | the pipeline of 1.3: components in callee-first order, the fixpoint of each, its finalization, and rows created on demand | every pass |
| `src/reify/rows.zig` | call graph, SCCs and their recheck, N12, `Apply`, parameter renumbering, digests, merging identical rows | `builder`, `type_digest` |
| `src/reify/loops.zig` | N11 slot and raising rules | `builder` |
| `src/reify/scalar.zig` | N14 | `builder` |
| `src/reify/ranges.zig` | N13u intervals: interval arithmetic per op, the entries the fact stack keeps, and the result range N8k records | `ir`, `prims` |
| `src/reify/laws.zig` | N16, layer L | `builder`, `prims` |
| `src/reify/place.zig` | latest regions for the late schedule, and N5b hoisting | `ir` |
| `src/reify/number.zig` | N9 canonical numbering | `ir` |
| `src/reify/views.zig` | single-use inlining, `inline` with `inline_digest`, `outline` | `builder`, `number` |
| `src/reify/verify.zig` | the invariant checker of 5.2 | `ir`, `prims` |
| `src/reify/eval.zig` | a reference evaluator of the normal form, for tests only | `ir`, `prims` |
| `src/reify/dump.zig` | the text form used by golden tests and `roc reify --dump` | `ir` |
| `src/check/code_reifier.zig` | the walk, retargeted from `ConstStore` to the builder | `reify` |
| `src/check/code_emit.zig` | the normal form written into `ConstStore` | `reify`, `const_store` |
| `src/build/roc/Builtin.roc`, `Code.Graph` | the value's types and the utilities of 1.8 that are written in Roc | the emitted value only |

Reused as libraries, not as pipeline stages:

| Reused | From | For |
|---|---|---|
| structural digests of cyclic graphs, "reduces cyclic components by bisimulation before hashing positions ordered by label" | `src/postcheck/type_digest.zig` | row identity of recursive components (N8d). Bisimulation replaces the permutation search over tied members that normal-form 3.8 describes, so the cost has no factorial term. The file moves to a module both `postcheck` and `reify` can import |
| the numeric operations the interpreter runs, `float_math` included | `src/builtins` | constant folding (N13j) computes exactly what Roc computes, with the same bits on every host, because it calls the same code (1.9) |

`src/postcheck/match_tree.zig` is not reused. Its column choice reads the
clause matrix, which depends on arm order, and N7's split rule must not. Its
sharing invariant is adopted: "rows (branches) are never duplicated during
specialization" (`design.md:13311-13318`), so decision trees stay linear in
pattern size.

### 1.7 Data layout

The layout serves the two hot operations, hash-consing and rebuilding.

| Choice | Why |
|---|---|
| nodes in struct-of-arrays pools: `op`, `ty`, `flags`, `args` as a range into one `u32` pool | a rebuild round streams pools; no per-node allocation |
| one arena per module's reification, freed after emission; per-site view state in a child arena | a row that ten sites reach is normalized once; normalization leaves nothing behind except the emitted value |
| `PrimId`, `TyId`, `RowRef`, `NodeRef` are `u32` | equality is integer equality everywhere, including in hash keys |
| hash-consing key: `(op, args, ty)`, in one table per row whose entries carry their region; regions carry pre-order and post-order numbers, so "encloses" is two comparisons; literals compare by their bits | a node written twice is found in one lookup, however deep the regions nest; the rebuild's dominator pre-order makes the result independent of build order (1.3); `-0.0` and `0.0` stay two nodes |
| the dominating-fact stack: a scoped map from `(NodeRef, position)` to the known tag or literal, pushed on entering a switch arm, a later `And`/`Or` operand, or a `ForRange` or `ForList` body | N13's dominating-test rules are one lookup at construction; with late scheduling, the facts on the stack are those of the node's latest region |
| provenance as a parallel array: node to a range of `(site, region, call path)` entries | the walk writes it as it goes; nothing reads it except diagnostics and the dump; a row shared across sites keeps each site's entries apart (1.10) |
| rows keyed by `DefinitionKey` during the walk, as today, and by digest once finalized | the walk's memoization is unchanged; a caller's `Call` names the canonical row; the emitter deduplicates by digest across all sites of the module |
| digests are 128-bit content digests, Merkle-style: a node's from its op, type and its arguments' digests; a region's from its end; computed when a node is built or a region closed | identical rows merge in one lookup, and the answer does not depend on where N5b will place their nodes. Equal digests are confirmed by a structural comparison before two rows merge, so a collision never merges two computations. N7d compares two arms structurally, not by digest, because a digest names a parameter by the region that binds it and so separates arms that bind equal regions of their own (normal-form 3.0) |

### 1.8 Built-in utilities for translators

The normal form is canonical, but it is not the shape every translator emits.
A GLSL translator emitting one expression wants a tree, SQL wants to know that
a loop scans a list, DBSP wants operator IDs that survive a refactor. If each
translator derives these itself, each writes a slightly different rule, and a
rule that reads anything outside the normal form brings back the instability
the normal form removed. So `Code.Graph` ships a fixed set of utilities.

Three rules decide the set:

| Rule | Consequence |
|---|---|
| a utility is built in when translators of one kind all need it, and when a hand-written version could disagree with another translator's or read something that is not invariant | `to_tree`, `iteration` and `inline_digest` are built in; a translator's naming scheme is not |
| a utility is written in Roc in `Builtin.roc` when it is a function of the emitted value alone | it costs nothing unless a translator calls it, it has one implementation, and it cannot read names, regions or provenance, because they are not in the value. Its invariance under R holds by construction, with no verifier rule to enforce it |
| a utility is written in Zig, and computed at publication, only when it needs the normalizer: the simplify rules, the digest function, the site's type | views and `inline_digest`; everything else stays out of the compile-time budget of section 2. A classification that normalization itself needs, such as whether a loop is bounded, is made once by the normalizer and stored in the node, so no utility repeats it |

A target's cost model is never built in. Whether to recompute a shared value or
store it, and whether a missing feature is a refusal or a workaround in the
target, belong to the translator.

| Utility | Answers | Written in | Cost | Step, milestone |
|---|---|---|---|---|
| `graph`, `inline`, `outline`, by site type | which rows the translator sees | Zig, at publication | 2.2 | V1 to V3, V6 |
| `to_tree` | the row as nested expressions | Roc | O(n) per call | V4, M1 |
| `uses` | the users of each node in a region, and their count | Roc | O(n) per region | V8, M1 |
| `children` | a node's arguments and owned regions, for generic walks, as `Ir.children` and `Ty.children` do today (`Builtin.roc:23073`, `:22567`) | Roc | O(arity) | V8, M1 |
| `inputs` | the root parameter's fields by name, for host bindings | Roc | O(fields) | V5b, M1 |
| `iteration` | what a loop iterates over, read off `ForRange`, `ForList` or `Loop` | Roc, over the node the normalizer classified | O(1), plus a scan of the body for `exits_early` | V7, M6 |
| `inline_digest` | a node identity stable under R and helper extraction, on `Code.Inlined` values | Zig, while `inline` is built, stored per node | O(size of `inline`), which the site already pays | V5a, M8 |
| `refuse_at` | a refusal the compiler reports at every source region the node has in this value's site | Roc constructor; the compiler reads it | none | I9, M8a |
| `is_eq`, `to_hash` on `Code` | equality of normal forms, ignoring the site key | Roc, by hand rather than derived (1.10) | O(n) | I10, M1 |
| `version` | the normal-form version, for translators' cache keys | Roc, a stored constant | none | I11, M1 |

`to_tree`, `uses` and `children` land in M1, not with the views in M8: the GLSL
example emits one expression, and without `to_tree` porting it in M1 would mean
writing a tree rule into the example, which is the thing 1.8 exists to avoid.

#### `to_tree`

The rule is normal-form 5.4. It reads two facts the graph records for every
node: its uses, and the kind of region each use is in. Under C2 (1.9) it needs
no crash information: substituting a node into a switch arm or an `And`/`Or`
operand evaluates it in fewer cases, which C2 allows.

| Node | In the tree |
|---|---|
| literal, parameter | substituted at every use |
| used once, in the same region | substituted at the use |
| used once, in a nested switch arm or `And`/`Or` operand | substituted into it |
| used once, inside a loop body or a lambda | kept as a def outside, because substituting would repeat its work on every turn |
| used more than once | kept as a def, so shared work stays shared |

Normal-form 10.1 declares `to_tree : Graph, RowId -> Tree` without defining
`Tree`. The type:

```roc
Tree := [
	Op({ op : Op, args : List(Tree), ty : Ty }),    # a substituted node
	Param(U32),
	Slot(U32),
	Def(U32),                                        # a reference to a kept def
	Block({
		defs : List({ id : U32, value : Tree }),     # kept defs, in N9 order
		end : [Value(List(Tree)), Jump(U32, List(Tree)), Return(Tree), Continue(List(Tree)), Break(Tree), Branch(Tree)],
	}),
]
```

Every region becomes a `Block`, and a block with no defs and a `Value` end is
that value's tree, so a body without shared work is one expression. A `Switch`,
`ForRange`, `ForList`, `Loop`, `And` or `Or` op carries its regions as `Block`s
among its args, an exiting switch carries its joins as `Block`s too, and a
path ends in the `Jump`, `Continue`, `Break` and `Return` of the IR.
 So `a and b` reaches a GLSL translator as an
`And` it prints as `&&`, and `for x in xs` as a `ForList` it prints as a `for`
loop, with no shape to recognize.
An `if` reaches it as a `Switch` on a `Bool` with two blocks, which is `?:`
and `CASE WHEN` already, so the tree has no `Select`. The `speculatable` flag
on the nodes of each `And`/`Or` operand and each arm tells a target without
short-circuit evaluation, such as SQL's `AND`, whether it may evaluate them
eagerly. Kept defs have no names,
only node indices.

`to_tree` never duplicates work. A target without local variables substitutes
kept defs itself or refuses them, because only the translator knows whether
the repeated work is acceptable. The type is added to normal-form 10.1 when
M1 lands, as 3.7 does for the new rules.

### 1.9 Semantic decisions

Four decisions change what the normal form promises. Each removes work from
several steps, so the plan builds on them from M1. Normal-form 1.1, 3.13 and
3.15 state them; this section records what each does to the implementation.

| Decision | Replaces | Simplifies | Costs | Steps |
|---|---|---|---|---|
| C2: the normal form gives the body's result wherever the body neither crashes nor diverges, and never evaluates a computation that is not speculatable where the body would not | strict crash tracking: C1, a `may_fail` flag on every node and every builtin, obligations for dead nodes that can fail, failing nodes pinned to their region | a `speculatable` flag from a short explicit list, where a builtin not on the list is not speculatable, which is exact; no obligations anywhere, in the IR, the API or `to_tree`; nodes sink into branches freely; dead nodes go; the bounded-increment rule is not needed, so the hand-written counter and the range step meet as they are; "move a binding into a branch" and "drop a dead binding" join R | a translator that wants Roc's crashes exactly, such as an interpreter, sees fewer of them; the language creator must accept C2 for reified bodies | I3, N5b, N6, N13a, N13c, N13g, N13k; N13l removed |
| constant folding through Roc's own float implementations | the worry that folding depends on the host's math library | everything folds, `sin` included: `src/builtins/float_math` is software in strict float mode (`src/builtins/float_math/f32.zig:245`, `src/builtins/float_math/tan.zig:14-15`), the same code compile-time evaluation already uses for top-level constants | a guard: the folder calls only those implementations, never `@sin` or a host library, and a test pins the bits on every CI platform | N13j, I3 |
| the translator's cut, and every other body read: a function in the site's cut is a primitive; every function outside it is walked, in any package | the reach rule of `roc-reify-refactor-safety.md` 4.3, under which a function of another package is read only when its author exposed its body, and a declaration that exposes a body | no declaration on libraries; one mechanism, the cut, decides what a translator reads by name, per translator, so GLSL keeps a math library's `lerp` as `mix` and SQL reads its body | a dependency upgrade can change a translation, or stop it building at the site, when a body the site reaches changes its normal form. The upgrade is explicit, since packages are pinned by URL and content hash. The normal form depends on the cut, so rows are shared by digest only between sites with one cut | I14, N8h, N8l |
| n-ary `And` and `Or` nodes, each operand after the first a region | `and` and `or` as a `Switch` | `(a and b) and c` meets `a and (b and c)` by flattening, which the `Switch` encoding could reach only with a case-of-case rule; expression targets get `&&` and `AND` without recognizing a shape; a nested `if` with a repeated `else` meets `if a and b` by one rule on region digests | one more op family in the rules, the fact stack and outlining's shape hash | N1c, N13o, N13p, N15b, N7d |

If the language rejects C2, the strict variant returns, and the plan changes in
exactly these places: I3 gains a flag per builtin with a completeness test
over every public builtin; N5b pins nodes that can fail to their region; N6
turns dead nodes that can fail into obligations, which the IR, the API and
`to_tree` carry; N13a, N13c and N13g gain their obligation conditions; N13l
returns; and the L5 differential accepts two crashes with different messages
instead of anything where Roc crashes.

### 1.10 Complications of leaving the plain `Ir`

The plain `Ir` gave translators names, spelling and one description per site.
Taking those away surfaces eight complications. Four more were resolved by
1.9: the crash flag for about 2,259 builtins (by C2), cross-host float drift
(by `float_math`), recovering `&&` from a `Switch` (by `And` and `Or`), and
loops that could never be removed because they might not terminate (by C2,
which drops dead loops like any dead node; bounded loops are `ForRange` and
`ForList` nodes, speculatable when their bodies are, so an invariant one can be
hoisted).

| Complication | Evidence | Design answer | Steps | Tests |
|---|---|---|---|---|
| translators recognize functions of their own library by name, and inlining would replace them with their CPU bodies | `Glsl.roc` maps `Glsl.Vec3.scale` to `*` and `Glsl.Sampler.texture` to `texture` (`examples/reifying/glsl/Glsl.roc:516-517`, `:552`) | a function in the site's cut is a `Prim` named by its qualified name, never walked, not speculatable. Until M13 the cut is every function of another package; from M13 the translator declares it (1.9) | N8h, M1; I14, M13 | the GLSL example keeps its output; a refactor inside a `Glsl` function body leaves the caller's normal form unchanged; renaming it changes it |
| walking an opaque nominal's own method reads the representation the opaque hides, and the walk then meets a field access that the opaque's type does not have | `Sealed :: { x : U16 }` with a written `is_eq` (`test/cli/StagedNominalMethods.roc:123-126`) | a method of an opaque nominal that is not a builtin is a `Prim` named by the nominal and the method, never walked, as N8h does for another package's function. A derived method over an opaque stays refused | N8h, M1 | "an opaque nominal's own method is named, not walked" in `src/compile/test/code_reifier_test.zig` |
| a `Code` value's equality and its identity pull apart | rows are shared by digest across a module's sites (1.7), and translator output should be cacheable by `Code` equality | the value carries a site key; `is_eq` and `to_hash` are written by hand in `Builtin.roc` and skip it; provenance is keyed by site and node; the site module's provenance is reachable wherever compile-time evaluation runs the translator | I10, M1 | two sites with one normal form are equal and hash equal; `refuse_at` on each reports its own regions; a translator in another module reports at the right site |
| compiler upgrades change normal forms | every rule is part of the language version (normal-form 10) | `Code.version`; rules, the speculatable list and layer L change only with a language version; golden files change exactly when the version does | I11, M1 | a fingerprint test over the rule set, the speculatable list and the builtin table fails unless the version changes with it |
| template calls describe a fresh body per call | a template is called once per use, and its arguments are described into its body (`roc-reify-design.md` section 12) | cache each normal form by the digest of the rows the walk built for its site, with every type, literal, primitive and name hashed by its content; a later site whose walk built equal rows takes that normal form without normalizing | P1, M3 | work counters: k distinct argument lists over n calls normalize the body k times |
| `roc check` and the editor run normalization on every edit | compile-time evaluation runs for `roc check` too (`design.md:770`) | none in the design beyond 2.2's bounds; the latency is measured | none | 5.8: edit-to-diagnostic latency on a module with sites |
| translators that match shapes across nodes, and layer L changing those shapes | `Sql.roc` matches `List.sum(List.map(rows, ...))` (`examples/reifying/sql/Sql.roc:799`) | translators match the `inline` view through `to_tree`, and match the forms after layer L; `iteration` reports scans (normal-form 3.16) | none new | the SQL example ported to the new forms, with and without layer L |
| float literals and value numbering | `-0.0 == 0.0` and `NaN != NaN` under IEEE comparison | hash-consing and switch keys compare bits; a NaN is never a switch key | I4, M0 | L1: `-0.0` and `0.0` stay two nodes; no NaN key |
| operators carry the type in the builtin's name | `Glsl.roc:541-552` lists `Builtin.Num.F32.sin` and its siblings one by one | `Prim` carries owner and method apart, so a translator keys its table by method | I3, N1a, M1 | L1 over the emitted `Prim` |
| a rule's match that builds a node leaves it dead in the region it matched in, and value numbering then merges an identical node of a nested region into it, so that node never reaches its latest region and the row never settles | a literal switch's key was built as a `Lit` to match the key pattern (`src/reify/builder.zig`, `matchLitSwitch`); a 512-seed L4 run met it | matching builds nothing: a literal switch's key binds its pattern variable to the literal's id, and a `Lit` is built only where the rule's result reads the variable as a value. So a rebuild that rewrites nothing builds only what its row reads, and a round that changes no fingerprint leaves every row settled (`src/reify/driver.zig`) | N5a, N5d, M2 | "matching a literal switch builds no node" in `src/reify/builder.zig`; the settled check after every component |
| a node that owns regions has new region ids each time it is built, so an `if` written twice, or an `if` bound before a `match` and written in every arm, stays two nodes | the M2 L3 pair "an if bound twice" and the L4 sink into every branch | an owner is hash-consed without its region ids, and a candidate is the same node when its regions end alike (`equal.zig`). N5c merges an owner that every arm computes when it delivers a value, is not a loop that can return, and its regions read nothing from the arms; the key holds each region's content digest, and the regions are compared structurally before the merge | N5a, N5c, M2 | the L1 tests "an if written twice is one node" and "a value switch every arm computes"; the L3 pairs; the L4 sink into every branch |
| the N9 rule for loop slots, the order the walk of the body first reads each, is not a fixpoint: renumbering the slots changes which slot the walk reads first, and the order can alternate with period 2 | met while M2 built the number stage | the number stage leaves slots in their order, and the slot order joins the slot rules of M6 | N9, M6 | none: M6 left the slots in their order, so the question stays open for a later canonical slot order |
| late placement clamps every node at the loop depth of the region it stood in, so work written before a loop and read in a branch inside it is not under that branch's facts, and the same work written in the branch is. A speculatable node written in the branch is simplified by the facts and then hoisted out of the loop, so the two spellings can differ | the clamp in `late` (`src/reify/place.zig`); normal-form 3.5 | moving work across a loop boundary is outside R, for speculatable work as for failing work | N5d, M2 | the L3 pair "failing integer work moved across a loop boundary is not in R" |
| L5 must tell a crash of the reference from an error of the generated program, and the coordinator names a report's problem only by its title | `Compile Time Crash` is a `runtime_error` report (`src/check/report.zig`) | the driver reads the answer's stored value, which is `.crash` when the reference crashed, and allows no report beside warnings and compile-time crashes (`src/compile/reify_fuzz.zig`) | M2 | the seed set asserts that it reaches both rows of the C2 table |
| the driver's per-round state reads every node of the store | `stateOf` computes `live.ofStore` each round (`src/reify/driver.zig`) | none yet: O(store) per round is within 2.2's bound per module, and the work counters of 5.8 report it | none | 5.8 |

---

## 2. Compile-time cost

### 2.1 Who pays

| Program | Cost |
|---|---|
| a module with no `Code` site | none: the early return at `code_reifier.zig:8208` stays first |
| a module with sites, on a cache hit | none: the normal form is in the artifact |
| a module with sites, on a cache miss | the walk plus normalization of every body the sites reach |
| a site that declares `Code.Inlined` or `Code.Outlined` | that view, and nothing for the others |
| a module with many template calls | one normalization per distinct argument list (P1) |
| an editor running `roc check` on a module with sites | the cache-miss cost on every edit of that module; measured in 5.8 |

### 2.2 Per step

n is the number of nodes the walk emits for the bodies a module's sites reach, r the
number of rows, and p the total pattern size of the matches.

| Step | Bound | Note |
|---|---|---|
| walk and smart constructors | O(n) expected | one hash lookup per node |
| N7 decision trees | O(p) | the no-duplication invariant; a debug lint asserts the bound, like the match compiler's (`design.md:13316-13318`) |
| N8 SCCs and digests | O(n + r log r) | Tarjan, then bisimulation over rows |
| N11 slot merging | O(n log n) | optimistic value numbering over each loop body |
| N11 raising | O(loop body) per loop and round | one match of the test the body's `Branch` ends in, the slot it reads, and the `Continue` terminators |
| N11m exits and joins | O(n) per round | the code after an exiting statement is one join; inlining a join with one jump, substituting an empty join and T3 each copy at most one end, so a body with k statements that exit in some arms stays O(k) |
| case-of-case | O(outer arms) per rewrite | outer arms become joins of the inner switch; nothing is copied |
| N13u intervals | O(1) per node | one interval operation per node, at its construction; a fact is pushed and popped with its region |
| each simplify round of a component | O(size of the regions that changed) | a rebuild, which includes late scheduling, canonical value numbering, the every-arm merge, dead-node removal and the row rules as hooks; an unchanged region is reused by digest |
| number of simplify rounds | per component, at most the round bound of 2.3; a small number on real code | a round is needed only when one row rule enables another; each caller is simplified once, so a late-converging row costs only itself; the round count per component is recorded, and 5.8 reports it |
| finalize | O(size of the component) | the SCC recheck, parameter renumbering, the digest and one digest lookup |
| late schedule | O(n) per round | latest regions from the previous round's uses, by one pass over the region tree |
| N5b hoisting | O(n) | Click's schedule over the region tree: speculatable nodes to the shallowest loop depth they allow |
| N9 numbering | O(n) | one post-order walk |
| emission | O(n) | one `ConstStore` node per normal-form node, plus one per distinct type |
| Roc utilities of 1.8 | O(n) per call, in the compile-time interpreter | only when a translator calls one; counted as translator time |
| `inline` view | O(size of the result), exponential in call depth in the worst case | only for `Code.Inlined` and `Code.Outlined` sites |
| `outline` view | O(m log m) per pass over the size m of `inline` | only for `Code.Outlined` sites |

### 2.3 Hard bounds

A pathological program must fail quickly and deterministically, never hang or
exhaust memory. Each bound is a constant of the language version, and
exceeding one refuses the site with a diagnostic naming the bound:

| Bound | Guards |
|---|---|
| simplify rounds per component | a long chain of rules that enable one another. Rounds do not grow with the size of a row, only with that chain's length, so the bound refuses no site for being large. A missed termination argument is caught earlier: after every round the driver checks that the measure of normal-form 3.0 fell, and a round in which it did not is a compiler bug, reported as one. The measure is lexicographic, so it proves termination but yields no round count to use as the bound |
| nodes in the `inline` view | exponential inlining |
| decision tree size per match | a regression of the no-duplication invariant, in debug builds |

### 2.4 Against today

The normal form is usually smaller than today's `Code.Ir` value. Today every
node carries a `Meta` node with a region, and every binder carries a `Str`.
The normal form carries neither, and hash-consing merges repeated work. The
translator, which runs in the compile-time interpreter, reads fewer nodes too.
Emission size, walk time and normalization time are measured on the GLSL and
SQL examples before M1 and after every milestone (5.8).

### 2.5 A follow-up to measure, not to build first

Each site module walks and normalizes the foreign callees it reaches, so two
modules that reach one helper normalize it twice. A content-addressed cache of
normalized rows, keyed by the defining artifact key and the instantiation,
would remove the repetition. Build it only if the measurements of 5.8 show
foreign rows dominate.

---

## 3. The steps

Every step is one unit of work with its own tests (section 5). The table is
exhaustive over the normal-form document: every rule it states is a row here.
"Where" says whether the step is a smart constructor (SC) that runs during the
walk and in every later rebuild, or a pass.

### 3.1 Infrastructure

| ID | Step | Where | Normal form |
|---|---|---|---|
| I1 | IR pools, ids, arena; regions with terminators; the `ForRange`, `ForList`, `Loop` and `Lambda` ops | `ir.zig` | 2, 10.1 |
| I2 | type interning: aliases expanded, fields by name, tags in union order, nominals by name | `types.zig` | 2 |
| I3 | builtin table: owner and method, the speculatable list, associativity, identity and absorber, law membership | `prims.zig` | 1.1, 3.15 |
| I4 | builder with one hash-consing table per row and regions numbered for "encloses", literals compared by bits, 128-bit Merkle digests of nodes and regions, the fact stack, and late scheduling; a rules-off mode that builds nodes without applying any rule, compiled only into test builds and `zig build reify-rules`, which the critical pairs of 5.7 and the rule-derivation tool build their terms with | `builder.zig`, `place.zig` | 3.0, 3.5 |
| I5 | verifier | `verify.zig` | 5.2 here |
| I6 | reference evaluator | `eval.zig` | 9 |
| I7 | dump text format | `dump.zig` | 6 |
| I8 | emitter to `ConstStore`; the Roc-side `Code` value | `code_emit.zig`, `Builtin.roc` | 10.1 |
| I9 | provenance recording and `refuse_at` diagnostics | `builder.zig`, reporting | 3.10, 6 |
| I10 | the site key in `Code`; hand-written `is_eq` and `to_hash`; provenance keyed by site, and reachable from compile-time evaluation in other modules | `code_emit.zig`, `Builtin.roc`, reporting | 10 |
| I11 | `Code.version` and the rule-set fingerprint | `prims.zig`, `Builtin.roc` | 10 |
| I12 | the pipeline driver: per-module arena; components in callee-first order, each simplified to its fixpoint and then finalized; rows created during simplification simplified and finalized on demand; the round bound and the check after every round that the measure fell; per-site view stage | `driver.zig` | 3.0; 1.3 here |
| I13 | the rule table: every smart-constructor rule as root op, argument patterns, side condition and result; dispatch, the knockout switch that disables one rule in test builds, the fingerprint of I11 and the overlap list of 5.7 read from it | `rules/table.zig` | 3.0 |
| I14 | the translator's cut: the well-known item `code_primitives` of the nominal type that owns the `Code(f)` function, a function reference or a tuple of them (normal-form 12); the checker's lookup through that type, its check of the form and of duplicates, and the cut recorded in the checked artifact for that type's sites | checker, checked artifact, site rule | 3.8, 12 |

### 3.2 Construct: during the walk

| ID | Step | Where | Normal form |
|---|---|---|---|
| N1a | operators, method calls and builtin calls to `Prim` | SC | 3.1 |
| N1b | `x \|> f(y)`, `f(x, y)`, `x.f(y)` to one call in parameter order | walk | 3.1 |
| N1c | `if` to `Switch` on `Bool`; `and`, `or` to n-ary `And`, `Or` | walk | 3.1 |
| N1d | `?` and `??` to a `Switch` on the `Try` tag, `?`'s `Err` arm ending in `Return`; an early `return` to a `Return` terminator | walk | 3.1 |
| N1e | interpolation to a `Str.concat` chain | walk | 3.1 |
| N1f | destructuring to `Field`, `Index`, `Payload` | walk | 3.1 |
| N1g | record update to a full `Record` | walk | 3.1 |
| N1h | omitted default fields written in | walk | 3.1 |
| N1i | literal spelling to one `Lit` | SC | 3.1 |
| N1j | `expect` erased | walk | 3.1 |
| N1k | `!=` to `Bool.not` of `is_eq` | SC | 3.1 |
| N1l | `is_gt(a, b)` to `is_lt(b, a)`, `is_gte(a, b)` to `is_lte(b, a)`, for builtin number types | SC | new, see 3.7 |
| N1m | derived structural `==` and hashing expanded into field operations, as the reifier does today | walk | 3.1 |
| N2 | positional params and node refs | walk | 3.2 |
| N3 | single assignment for `var`, with loop-carried `var`s as slots | walk | 3.3 |
| N4 | no `Let`: bindings are refs, independent nodes unordered | walk | 3.4 |
| N10 | provenance for every node | builder | 3.10 |
| N11a | `while` to `Loop` | walk | 3.11 |
| N11b | `for` over `a..<b` to `ForRange` | walk | 3.11 |
| N11c | `for` over `a..=b` to an inclusive `ForRange` | walk | 3.11 |
| N11d | `for` over a `List` to `ForList` | walk | 3.11 |
| N11e | `for` over another iterator to a general `Loop` with an iterator slot | walk | 3.11 |
| N11f | `break`, `continue` and `return` to terminators that end the arm they are written in; a statement that exits in some arms to an exiting switch, and the code after it to one join the continuing arms jump to (T1); `Return` in any region, `Continue` and `Break` in loop bodies | walk | 3.11 |
| N8a | local functions lifted to rows, captures as leading arguments | walk | 3.8 |
| N8b | a lambda passed as a value to `Closure(row)` with captures | walk | 3.8 |
| N8c | eta: `\|x\| f(x)` to `Closure(f)`; its call half: a call of a finalized row, not recursive, whose body only calls another row over its parameters, to that call | SC | 3.8 |
| N8d | known-function specialization keyed by the function's digest, not the call site | walk, then rows | 3.8 |
| N8h | a function in the site's cut to `Prim` by qualified name, not walked, not speculatable; until I14, the cut is every function of another package | walk | 3.8 |
| N8l | a function of another package outside the cut walked as a function of the same package; its body enters the normal form | walk | 3.8 |
| P1 | a site's normal form memoized by the digest of the rows its walk built, which reads types, literals, primitives and names by content, because each site has a store and a type table of its own; a site with an earlier site's digest is not normalized again | walk | none: performance |

### 3.3 Simplify: smart constructors, applied in every rebuild

| ID | Rule | Normal form |
|---|---|---|
| N5a | value numbering: a node merges into an identical one in an enclosing region; canonical in the rebuild's dominator pre-order, with the walk's lookup as a fast path; `Call` keyed by the callee's finalized row | 3.5 |
| N5d | late schedule: each node built in its latest region, at no deeper loop depth than the source's, under that region's facts | 3.0, 3.5 |
| N5c | a node that every arm of a `Switch` computes, from values outside it, merged into one node in the switch's region | 3.5 |
| N6 | dead nodes: the rebuild copies only what a row's terminators reach; unread switch outputs removed from every arm | 3.6 |
| N7c | nested literal switches on one scrutinee merged into one, so `if x == 1 ... else if x == 2` meets `match x`, when the outer switch is closed | new, see 3.7 |
| N7d | a nested `Bool` switch whose other arm computes the same value as the outer one, compared structurally, merged into an `And` or `Or` condition, with the two mirrors that give `And(Bool.not(a), b)` and `Or(Bool.not(a), b)`, when the outer switch is closed; over n-ary `And` and `Or`, a switch whose arm is an `And` or `Or` ending in the other arm, two switches on one pair of arms merged into a switch on a switch, and an operand both arms end in factored out | 3.7 |
| N8i | `Apply(Closure(r, captures), args)` to `Call(r, captures ++ args)`, specialized when `r` takes a function; `Apply` of a switch output whose every arm is a known `Closure` moved into the arms | 3.8 |
| N11m | exits and joins, when a switch or region is closed: T2, a join with one jump inlined there; T3, an exiting switch whose paths end in one kind of terminator to a value switch and one terminator; T4, a join without nodes substituted into its jumps; T5, an exiting switch that reaches no terminator to a value switch; T6, a `Return` in tail position to `Value` | 3.11 |
| N13a | `Field(Record(...))`, `Index(Tuple(...))`, `Payload(Tag(...))` to the component; the siblings are dropped | 3.13 |
| N13b | `Unwrap(Wrap(v))` to `v` | 3.13 |
| N13c | `Switch` on a known `Tag` or `Lit` to the arm | 3.13 |
| N13d | `Switch` at a position a dominating arm decided to that arm | 3.13 |
| N13e | `Switch` on `Bool` with arms `False`, `True` to the scrutinee | 3.13 |
| N13f | `Switch` on `Bool` with arms `True`, `False` to `Bool.not` | 3.13 |
| N13g | a switch output that every arm gives as one value available outside the arms, to that value, and the output removed; after N5c this covers every arm computing it | 3.13 |
| N13h | `Bool.not(Bool.not(x))` to `x` | 3.13 |
| N13i | `Switch` on `Bool.not(c)` to `Switch` on `c` with arms swapped | 3.13 |
| N13j | constant folding of speculatable builtins over literals, through `src/builtins`, floats included | 3.13 |
| N13k | constant folding of builtins that are not speculatable, only when this evaluation does not fail | 3.13 |
| N13m | `List.get(xs, i)` under a dominating `is_lt(i, List.len(xs))` to `Ok(Elem(xs, i))`; inside `ForList(xs)` with `i` its index, to `Ok` of the element | 3.13 |
| N13n | `Switch` on `is_eq(x, Lit)` or `is_eq(Lit, x)` over an integer, string or tag type to a literal switch on `x` | new, see 3.7 |
| N13o | `Switch` on a `Bool` with arms `False: Lit(False)`, `True: b` to `And`; with `True: Lit(True)`, `False: b` to `Or`; with `True: Lit(False)`, `False: b` to `And(Bool.not(c), b)`; with `False: Lit(True)`, `True: b` to `Or(Bool.not(c), b)` | 3.13 |
| N13p | `And`/`Or` operands that are literals, or that an earlier operand or a dominating arm decided, removed or deciding | 3.13 |
| N13q | over builtin integer types: `Bool.not` of `is_lt` or `is_lte` to the flipped comparison; a `Switch` on `is_lte(a, b)` to a `Switch` on `is_lt(b, a)` with arms swapped | 3.13 |
| N13r | case-of-case: a `Switch` on an output of a switch whose every arm gives it as a known `Tag` or `Lit`, to the inner switch, each arm continuing into the outer arm it selects; an outer arm selected more than once becomes a join | 3.13 |
| N13s | a `Switch` on a `Bool` to one on its negation with arms swapped, when the negation has fewer `Bool.not` leaves, then fewer integer `is_lte` leaves, then is an `And` or starts with a plain leaf | 3.13 |
| N13t | `Bool.not` of an `And`, an `Or` or a `Bool` switch pushed to the leaves: negation normal form | 3.13 |
| N15a | associative chains flattened into one n-ary `Prim`, identities dropped, a chain with an absorber and otherwise speculatable operands replaced by the absorber, order kept, equal operands kept | 3.15 |
| N15b | nested `And` and nested `Or` flattened, order kept | 3.15 |
| N15c | two operands of integer `plus`, `times`, or `is_eq` over builtin integers and `Str`: a literal last where the other operand is not a literal, two root parameters in parameter order | 3.15 |
| N17a | `List.len` and `List.is_empty` of a known list to a literal | 3.17 |
| N17b | `List.get` at a literal index, `List.first`, `List.last` of a known list to the `Ok` of the element or the `Err` tag | 3.17 |
| N17c | `List.get` of a known list at an index that is not a literal to a literal switch on the index | 3.17 |
| N17d | list builtins whose result's elements follow from known lists and literals to the `List` node of the result; `List.repeat` only at a length of at most B | 3.17 |
| N17e | `map`, `map2`, `map_with_index` over known lists with a known function to the `List` node of the calls; `keep_if` whose every predicate result is a literal to the kept elements | 3.17 |
| N17f | `fold`, `fold_rev`, `sum`, `any`, `all` over a known list to the chain of calls, `plus`, `Or` or `And` | 3.17 |
| N13u | integer intervals with literal bounds on the fact stack; comparisons they decide; checked arithmetic they prove speculatable; the `plus` chains N15a may flatten; the interval conditions of tier F rows | 3.13 |

### 3.4 Structure: passes over whole rows

"Runs" places each step in the pipeline of 1.3. A step marked "fixpoint" is a
hook on the rebuild: it rewrites a loop, a decision tree or a row through the
builder during the round, so the smart constructors it enables fire in the
same round. It must be idempotent, which the verifier checks (5.2).

| ID | Step | Where | Runs | Normal form |
|---|---|---|---|---|
| N7a, done | decision trees, phase 1: flat tag and literal matches, `if`, `?`. The smart constructors make the tree during every rebuild (`Builder.litSwitch`, `Builder.decidedSwitch`, the N13n row, now over `Str` too); `match.zig` holds the key order and the check of 5.2 | `match.zig` | fixpoint | 3.7 |
| N7b, done within its limits | decision trees, phase 2: nested and overlapping patterns, guards. `Builder.interchange` hoists a test of a position (field, then tag, then payload index) that an arm of a value switch makes after a position that comes later in `match.before`, so `match (a, t)` and `match (t, a)` meet. It leaves two `Bool` switches to N7d and N13o, switches on different roots to the parameter half of N15c (M11), guards, joins, switches with more than one output, and arms that hold a loop, an `Apply`, a `Lambda` or a `Closure` (`match.copyable`). `match.inversions` counts what is left | `match.zig`, `builder.zig` | on every switch | 3.7 |
| N8e | call graph and SCCs; each component checked again when it is finalized, and simplified again part by part if it split | `rows.zig` | once, and at finalize | 3.0, 3.8 |
| N12, done | self tail calls to `Loop`. `loops.tailSites` finds a row whose every call to itself is the value of a path of its body, and `rebuild.runTail` builds the row as one `Loop` over its parameters: a tail call is `Continue`, every other path end is `Break` of the row's value, and a value switch on those paths becomes an exiting switch. The component runs again after finalize merges rows that call each other alike into one that calls itself | `loops.zig`, `rebuild.zig`, `driver.zig` | fixpoint | 3.12 |
| N11g, done | invariant slots removed | `loops.zig` (`Ctx.sameKind`) | fixpoint | 3.11 |
| N11h, done | dead slots removed. Values computed only for a removed slot's next value are built once more over its initial value in the round that removes it, and the next round does not copy them | `loops.zig` (`Ctx.neededSlots`) | fixpoint | 3.11 |
| N11i, done | equivalent slots merged, by optimistic value numbering | `loops.zig` (`Ctx.refine`) | fixpoint | 3.11 |
| N11j, done | exit rules: a `Return` terminator to `Break` at a row's result, for a general `Loop` of one output of the row's type; the outputs a general `Loop` delivers and nothing reads are not carried by its `Break`s; an output every `Break` gives as one outside value is that value. A bounded loop narrows by whole slots only | `loops.zig` (`Ctx.sameKind`), `rebuild.zig` | fixpoint | 3.11 |
| N11k, done | an iterator-slot loop over `List.iter(xs)` to `ForList(xs)`, recognized by the checker-authored `IteratorProcedureId`, never by type name. The walk stores it as an `IteratorRole` on the named primitive (`ir.NamedPrim.role`), and the role is part of the primitive's content hash. The `item` is optional | `loops.zig` (`Ctx.iteratorToList`), `code_reifier.zig` | fixpoint | 3.11 |
| N11l, done | raising: a general `Loop` whose body ends in `Branch` on `is_lt(s, b)`, where `s` is the slot the test reads, of a builtin integer type, `b` is invariant, and every `Continue` steps `s` by `plus(s, 1)` or `plus(1, s)`, to `ForRange`; `ForRange(0, List.len(xs), exclusive)` to `ForList(xs)`, with `Elem(xs, index)` replaced by the element (`Builder.loopElement`, N13m over `Item`). The test may be `is_lt(s, b)` or its dual `is_lte(b, s)` with the arms swapped, because N13q does not reach an exiting switch | `loops.zig` (`Ctx.raiseCounter`, `Ctx.rangeToList`) | fixpoint | 3.11 |
| N8j | an `Apply` that a row of the site holds once every component is final refuses the site, as proposal section 10 exclusion 1 does | `rows.zig` | once, after every component | 3.8 |
| N14a, done | aggregate parameters of non-root rows split. `scalar.Usage` reads how a finalized row uses each parameter; a record or tuple that the row only reads by `Field` or `Index` has a `scalar.Shape` that says which components split, and a component that is itself such an aggregate splits again. A `Call` of that row is then a `Call` of a row built on the spot, over the components (`Builder.scalarizedCall`, `Specialize.scalarize` in `driver.zig`). The new row is the old body with each split parameter read as the construction of its components, so N13 cancels the reads; it is simplified and finalized before the call is built, as a specialization is (N8i), and it is keyed by the old row's digest and the shapes. `f(a, b)`, `f({ a, b })` and `f((a, b))` therefore merge by digest (N8g), and a component nothing reads goes at finalize (N8f). The measure counts the layers a call's callee still splits (`split_calls`) | `scalar.zig`, `builder.zig`, `driver.zig` | fixpoint | 3.14 |
| N14b, done | aggregate loop slots split. `loops.analyze` tries it after the slot rules of N11 and before a change of kind. A record or tuple slot splits when the body reads it only by `Field` or `Index` and every `Continue` of the loop gives it unchanged or as a construction (a component splits again only when it is constructed too). The new loop has one slot for each component, the initial value of a component is a read of the initial value, and a bounded loop gives one output for each component, from which the aggregate is built after the loop where something reads it | `loops.zig` (`Ctx.splitSlots`), `rebuild.zig` | fixpoint | 3.14 |
| N16a | append `ForList` to `List.map` | `laws.zig` | fixpoint | 3.16 |
| N16b | conditional append `ForList` to `List.keep_if` | `laws.zig` | fixpoint | 3.16 |
| N16c | `List.fold` with a known function to `ForList` | `laws.zig` | fixpoint | 3.16 |
| N16d | map fusion | `laws.zig` | fixpoint | 3.16 |
| N16e | `iter().map(f).collect()` to `List.map` | `laws.zig` | fixpoint | 3.16 |
| N16f | `is_eq(List.len(xs), 0)` and `is_lt(0, List.len(xs))` to `List.is_empty(xs)` and its negation | `laws.zig` | fixpoint | 3.16 |
| N11n | a general `Loop`'s leading `Bool` test on a slot decided on every edge: exiting edges jump to a join holding the exiting arm, the test goes | `loops.zig` | fixpoint | 3.11 |
| N11o | a `ForRange` slot stepped by 1 with the index, read only in the body, to `plus(i, minus(j0, a))` | `loops.zig` | fixpoint | 3.11 |
| N17g | a `ForList` over a known list of at most B elements, whose every path ends in `Continue`, unrolled: the body once per element, the slots threaded | `loops.zig` | fixpoint | 3.17 |
| V1 | single-use inlining for the `graph` view, repeated until the count stops changing; each turn simplifies the callers it changed and finalizes the site's rows again. A row whose body can end in `Return` stays a row until the rebuild turns a `Return` into a jump to the code after the call | `views.zig` | per site | 5.1 |

### 3.5 Finalize and number

| ID | Step | Where | Normal form |
|---|---|---|---|
| N8f | at finalize: non-root row parameters renumbered in first-read order, unread ones dropped, arguments permuted at every call | `rows.zig` | 3.8 |
| N8g | at finalize: row digests from content, recursive components by bisimulation; a row whose digest equals a finalized row's, confirmed structurally, merges into it | `rows.zig` | 3.8 |
| N8k | at finalize: the result range of a row with a builtin integer result, which N13u reads on each `Call` of it | `rows.zig`, `ranges.zig` | 3.8 |
| N5b | in the number stage: speculatable nodes hoisted by Click's schedule to the innermost region at the fewest enclosing loops between the latest and the earliest; the identical nodes it brings together merged | `place.zig` | 3.5 |
| N9 | in the number stage: canonical numbering of nodes, slots, switch outputs, joins and rows | `number.zig` | 3.9 |


### 3.6 Views and accessors

| ID | Step | Where | Normal form |
|---|---|---|---|
| V2 | `inline` view, with its simplify rerun; a `Closure` of a non-recursive row becomes a `Lambda` region | `views.zig` | 5.1 |
| V3 | `outline` view: cones, shapes, candidates, selection, rows | `views.zig` | 5.3 |
| V4 | `to_tree` | `Builtin.roc` | 5.4; 1.8 here |
| V5a | `inline_digest`: each node's content digest, computed while `inline` is built and stored with `Code.Inlined` values | `views.zig`, `code_emit.zig` | 4.3, 5.1 |
| V5b | `inputs` | `Builtin.roc` | 4.3 |
| V6 | `Code.Inlined` and `Code.Outlined` site types | `Builtin.roc`, site rule | 1.5 here |
| V7 | `iteration`: `ForList` as `OverList`, `ForRange` as `OverRange`, a general `Loop` as `General`, read off the node | `Builtin.roc` | 3.11 |
| V8 | `uses` and `children` | `Builtin.roc` | 1.8 here |

### 3.7 Rules that listing the steps added

Listing every step against the normal-form document found gaps. Each rule is
an exact equation in Roc and absorbs a refactor authors make:

| Rule | Absorbs | Why it is exact | In the normal form |
|---|---|---|---|
| N1l: `a > b` as `b < a`, `a >= b` as `b <= a` | flipping a comparison | for builtin number types, `is_gt(a, b)` and `is_lt(b, a)` are equal on every input, NaN included; a nominal type can define its two methods inconsistently, so the rule does not apply to it; the rule fixes one form by op, not by operand digest, so it keeps N9's numbering stable (the objection of normal-form 7.2 does not apply) | added when M4 lands |
| N13h, N13i: double negation; `if !c a else b` as `if c b else a` | negating a condition and swapping the branches | `Bool.not` is speculatable and an involution | 3.13 |
| N13n, N7c: `if x == 1 ... else if x == 2 ...` as `match x { 1 => ..., 2 => ... }`, with the literal on either side of `==` | an `if` chain versus a `match` on literals | integer, string and tag equality is speculatable and decides the same arm; floats are excluded, because `NaN == NaN` is false and a literal pattern would need its own definition | added when M5 lands |
| N13q: `!(a < b)` as `b <= a`; a `Switch` on `a <= b` as one on `b < a` with the arms swapped, over integers | `a >= b` versus `!(a < b)`, and an `if` on either with its branches swapped | integer comparison is a total order; floats are excluded, because `!(a < b)` holds for `NaN` and `b <= a` does not. With N13i the three rules join: from `Switch(Bool.not(is_lt(a, b)))` both orders reach `Switch(is_lt(a, b))` with the arms swapped | 3.13 |
| the mirrors in N13o: `if a Bool.False else b` as `!a and b`, `if a b else Bool.True` as `!a or b` | the `if` an author writes for a negated `and` or `or` | the two sides agree on every input and evaluate `b` in the same cases | 3.13 |
| N13t, N13s: `!(a and b)` as `!a or !b`; `if !a or !b x else y` as `if a and b y else x` | De Morgan's laws, in a value and in a condition | `Bool.not` is speculatable, and a negation pushed to the leaves evaluates each operand in the cases it ran | 3.13 |
| N5c: work in every arm merged before the switch | binding a value once before a `match` whose every arm reads it, versus computing it in each arm | the merged node runs on exactly the inputs that reach the switch, which is where the body ran one of the copies | 3.5 |
| the mirrors in N7d: nested `if`s whose shared arm is on the other side | `if !a { if b x else y } else y` versus `if !a and b x else y`, and the same after N13i or N13q swapped the outer arms | without them N7d and N13i do not join; with them both orders reach `And(Bool.not(a), b)` | 3.7 |
| N13r: case-of-case | a helper that returns a tag or a `Try`, matched or unwrapped by `?`, versus its tests written in place | each test runs in the order it ran and each outer arm in the cases it ran; outer arms selected twice become joins, so nothing is copied | 3.13 |
| N8i: `Apply` of a known closure, and of a switch whose arms are known closures | calling `(if c f else g)(x)` or `{ op: f }.op(x)` versus calling the functions directly | a call of a known closure is a direct call with its captures; the call moved into the arms runs in the cases it ran after the switch | 3.8 |
| T4 to T6 in N11m | `return x` as the last statement versus `x`; a join that only passes values on versus the terminator written in each arm; an exiting arm that N13 decided away | each copies at most one end, or none | 3.11 |
| N15c: `1 + a` as `a + 1`; `y == x` as `x == y` over the root's parameters | operand order of a commutative builtin, where the order cannot move under an unrelated edit | integer `plus`, `times` and `is_eq` are commutative, crashes included; the key is a literal or a root position, never a digest or a first-read number, so N9 stays stable and N8's parameter order is not read | added when M11 lands |
| N13u, N8k: literal intervals | `while $i <= n` versus `a..=n`, regrouped `plus` chains, checked arithmetic hoisted out of loops, and the conditional rows of `roc-reify-rule-derivation.md` 3.4 | each rule's condition is an interval the builder computed from literals and dominating tests; a missing interval leaves a rule unapplied | added when M11 lands |
| N11n: a leading test decided on every edge | a `$done` flag loop versus the loop with `break` | each turn runs the test on the value the edge passed, which is known there | added when M12 lands |
| N11o: a derived counter | `$j` stepped with the index versus `i + j0` | the sum equals the slot's value at every turn, so it overflows nowhere the slot did not | added when M12 lands |


N13q keeps `<=` for translators: a comparison used as a value keeps its
operator, and only a comparison a `Switch` tests is always `<`. Collapsing
every comparison to `<` and `Bool.not` would also be canonical, and would make
every expression target print `!(b < a)`.

N13n meets every rule that reads a `Bool` switch, because each can fire on
`switch(x == k, f, t)` before N13n does. The normal form keeps the literal
switch except where such a rule applies to its reading as `x == k`, as N13e
and N13f already decide for `match x { k => True, _ => False }`. The table
states this once: `rules/table.zig` derives a mirror of each first-order row
for every set of its `Bool` switch patterns on a variable, in which the switch
is `switch_#1(s, k, t, f)` and the variable reads as `s == k`. A mirror is the
row composed with N13n's equation, so it is exact; its step is the row's with
`/N13n`, and the derivation tool orients it and checks its pairs like any row.
The rule-derivation tool proposed these rows too, but its terms have no
regions, so its rows lacked N7d's `movable` conditions and its sequence
variables, and it could not admit them.

The literal half of N15c lands with N13n, not with M11: without it every
mirror and N13n itself would need a second row for `k == x`. It swaps a
literal first operand of integer `is_eq`, `plus` and `times` when the other
operand is not a literal, which the new condition `not_lit` states, and the
measure counts such calls (`unordered_leaves`). `Str.is_eq` waits for string
literals in the tool's terms. The parameter half stays in M11.

## 4. Milestones

Each milestone ends with every test layer of section 5 green for the steps it
added, the benchmarks of 5.8 recorded, and `zig build minici` passing.

The milestones are in two parts:

- 4.1, the core. These milestones answer the objection of
  `roc-reify-refactor-safety.md`. Its R table (4.1 there), the opaque value
  and `refuse_at` (4.2 there) must hold. The translator's cut and the policy
  for dependency bodies (1.9) replace its reach rule (4.3 there). The core
  also holds M6 and the rule derivation at k = 6 and k = 7.
- 4.2, the extensions. They keep their names and steps, and they come after
  the core. Each one grows R past what the safety document asks for.

Work on the core runs in the order of its table. An extension starts only
after the last core milestone, and only when a refactor that someone really
made breaks a translator.

### 4.1 The core, in order

| Order | Milestone | Steps | What becomes true | Safety document |
|---|---|---|---|---|
| 1 | M0, done | I1 to I7, I12, I13 | the `reify` module exists. Graphs can be built, verified, evaluated and dumped without a checker. The driver runs the pipeline of 1.3 with whichever passes exist. Every rule is a row of the rule table | base |
| 2 | M1, done | I8, I10, I11, N1a to N1m, N2, N3, N4, N10, N11a to N11f, N11m, N8a to N8c, N8h, N5a, V4, V5b, V8 | the walk builds the normal-form IR, and `Code.Ir` is gone. The GLSL and SQL examples and `Interp.roc` read the new value and give their expected output. The GLSL example reads it through `to_tree`, and its own library arrives as named primitives. `for` loops arrive as `ForRange` and `ForList`. Exits and `?` are built with joins, so no code after an exiting statement is copied, and exits written anywhere meet. `Code` values compare by normal form and carry a version | 4.1: rename; destructure; `and`/`or`, `?`, `??` and `return` against their `if` or `match`; move code and comments; annotations. 4.2: no names and no regions in the value. 4.3: other packages' functions are primitives |
| 3 | M2, done | N5b, N5c, N5d, N6, N9 | order and placement are canonical under C2. These rows of R hold: reorder, rename, bind twice (also once before a `match` against once in every arm), move into a branch, and drop dead code. A dominating test applies to a binding, whether it is written inside the branch or before it | 4.1: reorder bindings, bind once or twice, drop a dead binding |
| 4 | M3, done | N8d to N8g, N8i, N8j, V1, P1 | rows are digests and are finalized before their callers. These rows of R hold: helper renames, moves, generic helpers, parameter order, extraction of a helper with one use, and two identical helpers. A component that stops being recursive is treated as not recursive. A function chosen by an `if` or read from a record literal is called directly | 4.1: extract or inline a helper with one use; reorder top-level definitions |
| 5 | M8a, done | I9, V2, V6 | a translator refuses a node through `refuse_at`, and the compiler reports it at every source region of that node. A `Code.Inlined(f)` site gets the `inline` view. In it, every non-recursive helper is inlined, however many calls it has, and a `Closure` of a non-recursive row is a `Lambda` region | 4.1: extract or inline a helper with many uses. 4.2: `refuse_at` |
| 6 | M13 | I14, N8h with the declared cut, N8l; the edits of `roc-reify-refactor-safety.md` 6 | a translator declares its cut, and the site carries it. A function in the cut is a primitive (N8h). Every other function is walked by its body, in any package (N8l). The GLSL example declares `Glsl.roc`'s primitives as its cut and keeps its output. `roc-reify-proposal.md` states R, the cut, the policy of 1.9 for dependency bodies, and the table of safety section 5 | 4.3, replaced by the policy of 1.9. 6: the proposal edits |
| 7 | M14 | no new steps; tests only | each row of the safety document's R table (its 4.1), and each row of its section 2 that R absorbs, has an L3 pair that names the row and meets. Each row of its section 5 has an L3 pair that stays apart. Section 5.12 here records the matrix | 4.2: the guarantee is a test |
| 8 | M6, done | N12, N11g to N11l, V7 | there are three canonical loop forms, with the slot, exit and raising rules. The three `sum_to` bodies of normal-form 11.1 meet as one `ForRange`. `for x in xs` meets `for x in xs.iter()` and an index `while`. Translators read what a loop iterates over | none. It is the first extension, because loop form is the refactor that section 2 there shows breaking the GLSL translator. Built as normal form version 8, with limits: (1) the slots keep their order, so the N9 loop-slot rule below is still not a fixpoint question, because no rule reorders slots; (2) a bounded loop keeps one output per slot and narrows by whole slots; (3) the return-to-break rule needs a general `Loop` with one output of the row's type; (4) the language has no `continue` yet (`docs/langref/statements.md`), so the L3 pair for `continue` is the update in each branch against one update of the `if`; (5) `exits_early` counts a `Break` of the loop itself and a `Return`, and not a `Break` of a loop nested in it |
| 9 | M15 | the rule-derivation phase D5 | S1 and S2 reach an empty report at k = 6 (`roc-reify-rule-derivation.md` 5). The admitted rows enter the table through `--admit`, and criterion 1 of 6.1 there is run again, for rows whose left side has a size of 6 or less | none: completeness of the rule set up to size 6 |
| 10 | M16 | the rule-derivation phase D6 | S1 and S2 reach an empty report at k = 7. The switch-over-switch terms of G6 are enumerated. The groups that only N13r joins are filed against N13r, which lands in M5 | none: completeness of the rule set up to size 7 |

M1 is the largest, because retargeting the walk and removing `Code.Ir` must
land together. Its steps are what the walk already does under other names; M1
changes where the walk writes, not what it decides.

M3 leaves two gaps, each closed by a later step. V1 keeps a row whose body can
end in `Return`. A lambda that captures a whole record meets a helper that
takes one of its fields only once N14a splits the record (M7). M7 closed this
gap: `L3 M7: a lambda that captures a whole record meets a helper that takes the field`
in `src/compile/test/code_reifier_test.zig` pins it.

M8a leaves three gaps. A row whose body can end in `Return` stays a row in
`inline`, as V1 keeps it in `graph`; its closure still becomes a lambda. N13d
does not decide an exiting switch on a known scrutinee, because the arm
result it needs is one output. `Code.Outlined` waits for V3 (M9). A refusal is
reported at compile time by the dev backend's evaluation; the interpreter's
evaluation runs only where no problem store is present, so it never reports
one.

M13 declares the cut with the well-known item `code_primitives` on the
translator's type (normal-form 12), so it needs no new syntax. Until M13, N8h keeps every
function of another package a primitive, and no dependency body is read.

M15 and M16 change normal forms when they admit rows, so each one raises
`normal_form_version`, as every milestone that changes a rule does.

### 4.2 The extensions

They keep the order and names they had. Some of their first-order rows were
built early, while the rule-derivation tool was judged at its gate
(`roc-reify-rule-derivation.md` 6.3 and 5.2). The "Built" column lists these
rows. They stay in the table and in force. The milestone builds the rest.

| Milestone | Steps | Built | What becomes true |
|---|---|---|---|
| M4 | N7a, N13a to N13i, N13n, N13o, N13p, N13q, N13s, N13t, N1l | all, N7a done (N13n now also keys `Str` literals, normal form version 6; `src/reify/match.zig`: the canonical flat tree, its check and its tree bound). The ledger keeps open entries filed against N13d: they wait for a tested value read as its literal inside an arm, not for N7a | flat matches, known values, `Bool`, `And` and `Or` rules, integer comparisons. The rule-derivation tool ran its three gate iterations over these rules, and the gate passed on 2026-09-27 (`roc-reify-rule-derivation.md` 6.3). From then on, a tier F rule enters the table through the tool's `--admit`, and a hand-written tier F row states its reason |
| M5 | N7b, N7c, N7d, N13j, N13k, N13m, N13r, N15a, N15b | all, done (normal form version 7), with three limits. N7b hoists a test only within one root and only for value switches (see its row in 3.4). N13r does not join an outer arm that two inner arms select, because an exiting switch carries at most one join. N15c's `Str` literal-last half is built; its parameter half waits for M11. N13j and N13k fold integers, floats with the bits of Roc's own float code and its one `NaN`, `Bool`, and `Str` equality and concatenation, and fold two literals that are adjacent in a chain. N15a also flattens `Str.concat` and `List.concat` chains and drops `""` and `[]`. `Builder.decidedNot` is N13d over `Bool.not`, and `Builder.decidedRefs` is N13d over a `Bool` that ends a region. Two L4 seeds beyond the committed one (0x1111 with 1500 cases) still find one pair of prints that do not meet: a field read that one print places before a switch and the other in two sibling arms, which looks like a placement question (N5, M2) and was not checked against the code before M5 | full decision trees over switch trees; nested `if`s meeting `and`/`or` in every arm order; case-of-case; folding with pinned float bits; `Elem`; chains |
| M7 | N14a, N14b | all, done (normal form version 9), with limits: (1) a value splits only when every use of it is a `Field` or `Index` of it, so a record that is also passed to a `Call`, a `Prim`, a `Closure` or a construction, returned, switched on or given to a loop stays whole, even when the callee would take it apart; (2) a tag union, a record with a member a value may lack, and a record or tuple with no component never split, and neither does a nominal that wraps a record; (3) a loop slot whose `Continue` gives a value that is neither the slot nor a construction, such as a switch output or a call, stays whole, so a record `var` that only some branches update does not meet its fields until a rule moves a read into the arms of the switch (the plan has none); (4) the outputs of a general `Loop` are not split; (5) a `Closure` names the row it always named, and only a `Call` is split, so a row both called and made into a closure keeps its parameters for the closure; (6) the slots of a loop keep their order, with the components of a split slot in the order of the type (names sorted), so a record `var` meets one `var` per field when the fields are named in the order of the `var`s | scalar replacement: `f(a, b)` meets `f({ a, b })` and `f((a, b))` for a private helper; a record or tuple `var` meets one `var` per field; a field that nothing changes is no slot; a lambda that captures a whole record meets a helper that takes the field |
| M8 | V5a | none | stable identities: `inline_digest` |
| M9 | V3 | none | `outline`, with K measured on the examples |
| M10 | N16a to N16f | none | layer L, opt-in |
| M11 | N15c's parameter half, N13u, N8k, and the interval conditions of the rule-derivation tool (`roc-reify-rule-derivation.md` phase D4) | N15c's literal half, with N13n (3.7) | literal intervals: `while $i <= n` with a bounded `n` meets `a..=n`; `a + 1` meets `1 + a`; tier F rows with interval conditions enter through `--admit`. Most rows it adds are conditional, which step 1 checks on the built peak (`roc-reify-rule-derivation.md` 3.1) |
| M12 | N11n, N11o | none | facts across loop turns: a `$done` flag loop meets its `break` form, and a derived counter meets `i + j0` |
| M17 | N17a to N17g | none | known lists (normal-form 3.17): a list of known length loses its list builtins; a loop over it unrolls up to B elements; `map2` then `sum` over literal lists meets the written sum in `inline`; a lookup in a known list is a literal switch, which a translator without arrays accepts |

M8 was one milestone. The core took I9, V2 and V6 from it as M8a, and M8
keeps what the safety document does not need.

Each extension changes normal forms, so after a first release each one ships
as a language-version change.

---

## 5. Testing

### 5.1 Layers

| Layer | Runs | Catches | Built in |
|---|---|---|---|
| L1 rule tests | `zig build test`, over graphs built with the builder, no checker | a rule that fires wrongly, or fails to fire | M0, extended every milestone |
| L2 verifier | after every pass, in debug builds and in all tests | a pass that breaks an invariant | M0 |
| L3 source pairs | `zig build test`, through the checker | a refactor in R whose two sides differ | M1 |
| L4 R fuzzer | AFL target and a fixed seed set in `minici` | combinations of refactors nobody wrote a pair for | M1 |
| L5 soundness differential | AFL target and a fixed seed set in `minici` | a normal form that means something else than its body | M1 |
| L6 confluence | `zig build test`, bounded exhaustive | two rules that do not join | M4 |
| L7 end-to-end | CLI suite | translator output that changed under a refactor | M1 |
| perf | `zig build test` for counters; benchmarks recorded | a pass whose work grows faster than its bound | M0 |

### 5.2 L2: the verifier

The verifier runs after every pass. A test never passes with a broken invariant
hidden behind an equal dump.

| Invariant | Checked from |
|---|---|
| every ref points to a param, a slot, or an earlier node in a dominating region | M0 |
| every node's type agrees with its op and argument types | M0 |
| `speculatable` agrees with the op, the speculatable list, for a `Call` with the callee row's body, and for `ForRange` and `ForList` with their body | M0 |
| every path of a loop body ends in `Continue`, `Break`, `Return` or a `Jump`; `Continue` and `Break` appear only in loop bodies; a `Jump` names a join of the enclosing exiting switch, and only a later join from a join | M0 |
| no names and no regions in the IR; provenance has an entry for every node | M1 |
| no two identical nodes where one dominates the other | M1 |
| every `Call` names a finalized row, no two finalized rows have equal digests, and every row's recursive flag agrees with the call graph recomputed from its finalized body | M3 |
| no `Apply` in a finalized row | M3 |
| before N5b, every node sits in its latest region at the source's loop depth | M2 |
| no switch output that every arm gives as one value, and none that nothing reads | M4 |
| no node that every arm of a switch computes from values outside it | M2 |
| the content digest of every region is unchanged by N5b | M2 |
| no node comes from the body of a function in the site's cut | M1 |
| raw rows: no `Let`, no binder, no syntax variant | M1 |
| normal rows: numbering is a fixpoint, so renumbering is the identity | M2 |
| every row has a digest, and the digest recomputes to itself | M3 |
| no decision tree larger than the multiplier bound | M4 |
| no smart-constructor rule applies anywhere in a normal row, and every pass marked "fixpoint" in 3.4 is the identity on it | M4 |
| no loop of a finished row matches a rule of `loops.zig`, the raising rules of N11l included (`loops.noneRewritable`, run with the checks of the driver) | M6, done |
| no join that exactly one jump reaches, no join without nodes of its own, no exiting switch that reaches no terminator, no exiting switch whose paths end in one kind of terminator, and no `Return` in tail position | M1 |
| a switch with an arm that ends in a terminator or a jump ends its region in `Branch`, and every node the source wrote after it sits in one of its joins; every arm of a value switch ends in `Value` with one value per output | M1 |
| every simplify round decreased the measure of normal-form 3.0 | M4 |
| no node that is not speculatable sits in a region evaluated in more cases than the region the walk built it in | M2 |

"No rule applies" is the strongest invariant: it states that the output is in
normal form without trusting the fixpoint's stop condition.

### 5.3 L1: rule tests

Each rule gets the same four tests, in `src/reify/test/<file>_test.zig`, written
as builder calls and asserted as dump text:

| Test | Asserts |
|---|---|
| fires | the redex becomes the stated result |
| condition | each side condition, removed one at a time, stops the rule: integer arithmetic invariant in a loop is not hoisted out of it; `1 // 0` does not fold; a float `is_eq` does not become a literal switch; a float `!(a < b)` does not flip; a loop with a float counter is not raised, and one stepped by `plus(1, s)` is; case-of-case does not fire when one inner arm's tag is unknown; `Apply` of a switch is not moved into the arms when one arm's closure is unknown; a nested `if` whose `else` arms differ does not become an `And`; work in all but one arm is not merged; a `while $i < n` stepping by 2 is not raised |
| context | the rule fires where the redex appears only after another rule or after inlining |
| knockout | with the rule disabled, the fires test fails |

The knockout test is how every test here validates that it catches the bad
behavior: the builder has a per-rule disable switch, compiled only into test
builds, and a test that still passes with its rule disabled is a test that
checks nothing. A meta-test iterates every rule, disables it, and asserts that
at least one L1 test and one L3 pair fail.

### 5.4 L3: source pairs

For every row of R (normal-form section 7), a pair of Roc bodies that differ by
exactly that refactor, compiled through the checker, with equal normal forms
asserted in the view the row names: `graph` for tier A, `inline` for tier B.
They extend `src/compile/test/code_reifier_test.zig`, and the calls into other
modules and builtins that it cannot reach (`roc-reify-design.md`, section "How
each box was checked") go in `src/eval/test/eval_staging_tests.zig`.

Every row of section 7.1, the edits outside R, gets a pair too, asserting
unequal normal forms. These pin the boundary from the other side: a rule that
starts hoisting integer arithmetic out of a loop fails here.

### 5.5 L4: the R fuzzer

A new fuzz target, `fuzz-reify`, beside the five in `build.zig:7052-7058`. It
follows the rule in `AGENTS.md` and `test/fuzzing/README.md`: small typed
constructs composed at random, names from the symbol generator.

1. `TypedCodeGenerator.zig` generates a module with a function body, in its
   own typed representation, before printing.
2. A refactor engine applies a random sequence of refactors from R to that
   representation. Each R row is one typed transform: rename a binder, swap two
   independent statements, extract a subexpression into a helper, inline one,
   turn `if` into `match`, turn a `for` into a `while`, split a record
   parameter, and so on. Working on the typed representation makes each
   transform meaning-preserving by construction, and it cannot produce a
   program that fails to check.
3. Both programs are printed, checked and reified. The target asserts equal
   normal forms, and equal digests.
4. On a failure, the harness shrinks the refactor sequence to the shortest one
   that still differs, and prints both dumps.

The transform list grows with the milestones: a milestone that absorbs an R
row adds its transform. A transform whose row is not absorbed yet is disabled
in the list, so the fuzzer's scope is the current R and nothing else.

### 5.6 L5: the soundness differential

`src/eval/test/lambda_mono_differential_runner.zig` is the precedent: two
executions that share no lowering code must agree. Here:

| Execution | Runs |
|---|---|
| reference | the Roc interpreter on the original function |
| subject | `src/reify/eval.zig` on the normal form, in each view |

Inputs are generated from the root parameter types. The check is C2, read
directly:

| Reference | Subject must |
|---|---|
| returns a value | return an equal value within the step budget: a crash or a timeout here is speculation, and a different value is a wrong rewrite |
| crashes, or exceeds the step budget | nothing: any outcome is allowed |

The first row is what catches a pass that hoists a division out of the branch
that guarded it.

The subject runs after every pass, not only on the final form, so a failure
names the first pass whose output disagrees. The same harness checks "views
agree" (all three views against the reference) and each law of layer L, with
its two sides as the two functions.

`eval.zig` shares no code with the normalizer beyond the IR definition and the
builtin table's numeric functions, which are the interpreter's own. Its
builtin semantics are the interpreter's, called through the same entry points,
so the differential tests normalization, not two implementations of `plus`.

### 5.7 L6: confluence

Termination is proved by the measure. Confluence is tested:

| Test | How |
|---|---|
| critical pairs | for every pair of rules in the rule table (I13) whose left sides overlap, which the table enumerates from the root ops and argument patterns, a generated graph containing the overlap, normalized with each rule forced first; both orders must give the same normal form. A rule added to the table adds its pairs to the test without anyone listing them. Implemented as step 1 of `roc-reify-rule-derivation.md`. A pair of conditional rows is checked on a peak the builder builds, at each literal the rows name where a condition needs one, and only where both rows rewrite that peak (3.1 there) |
| sharing | the critical pairs and the bounded exhaustive graphs again with shared nodes, a node read by both overlapping redexes, because joinable critical pairs imply confluence over terms and need extra conditions over graphs (Plump, 1999) |
| oracle | the exploration of `roc-reify-rule-derivation.md` step 2 at the milestone's signature and size bound, in a scheduled CI job: small irreducible terms grouped by their values in the reference evaluator; two terms with equal values that step 3 proves equal must get one normal form. It shares no rule code with the normalizer, so it finds a missing rule, not only two rules that fail to join |
| bounded exhaustive | every graph up to a small size over a small signature (a `Bool` param, an integer param, a two-tag union, one record type, the rule-relevant builtins), normalized under several random rule orders; all results must be equal. This is the small-scope hypothesis: most confluence bugs show up in small terms |
| order independence | the builder has a test hook that shuffles the construction order of independent nodes; the normal form must not change. This tests N4 and N9 directly, beneath the source level |
| idempotence | normalizing an emitted normal form again gives it back unchanged |

A failing critical pair is fixed by adding the rule that joins it, and the
new rule arrives with its own L1 tests.

### 5.8 Performance

Wall-clock time is noisy in CI, so the gate counts work, and the benchmarks
report time.

| Test | Gates on |
|---|---|
| work counters: hash lookups, nodes built, simplify rounds, bisimulation refinements | generated bodies of size n, 2n, 4n, 8n; each counter must grow within its bound of 2.2 |
| round bound | no component takes more simplify rounds than the bound of 2.3, and every round lowers the measure; the round distribution is reported, and a milestone that raises its maximum on the benchmarks stops for review |
| callers once | every caller outside a component is simplified exactly once, counted per row |

| decision tree lint | the multiplier bound per match |
| exits | a loop body of k sequential statements, each with two continuing arms and one `break`, normalizes to O(k) nodes |
| no-site module | a module without sites performs zero reify work: the counters stay at zero |
| cache hit | a second build performs zero reify work |
| editor latency | reported, not gated: the time from an edit to diagnostics under `roc check` on the GLSL and SQL examples and on a module with 100 sites |

The benchmarks run the GLSL and SQL examples and a generated body of 10,000
nodes, and record walk time, normalization time, emitted `ConstStore` nodes and
translator time, with the share spent in the utilities of 1.8, before M1 and after each milestone. A milestone that makes
normalization more expensive than the walk, on any benchmark, stops for a
design review before it merges.

### 5.9 L7: end to end

| Test | Asserts |
|---|---|
| the examples | `examples/reifying/glsl` and `examples/reifying/sql` produce their `expected_output` files |
| refactored examples | a copy of each example with a stack of R refactors applied by hand (renames, reordered bindings, an extracted helper, a `while` for a `for`) produces byte-identical output. This is the claim of the document, shown on the programs a reader will look at first |
| refusals | snapshot tests of `refuse_at` diagnostics, pointing at every source region of a merged node, with the call path |
| cache | the artifact round-trips; `test/serialization_size_check.zig:41-42` moves, and `CACHE_VERSION` (`src/compile/cache_config.zig:263`) is bumped once per milestone that changes the stored form |
| builtin table | every entry in `prims.zig` names a public builtin listed by `test/fuzzing/BuiltinSurface.zig`; a builtin on the speculatable list never crashes or exceeds the step budget on the typecheck fuzzer's generated inputs |
| float folding | a fixed set of float expressions, `sin`, `pow` and `sqrt` among them, folds to pinned bits on every CI platform |
| version | the fingerprint of the rule set, the speculatable list and the builtin table equals the one recorded with `Code.version` |
| translator libraries | the GLSL example, with a refactor applied inside `Glsl.Vec3.scale`, produces byte-identical output |
| sites | two sites with one normal form give equal `Code` values; a refusal at each names its own site |

### 5.10 Tests per milestone

The core milestones come first, in their order of 4.1, and then the extensions of 4.2.

| Milestone | L1 | L2 | L3 | L4 transforms | L5 | L6 | L7 |
|---|---|---|---|---|---|---|---|
| M0 | builder, hash-consing across deep regions, fact stack, the rule table's dispatch and knockout, driver with stub passes (callee components finalized before callers; a row created on demand is finalized before its caller continues) | base invariants, terminators and jumps | none | none | `eval.zig` against the interpreter on hand-built graphs | none | none |
| M1 | every N1 rule, `And`/`Or` construction; SSA; switches with several outputs; loop lowerings to `ForRange`, `ForList` and `Loop`; joins: T2 to T6 each, the T2 and T3 pair (`if c { continue(a) }; continue(b)` reaches `Continue(Switch c { a, b })` in either order), and `x // y` after a partially exiting `if` staying in the join; N8h; `to_tree`, `uses`, `children`, `inputs` (5.11); literal bits | raw invariants; join invariants; no foreign body walked | spelling, desugaring, `var`, `for`/`while` lowering, `a and b` versus `if a b else Bool.False`, `return x` last versus `x`, `continue` in each branch versus one after the `if`, `if c { break }; rest` versus `rest` in the `else`, `?` versus the `match` it means | rename, reformat, operator versus method, pipe, destructure, record update, default fields, `expect`, a refactor inside a foreign function | on | idempotence | examples ported; translator libraries; sites; version |
| M2 | placement under C2 with Click's precedence (a speculatable node used in a branch inside a loop lands just outside the loop, after the branch's facts simplified it), the late schedule (a `match x` written before an outer `match x` and read in one arm is decided there), N5c, dead nodes, numbering; value numbering under a shuffled build order | numbering fixpoint; no speculation; no every-arm node left; digests unchanged by placement | reorder, bind twice, bind once before a `match` versus in every arm, move a failing binding into a branch, drop a dead failing binding; integer work across a loop boundary stays outside R | reorder independent, bind twice, drop unused, sink into a branch | on, with the C2 table | order independence | refactored examples: renames and reorders |
| M3 | SCC and its recheck (a recursive call N13 deletes leaves a row that is not recursive), digests confirmed structurally (a forced digest collision does not merge), finalize before callers (two calls to two identical helpers merge; a dropped parameter leaves no dead argument), `Apply` rules and the refusal of an unresolved one, parameter order, single-use inlining, template memoization counters | digests; finalized rows | helper rename, move, generic, parameter order, single-use extraction | extract and inline helper, move helper, reorder parameters | on | order independence over rows | refactored examples: helper extraction |
| M8a | the `inline` view with its simplify rerun; `Lambda` regions in `inline`; `refuse_at` reaching every source region of its node, including a node N5a merged from two sources | views verified | tier B rows in `inline` | all, in `inline` | views agree | none | refusal snapshots, site types |
| M13 | N8h with a declared cut: a function in it stays a primitive, in any package; N8l: a function of another package outside it is walked; I14: a cut entry that is not a function reference is a compile error | no node from the body of a function in the cut | a refactor inside a dependency's function outside the cut that keeps its normal form, against the same refactor inside the package | a refactor inside a foreign function outside the cut | on | none | the GLSL example with its declared cut; a two-package example whose helper, outside the cut, is inlined |
| M14 | none | none | every row of 5.12 | none | on | none | none |
| M6 | N12, each slot and exit rule, N11k, each raising rule of N11l and each of its conditions (a step of 2, a bound read from a slot, a `Break` that is not the other slots: each stays a general `Loop`), each `iteration` result; a `ForList` over a `//` in its body stays not speculatable | loop invariants; no raisable `Loop` | the three `sum_to` bodies as one `ForRange`, counter `while` versus range `for`, index loop versus list `for`, `for x in xs` versus `for x in xs.iter()`; for each, equal `iteration` results; `xs.iter().keep_if(p)`, `while $i <= n`, a `$done` flag loop and a derived second counter stay general loops or unequal; `continue` in each branch versus one after the `if`; `if c { break }; rest` versus `rest` in the `else`; `while Bool.True` with a `break` versus `while i < n` | loop form, tail recursion, `.iter()` added or dropped, `continue` moved into or out of branches, `if c { break }` with or without `else` | on | loop-rule pairs | refactored examples: loop form; the SQL example reads `iteration` for its scans |
| M15 | each admitted row: it fires, it joins, and its knockout stops it (`src/reify/derive/derived_test.zig`) | none | the holdout pairs (`roc-reify-rule-derivation.md` 6.3) | none | on | step 1 on the table: every unjoined critical pair equal modulo the ledger | none |
| M16 | as M15 | none | as M15 | none | on | as M15 | none |
| M4 | each N13 rule, N1l, N7a; the N13q and N13i critical pair | no rule applies; tree bound; measure | `if` versus `match`, known tags, dominating tests, negation, `and`/`or` versus their `if`, `if a Bool.False else b` versus `!a and b`, `a >= b` versus `!(a < b)` over integers, and unequal over floats | `if`/`match`, negate and swap, flip comparison, `and` to `if` and back | on | critical pairs, bounded exhaustive | refusal snapshots of its rules |
| M5 | N7b over switch trees built after inlining, N7c, N7d with its mirrors and their critical pairs with N13i and N13q, N13r, folding, `Elem`, chains, `And`/`Or` flattening | as M4 | arm order, `if` chains versus literal `match`, nested `if`s versus `and`/`or`, constant naming, chain grouping, `and` grouping, De Morgan in a value and in a condition | reorder arms, regroup concat, regroup `and`, nest and unnest `if` | on | as M4, larger signature, with `And`/`Or` | float folding bits |
| M7 | N14 | as M4 | `f(a, b)` versus `f({ a, b })` | split and merge aggregates | on | as M4 | none |
| M8 | `inline_digest` (5.11) | none | none | `inline_digest` equal under every transform, in `inline` | none | none | none |
| M9 | cones, shapes, selection | outline invariants | all rows in `outline` | all, in `outline` | views agree | determinism of selection | none |
| M10 | each law | as M4 | loop versus `map`, `keep_if`, `fold`; fusion; `len() > 0` versus `!is_empty()` | loop to builtin | laws | law pairs | none |
| M11 | interval arithmetic per op at every width, with the type's bounds; each source of 3.13; N15c on each operand kind, and a helper with reordered parameters still meeting itself; a checked `plus` proved to fit hoisted out of a loop, and one not proved staying | intervals only narrow: every interval contains every value the reference evaluator computes, on the L5 inputs | `while $i <= n` with `n` bounded versus `a..=n`, and unbounded staying apart; `a + 1` versus `1 + a` | swap a literal operand, swap root parameters | on, with interval facts in the C2 table | the pairs of conditional rows, joined | none |
| M12 | N11n on each edge kind, and an edge no test decides staying a general `Loop`; N11o at `a = 0`, at a proved difference, and at a step of 2 and an exit reading `j`, which stay | loop invariants | the M6 rows for a `$done` flag loop and a derived second counter, now equal | flag to `break`, counter to sum | on | loop-rule pairs | none |
| M17 | each N17 step, with its knockout; B at its bound and one above it; `keep_if` with one predicate result not a literal staying a builtin; a loop over a known list with a `Break` staying a `ForList` | no builtin of N17 left over a known list | the three meeting pairs of normal-form 3.17, and its apart rows staying apart | a literal list's builtin to its result, a loop over a literal list to its statements | on | pairs of N17 with N13 and N15a | none |

### 5.11 Built-in utilities

The Roc utilities run in the compile-time interpreter over emitted values. The
tests feed them the values of the L4 and L5 fuzzers' graphs and check
properties in Zig on what they return. The properties are stated, not
reimplemented, so no second implementation of a utility exists to drift.

| Utility | Property | Catches |
|---|---|---|
| `to_tree` | meaning: the reference evaluator gives the same result on the tree as on the graph, on the L5 inputs | a wrong substitution |
| `to_tree` | no duplication: every node that is not a literal or a parameter appears exactly once in the tree | a shared def substituted at each use |
| `to_tree` | no speculation and no repeated work: nothing is substituted into a loop body or lambda, and a node substituted into an arm or operand is one the graph places outside it | a node moved into a loop, or out of a branch |
| `to_tree` | round trip: building the tree back through the builder gives the identical normal form | a tree that loses or reorders structure |
| `to_tree` | canonical: equal graphs give equal trees; the L4 fuzzer compares trees as well as graphs | a dependence on anything but the value |
| `uses`, `children` | agree with the use counts and children the Zig verifier computes over the same graph | an off-by-one in either |
| `inputs` | the root parameter's fields, by name, in the type's order | a field order read from the source |
| `iteration` | the M6 rows of 5.10; it agrees with the node kind on every loop of the L4 graphs | a classification made anywhere but the normalizer |
| `inline_digest` | equal under every R transform and under helper extraction, in `inline`; unequal for nodes whose content differs, on the L4 graphs | a digest keyed by row identity instead of content |

Each property has a knockout test, as in 5.3: a test build of `to_tree` that
substitutes single-use nodes into loop bodies must fail the no-speculation test,
and one that substitutes shared defs must fail the duplication test. The
utilities' time is part of the translator time in the 5.8 benchmarks, and
`to_tree` on the 10,000-node body is gated by the same n, 2n, 4n, 8n counter
growth test as the passes.

### 5.12 The safety matrix

M14 writes one L3 pair for each row, names the row in the test's title, and
fills in the last column. Rows marked "meets" must give one normal form. Rows
marked "apart" must give two, and each is a row of `roc-reify-refactor-safety.md`
5 that R leaves out on purpose.

| Refactor | Safety document | Absorbed by | Milestone | Expected | Test |
|---|---|---|---|---|---|
| rename a local or a parameter | 4.1, 2 | N2 | M1 | meets | |
| reorder independent bindings | 4.1, 2 | N4, N9 | M2 | meets | |
| bind a value once or write it twice | 4.1 | N5a, N5c | M2 | meets | |
| drop a binding nothing reads | 4.1 | N6 | M2 | meets | |
| extract or inline a helper with one use | 4.1, 2 | N8d to N8g, V1 | M3 | meets | |
| extract or inline a helper with many uses, in `inline` | 4.1, 2 | V2 | M8a | meets | |
| destructure or read fields | 4.1 | N1f | M1 | meets | |
| `and`, `or` and the `if` they mean | 4.1 | N1c | M1 | meets | |
| `?`, `??`, early `return` and the `match` they mean | 4.1 | N1d, N11m | M1 | meets | |
| move code, reformat, comment | 4.1, 2 | N10 | M1 | meets | |
| add or remove a type annotation | 4.1 | types from the checker | M1 | meets | |
| reorder unrelated top-level definitions | 4.1 | N8g, N9 | M3 | meets | |
| reorder two calls to one generic function | 2 | N8d, N8g | M3 | meets | |
| a refactor inside a function in the translator's cut | 2, 4.3 | N8h | M1 | meets | |
| a refactor inside a dependency's function outside the cut that keeps its normal form | 4.3 | N8l | M13 | meets | |
| `x * 2` or `x + x`; `(a + b) + c` or `a + (b + c)` | 5 | none | none | apart | |
| `x.len() > 0` or `!x.is_empty()` | 2, 5 | none without layer L | none | apart | |
| a fold or a `for` loop with a `var` | 2 | none without layer L | none | apart | |
| a recursive function or a fold | 5 | none | none | apart | |
| a dependency upgrade whose function outside the cut changes its operations: non-tail recursion, a list of input-dependent length, a builtin the target lacks | 4.3, replaced by 1.9 here | none | M13 | apart; the build stops at the site | |

---

## 6. Risks

| Risk | Mitigation |
|---|---|
| the M1 retarget of an 8,400-line walk is large | the walk's decisions do not change; the tests of `code_reifier_test.zig` and `eval_staging_tests.zig` are ported first and pin its behavior across the retarget |
| a rule set that is not confluent | L6 finds it; the fix is a new rule, which completion always allows because every rule is an equation valid in Roc |
| the simplify fixpoint takes many rounds on some input | the round bound refuses the site deterministically and names the bound; the perf counters report the round distribution on the benchmarks |
| `inline` explodes on a real program | the node bound refuses the site; `Code.Outlined` is the answer for that program |
| the builtin table drifts from `Builtin.roc` | a builtin without an entry is not speculatable, which is sound; a stale entry fails the table test of 5.9, and a wrong speculatable claim fails its fuzz test |
| the language rejects C2 | the strict variant of 1.9 is a bounded change to seven steps; the decision is needed before M2, which builds placement |
| a translator's cut misses a function its target has | the function is walked and its body inlined, which is sound; the translator's refusal names the function, and the fix is one cut entry |
| the cut is per type, so two translators that need different cuts must be two types | the rule is stated in normal-form 12; a finer grain would need the second `Code` parameter that 12 rejects |
| the hand-written `is_eq` on `Code` drifts from the normal form | it is written over the emitted fields with the site key named once, and the sites test of 5.9 compares it with equality of dumps |
| intervals make the rule set depend on a fact the builder computes | an interval is one operation per node over literals and dominating tests, with no widening; L2 checks on the L5 inputs that every interval contains the value, so a wrong interval is found rather than trusted |
| rule derivation at k = 6 and 7 outgrows the tool's time or memory: a run at k = 5 over S2 peaks at 5.4 GB (`roc-reify-rule-derivation.md` 5.2) | M15 runs S1 before S2, and the D3 record keeps each run's time and peak memory beside those at k = 5. Making the tool fit is M15's work, in the tool, which the compiler does not import |
| translator authors lose names while debugging | `roc reify --dump` (I7, normal-form 6) ships in M1, with the first normal form |

---

## Sources

- Matthias Braun, Sebastian Buchwald, Sebastian Hack, Roland Leißa, Christoph Mallon, Andreas Zwinkau, "Simple and Efficient Construction of Static Single Assignment Form", CC 2013 (SSA and simplification during construction)
- Cliff Click, "Global Code Motion / Global Value Numbering", PLDI 1995 (placement: schedule late across branches, early across loops)
- Bowen Alpern, Mark Wegman, Kenneth Zadeck, "Detecting Equality of Variables in Programs", POPL 1988 (optimistic value numbering)
- Robert Tarjan, "Depth-First Search and Linear Graph Algorithms", SIAM Journal on Computing 1(2), 1972 (SCCs)
- Max Willsey et al., "egg: Fast and Extensible Equality Saturation", POPL 2021 (the e-graph alternative, rejected in 1.3)
- Colin Runciman, Matthew Naylor, Fredrik Lindblad, "SmallCheck and Lazy SmallCheck", Haskell Symposium 2008 (bounded exhaustive testing)
- Luke Maurer, Paul Downen, Zena Ariola, Simon Peyton Jones, "Compiling without Continuations", PLDI 2017 (join points)
- Detlef Plump, "Term Graph Rewriting", in Handbook of Graph Grammars and Computing by Graph Transformation, volume 2, 1999 (critical pairs over graphs with sharing)
- Cranelift ISLE, the instruction-selection and rewrite rule language (rules declared as data)

- Donald Knuth, Peter Bendix, "Simple Word Problems in Universal Algebras", 1970 (critical pairs and completion)
