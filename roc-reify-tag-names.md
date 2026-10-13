# Reify: tags by name, and no Widen

Status: implemented. It replaces `Op.Widen` (commit "Normalize reified
functions") with tags that the normal form identifies by name. The line
references below point at the working tree that implements it.

## 1 The problem

Upstream added `row_coerce` (design.md, "Row Coercion Primitive"). The checker
writes it where a value of a tag union is read at a wider union:

```roc
size = |x| if x < 1 Small else Big    # the body closes the row to [Big, Small]

main = match size(n) {                 # this match reads [Big, Huge, Small]
    Big => 2
    Huge => 3
    Small => n
}
```

The value does not change: `Small` stays `Small`. The rebase gave the normal
form an `Op.Widen` node at that point. A translator gets no information from
it, because the `Code` view names tags by text (`Op.Tag(Str)` at
`src/build/roc/Builtin.roc:23945`, `Key.Tag(Str)` at `:23859`).

The node existed because the normal form numbered a tag by its position in its
own union. Each place that read a tag by position was changed to read it by
name:

| Place | Before: a tag is | After: a tag is |
|---|---|---|
| `.tag` node | `payload` = member index | `payload` = `NameId` (`src/reify/builder.zig:895-899`, `src/reify/ir.zig:269`) |
| `.payload` node | member index and field | `NameId` and field (`src/reify/builder.zig:917-923`, `src/reify/ir.zig:271`) |
| tag `switch_` | one arm per member of the scrutinee type, by position | the same, with the arm of a tag found by name (`src/reify/builder.zig:1083-1095`, `src/reify/verify.zig:233-234`) |
| N13a, `Payload(Tag(..))` | compares the two indices | compares the two `NameId`s (`src/reify/builder.zig:1973`) |
| N13d, tag arm of a known tag | `regions[n.payload]` | `regions[memberIndex(type, name)]` (`src/reify/builder.zig:1796-1806`) |
| decided switch | arm index from a dominating fact | the fact holds a `NameId`, and `memberIndex` finds the arm (`src/reify/builder.zig:792-799`, `:1303-1310`) |
| evaluator | `t.index` | `t.name` (`src/reify/eval.zig:233`, `:272`, `:288`) |

`Small` is index 1 in `[Big, Small]` and index 2 in `[Big, Huge, Small]`. So
with positions, a widening renumbered, and `Widen` was that renumbering.
The node had three costs:

1. Translators must handle an op that has no meaning for them.
2. It breaks the refactor promise "extract or inline a non-recursive helper"
   (`roc-reify-refactor-safety.md:118`). Code written inline builds `Small()`
   at the wide union. The same code moved into a helper gives
   `widen(Small())`.
3. No rule reads through it, so it blocks folding.

## 2 The design

A tag is its name. The normal form identifies a tag by the interned name of
its label, `NameId` (`src/reify/types.zig:13-26`, `name()` at `:160`). Tag
unions already keep their members in name order and intern each name
(`src/reify/types.zig:276-299`). `Types.memberIndex` finds a member by name
(`src/reify/types.zig:481-493`).

| Part | Before | After |
|---|---|---|
| `.tag` node `payload` | member index | `NameId` of the tag (`src/reify/builder.zig:895`) |
| `.payload` node | member index, field `k` | `NameId`, field `k` (`src/reify/builder.zig:917`) |
| tag `switch_` | one arm per member of the scrutinee's type, by position | the same. A switch always has one arm per member of its scrutinee's own type, in name order (2.2). |
| builder facts for tag arms | arm index | `NameId` (`src/reify/builder.zig:792`, `:803`) |
| N13a, N13d, decided switch | compare indices | compare `NameId`s (`src/reify/builder.zig:1303`, `:1796`, `:1973`) |
| evaluator tag value | `{ index, payload }` | `{ name, payload }`. A switch finds the arm by name in its scrutinee's type (`src/reify/eval.zig:233`). |
| `verify.zig` edges | exact type | conformance (2.1) |
| digest of a tag or payload node | the raw payload word | the name's text, as `.derived` does (`src/reify/digest.zig:348-349`) |
| `code_emit.zig` | index to name through the type | `nameText(payload)` (`src/check/code_emit.zig:221`, `:228`). Only the keys of a tag switch still use a member position (`:261`, `:281`). |
| `Op.Widen`, `ir.widen`, `Builder.widen` | present | removed |
| walk, `row_coerce` | `widen(at, x)` around a value with a name | `x` (`exprAt`, `src/check/code_reifier.zig:1564`) |

`Bool` does not change. It is its own type kind (`.bool_`,
`src/reify/types.zig:86`), and most of the rule table is about `Bool`.

### 2.1 Conformance

The verifier replaces `child type == expected type` with "the child's type
widens to the expected type" at every edge where a value flows into a slot
(`argFits`, `src/reify/verify.zig:128-131`). `Types.widens` already
implements the reach and the superset rule of design.md
(`src/reify/types.zig:401-455`):

| Edge | Expected type | Checked at |
|---|---|---|
| record field, tuple element, tag payload | the member type of the node's own type | `src/reify/verify.zig:156-185` |
| `Wrap` argument | the nominal's backing | `src/reify/verify.zig:206-209` |
| `Call` argument | the callee row's parameter | `src/reify/verify.zig:215-222` |
| `Apply` argument | the function type's parameter | `src/reify/verify.zig:271-278` |
| region end value, `Return` | the owner's output, or the row's result | `src/reify/verify.zig:294-300`, `:356-368` |
| jump value | the join parameter | `src/reify/verify.zig:445` |
| loop and for argument | the loop parameter | `src/reify/verify.zig:251-270` |

A projection (`Field`, `Index`, `Payload`, `Unwrap`, `Elem`) takes its type
from its argument and stays exact. Outside the reach (list elements, record
fields of a record, function types, a named type with no backing) `widens`
requires identical types, as design.md does.

### 2.2 Switch arms

Inlining puts an argument where a parameter was, so a switch on that
parameter can get a narrower scrutinee. The switch constructor then keeps the
arms of the tags its new scrutinee has, matched by name, and drops the others
(`Builder.tagSwitchOn`, `liveTagArms`, `src/reify/builder.zig:1061-1095`).
A dropped arm is dead: the value cannot hold that tag. With this rule, the
arms of a tag switch are always fixed by the scrutinee's own type, so a switch
needs no keys and two equal switches have equal arms. The scrutinee can never
be wider than the arms, because the checker makes a match exhaustive at the
type it reads, and conformance only makes values narrower. A debug build
checks the arm count in `Builder.make` (`src/reify/builder.zig:1126-1131`)
and in the verifier (`src/reify/verify.zig:233`). `Builder.tagLive`
(`:1077`) tells the walk that an arm for a tag is dead, and `tagTest` uses it
(2.3).

### 2.3 Demanded type

Section 1, point 2 is about types as well as nodes. Without `Widen`, code
written inline builds `Small()` at `[Big, Huge, Small]`, and the inlined helper
builds it at `[Big, Small]`. That is still two descriptions of one function.
The walk already follows one rule: a node whose type the builder chooses is
built at the type its consumer demands (`exprAt`, `src/check/code_reifier.zig:1564`).
The normal form keeps that rule through inlining.

What the walk does (`callExpr`, `src/check/code_reifier.zig:3558`; `callOf`, `:3618`):

- A `Call` node has the type its site reads the result at. That is the
  `row_coerce` type when `exprAt` reaches the call through a `row_coerce`, and
  the checker's own type for the call expression in every other case. The
  checker already gives a call of a helper that constructs its result the
  union its consumer reads, and the row of the helper keeps its own, narrower,
  result. `Builder.callRowAt` builds the node (`src/reify/builder.zig:1039`).
  `Builder.callRow` (`:1032`) is `callRowAt` at the result of the row.
- `verify.zig` accepts a `Call` whose type the result of the row `widens` to.
  Any other call type is reported (`src/reify/verify.zig:215-222`).

What the inline view does (`Demand`, `src/reify/rebuild.zig:116`;
`DemandWalk`, `:145`; `Rebuild.inlined`, `:522`; the retyping of an inlined
node, `:455`). When the call has a type other than the result of
the row, the inlined body is built with its ends at the type of the call. The
walk starts at the end value of the body and goes down:

| Value | Built at the demanded type | Goes on to |
|---|---|---|
| `Tag` | yes, with the same `NameId` | each payload, at the payload type of that member of the demanded union |
| `Wrap` | yes | the argument, at the backing of the demanded nominal |
| output of a value `Switch` | yes | the end value of every arm, at the same type |
| join parameter | yes | the argument of every jump to the join |
| `Call`, `Crash` | yes | nothing |
| any other value (row parameter, projection, loop result, `Apply`) | no, its producer fixes its type | nothing. It conforms by 2.1. |

A value keeps its own type when another reader than these ends reads it, or
when two ends demand two different types of it. The other reader needs the
own type, and the verifier checks every edge. The case is rare: a helper that
reads a value it also returns. In it the two descriptions can still differ in
that node. The demanded type must be a type that the own type of the end
`widens` to. If it is not, the walk stops with a compiler invariant
(`src/reify/rebuild.zig:189`).

Other rules that replace one `Call` by another (N8c forwarding, N8d
specialization, N8i `Apply` of a closure) keep the type of the call they
replace. No other rule replaces a `Call` by the body of its row.

What this does not reach. A value that the helper binds to a local keeps the
type of the local, as it does in inline code (design.md "Local Values Share").
So `x = Ok(..)` followed by `x` at the end of a helper gives the same node
types in the helper and in the inline code.

The walk of `tagTest` (`src/check/code_reifier.zig:2930`) relies on this
rule. A call carries the wider type, so the scrutinee of a match has every tag
the match lists. A pattern tag the scrutinee lacks is a compiler invariant
(`src/check/code_reifier.zig:2951-2955`), not a case that the walk handles.

Known limits:

| Limit | Why it stays |
|---|---|
| A value that another reader also reads, or that two ends demand at two types, keeps its own type and conforms. In that node an inlined helper can still differ from inline code. | The other reader needs the own type. The case is a helper that reads a value it also returns (`src/reify/views.zig:620`). |
| A `Call` inside the helper body is retyped at the call's type, but its row keeps the narrower result of the helper. | A row is built once, at its own types, and is shared by every site that calls it. |

Tests:

| File | Test | Covers |
|---|---|---|
| `src/reify/views.zig:542` | a call read at a wider union inlines to a body whose ends are built at that union | the end types after inlining |
| `src/reify/views.zig:580` | a call read at a wider union demands the payload types of a tag and the backing of a nominal | the payload and nominal steps |
| `src/reify/views.zig:620` | a value another node also reads keeps its own type | the shared value |
| `src/reify/rebuild.zig:654` | inlining a call over a narrower argument drops the arms of the tags the argument cannot hold | switch pruning (2.2) |
| `src/reify/verify.zig:522`, `:559`, `:578` | conformance of a narrower tag, a wider value where a narrower one is expected, and the call type | 2.1 and the call type |
| `src/reify/rows.zig:1140` | the walked digest reads a tag by its name, not by the order a store interned it in | digest by text |
| `src/compile/test/code_reifier_test.zig:1384` | a helper that closes a row, read at a wider union, describes as the same code written inline | the refactor promise |
| `src/compile/test/code_reifier_test.zig:1334`, `:1421`, `:1463` | a `?` body reaches a wider match with no node between; a match keeps the arm of a tag only it lists; a match lists a tag the helper cannot build | conformance and arms through the walk |
| `src/eval/test/eval_staging_tests.zig:1573` | a call result of the union its callee's body closed reaches a wider match by name | staged output without `Widen` |

## 3 Tag ids across module and site boundaries

| Boundary | What crosses | Must the ids be equal? |
|---|---|---|
| modules read in one site | one `Types` store for the whole site (`Walk.startSite`, `src/check/code_reifier.zig:6470-6476`). Every reader interns the label text (`tagUnionTy`, `:4958-4970`; `Types.tagUnionTy`, `src/reify/types.zig:276-299`). | Yes, and they are, because the store interns by text. Roc tags are structural, so `Small` from module A and `Small` from module B are the same tag. Equal text is the language's rule, not an approximation. |
| two sites, P1 memo | `walkedDigest` and the provenance digest (`src/check/code_reifier.zig:6532-6533`) | No. Digests hash names by text (`src/reify/digest.zig:139`, `:163`), and tag nodes do too (`:348-349`). |
| the stored `Code` value, the cache | the `ConstStore` graph, where a tag is a `Str` | No id is stored. |
| `CodeProvenanceTable` | sites, sources, rows, node spans (`src/check/checked_artifact.zig:34033-34044`) | No tag ids. |
| packages | the same as modules | Tags have no package. A nominal is named with its package, and `widens` requires equal nominal names before it steps into the backing. |

A `NameId` never leaves one site's `Types` store, so it does not have to be
stable between modules, processes, or cache entries.

### 3.1 Why interned ids and not a hash of the name

| | Interned `NameId` | Hash of the text |
|---|---|---|
| two names, one id | never | possible. A switch then takes the wrong arm with no error. AGENTS.md does not allow a stage that is right only "almost always". |
| equal across modules | yes, one store per site | yes |
| stable across processes | not needed (section 3) | yes, but nothing reads it |
| cost | a lookup in the store | none |

The name is hashed only where a hash is already the contract: the digest.

## 4 Analysis

### 4.1 What the design gets right

| Claim | Why |
|---|---|
| a widening is the identity in the normal form | a value carries its name, and its name does not depend on the union |
| translators see one meaning | the `Code` view was already by name, so no translator changes, and `Widen` leaves the op list |
| the refactor promise holds | conformance and the demanded type (2.3) make inline code and an inlined helper give the same nodes and the same types, except in the known limits of 2.3 |
| the rules gain | N13a and N13d now fire through what was a `Widen` |
| no new compiler data | names, unions in name order, and `widens` exist now |

### 4.2 What was not good enough as it stood

Each gap is resolved. The last column says where.

| Gap | Effect if left | Needed | Resolved at |
|---|---|---|---|
| digest hashed tag payload words raw | interning order depends on walk order, so two equal sites digest differently | hash tag and payload names by text (section 2) | `src/reify/digest.zig:348-349`. Test: `src/reify/rows.zig:1140`. |
| the demanded-type rule (2.3) is new | without it, an extracted helper changes node types, a smaller version of the `Widen` problem | the inline view rebuilds the ends at the demanded type, with a test that compares inline code and an inlined helper | `src/reify/rebuild.zig:116-265` and `:522`. Test: `src/compile/test/code_reifier_test.zig:1384`. Limits: 2.3. |
| switch pruning (2.2) is new | a switch with arms for tags its scrutinee cannot hold fails `verify` after inlining | the switch constructor maps arms by name | `src/reify/builder.zig:1061-1095`. Test: `src/reify/rebuild.zig:654`. |
| typed translators | a C or GLSL translator with one struct per union sees a child whose type is narrower than its slot, and must convert there | document conformance in `Code` | the paragraph in `src/build/roc/Builtin.roc:23930-23936`. `Code.Ty.widens` was not added: the paragraph is enough for the translators that exist, and the helper can follow when one needs it. |
| the derivation tool | `src/reify/derive/cp.zig` and `sig.zig` read tag positions through `armCount` | update them | `src/reify/derive/sig.zig:22-37` (the tool interns `A` and `B` first, so a tag name is its index), `:330-331`, `src/reify/derive/term.zig:667-702` (`readBack` turns a name into a term position), `src/reify/derive/cp.zig:278`, `:309`, `:586`, `:617-620`. The rule table and the builtin table did not change, so the fingerprint did not change either. The version stays 3. |
| `place.zig` merge key | none: it compares nodes within one store, where equal names have equal ids | nothing | `src/reify/place.zig:433` is unchanged |

The normal-form version stays 3 (`src/reify/mod.zig:33`). The version covers
the emitted `Code` view, the rules, the builtin table and the ops. The emitted
view is the one of version 3: a tag was always a `Str` there. The rules and
the builtin table did not change. The ops are those of version 3, because
`Widen` was the only op added after it, and this change removes it. So the `recorded`
list ends at version 3 again, and `CACHE_VERSION` stays 146.

### 4.3 Cost

`git diff --stat` of the working tree: 55 files, 1219 insertions, 339 deletions.

| Area | Files |
|---|---|
| IR and builder | `ir.zig`, `builder.zig`, `rebuild.zig` |
| meaning and checks | `eval.zig`, `verify.zig`, `types.zig`, `equal.zig` |
| canonical form | `digest.zig`, `views.zig` (2.3), `number.zig`, `rows.zig`, `polarity.zig`, `dump.zig`, `mod.zig` (version back to 3) |
| derivation | `derive/cp.zig`, `derive/sig.zig`, `derive/term.zig`, `derive/classify.zig`, `derive/enumerate.zig`, `derive/fingerprint.zig`, `derive/loop.zig`, `derive/prove.zig`, `derive/smt.zig`, `derive/derived_test.zig` |
| compiler | `check/code_reifier.zig` (remove `widen`, call type, `tagTest`), `check/code_emit.zig` |
| Roc and tests | `Builtin.roc` (remove `Widen`, add the conformance paragraph), 3 examples, 22 CLI test apps, `parallel_cli_runner.zig`, `eval_staging_tests.zig`, `code_reifier_test.zig` |

`rules/table.zig` and the rule ledger did not change.

### 4.4 Verdict

The design is sound. Tag identity by name is what Roc's structural tags
mean, and the cross-module question has a clear answer: ids only need to be
equal inside one site, and they are. The three new rules (text digests for
tags, switch arms by name, and the demanded type when inlining) are part of
the change, and they are implemented and tested. Without them, removing
`Widen` would move the problem into node types and digests.

The refactor promise holds for the cases the demanded type reaches: tags,
nominals, value switches, join parameters, nested calls and `crash`. It does
not hold in two rare cases (2.3, known limits): a value that a helper both
returns and reads elsewhere, and the row of a call inside a helper body, which
keeps the helper's narrower result. In both, the `Code` value is still correct
and still verifies, because the node conforms. Only its node types can differ
from the inline form.
