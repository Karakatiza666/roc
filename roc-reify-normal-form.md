# Reification through a normal form

A translator never reads the syntax of a reified body. It reads a normal form:
a graph of definitions ("defs") whose shape depends only on what the body
computes. Every refactor in a published list R produces the identical normal
form, so the translator produces identical output. Function calls stay calls
to definitions ("rows") where the source shares a helper. Two further views
exist for translators that must not see the author's helper boundaries:
`inline` removes every non-recursive row, and `outline` replaces them with
rows the compiler chooses from the computation alone.

This document designs the normal form that `roc-reify-refactor-safety.md`
section 4 calls "observe a quotient". It edits no other document.

| Question | Answer | Section |
|---|---|---|
| What does a translator see? | rows of defs in single-assignment form, positional binders, canonical order, no names, no regions | 2 |
| Which refactors leave that unchanged? | the table in section 7, tested by a fuzzer | 7, 9 |
| What about the order of calls? | source order is erased and data order is kept. A reified body promises Roc's result wherever Roc does not crash, and never evaluates what Roc would not (C2), so order matters only for evaluation that could speculate | 1.1, 4 |
| What about functions from the translator's own library? | the translator declares a cut: the functions it reads as primitives, named by their qualified names. The walk reads every other function's body, in any package | 3.8 |
| Are loops, records and tags normalized too? | yes: a loop over a range, a loop over a list, and one general loop, each reached however the loop was written; tail recursion as a loop; construction followed by a read cancels, record updates and defaults are expanded, known tests are decided, and aggregates are split into scalars | 3.11-3.16 |
| Can calls stay as defs? | yes. Shared helper boundaries are the one structure the `graph` view keeps. `inline` removes them, and `outline` recomputes them canonically | 5 |
| How do errors reach the right line? | a provenance table the translator cannot read maps each node back to its source regions | 6 |
| Does this answer the creator's remark? | point by point in section 8 | 8 |

---

## 1. The requirement

The remark:

> if we did incorporate it, it would mean there would be no such thing as a
> safe refactor in the language anymore; any change to any AST node, even just
> reordering two unrelated constants, could break the entire program

The requirement it sets is a property of the feature:

> For every edit in a published set R, the value a translator receives is
> identical before and after the edit.

"Identical" is equality of values, and it is testable. It does not ask the
translator to be correct, complete or careful. A translator that refuses half
of Roc still refuses the same nodes before and after an edit in R, and emits
the same bytes, because its input did not change.

Two tiers of safety follow from the three views of section 5:

| Tier | Meaning | Holds for |
|---|---|---|
| A, identical | the normal form is equal, so every translator's output is equal | every refactor in R, in every view |
| B, equivalent | the normal form differs only in which computations sit behind a call to a non-recursive row | extracting or inlining a helper that is called from two or more places, in the `graph` view only |

Tier B is where keeping the author's calls as defs costs anything. Section 5
argues that the cost is small and optional.

### 1.1 What Roc itself treats as meaning, and what a reified body promises

Roc is strict, and its compiler preserves strict evaluation order: "a pure call
can diverge", and knowing an expression has no effect "does not prove that
evaluating it early or not at all preserves strict source evaluation behavior"
(`design.md:6128-6141`). So in Roc, source order is observable through exactly
two things:

| Observation | Example |
|---|---|
| which of two independent failures happens first | `a = x // 0` then `b = crash "B"`: the message depends on the order |
| whether a computation nothing reads still runs | `_ = loop_forever(n)` never returns, whatever follows it |

Both observations are about crashing or diverging. Neither is one a
translator's target can reproduce. A crash in Roc is not control flow: nothing
in Roc can catch or inspect it, which is why the language has no syntax for
it. It means "this is a bug" and ends the program. A GPU wraps integer
overflow and has no crash, and a database raises its own errors in the order
its plan hits them. Tracking exactly when Roc would crash buys precision no
such target can deliver, and it costs every step a condition: nodes that can
fail keep their region, dead ones become obligations, and every builtin needs
a flag.

One property does matter to every target: a translation must not fail where
Roc would not. `if y != 0 then x // y else 0` must not evaluate the division
when `y` is zero, or the target crashes, or on a GPU reaches undefined
behavior, where Roc was fine. So the normal form promises exactly this:

> C2. On every input where the body neither crashes nor diverges, the normal
> form computes the body's result. The normal form never evaluates a
> computation that is not speculatable on an input where the body would not
> evaluate it.

The first sentence lets the normal form reorder, sink and drop work freely.
The second forbids speculation, which is the one move that can make a target
fail where Roc did not. A speculatable computation can neither crash nor
diverge, so evaluating it where the body would not is allowed, and N5 uses
exactly that to hoist it out of loops. C2 is a language decision for reified bodies only; it
changes nothing about how Roc runs.

Speculation needs one classification. A node is speculatable when evaluating
it can neither crash nor diverge on any input:

| Speculatable | Not speculatable |
|---|---|
| a literal; a record, tuple, list, tag or closure built from values; `Wrap`, `Unwrap`, `Field`, `Index`, `OptField` | `Payload` and `Elem`, which are defined only under the test that dominates them |
| float arithmetic and comparisons; integer comparisons; `Bool` operations; `_wrap` arithmetic; bitwise `and`, `or`, `xor`; the builtins on the speculatable list | integer `plus`, `minus`, `times`, `//`, `%`, `negate`, `abs`, which are checked (`design.md:13576-13581`); shifts, until their range is specified; `crash`; any builtin not on the list |
| a `Call` of a non-recursive row whose body is speculatable | a call to a recursive row; a primitive from another package (3.8) |
| a `ForRange` or `ForList` (3.11) whose body is speculatable: it runs a bounded number of turns and none of them can fail | a general `Loop` |

A rule that drops or repeats an operand under a speculatable condition reads
the whole cone of the operand: the node, every node it reads, and every node
the regions it owns read. The flag of one node covers only that node, and
`Field` of a loop output is flagged speculatable although the loop it reads is
not (`src/reify/builder.zig:3080`, `coneSpeculatable`). Rule T1.11 (`x - x`
is `0`), `x * 0`, and the rules over `speculatable_rest` use it, so a loop
that can crash on checked-integer overflow is never lost (C2).

A checked integer `plus`, `minus` or `times` whose operands' intervals (N13u)
prove that the result fits its type cannot crash in the regions those facts
hold in, so it is speculatable there, and N5b hoists it no further out than
those regions. The builder records the proof with the innermost region whose
fact it read (`src/reify/ir.zig`, `NodeRange`; `Store.fitFloor`). Placement
reads that region as one the node reads, for the node and for a node whose
regions hold it (`src/reify/place.zig`, `readRegions`). Every other step that
moves a node out of a region treats a proved node as not speculatable outside
its facts: N13w (`match.speculatableWithin`), the invariant outputs of N11j
(`loops.zig`, `invariant`), the rows of layer L (`laws.zig`, `settle`) and the
holes of V3b (`views.zig`, `movable`). A proof that reads no fact, such as
`f(x) + 1` where N8k bounds `f`, holds everywhere.

The list is short and explicit, and a builtin not on it is not speculatable,
which is exact rather than a guess: the only effect of leaving a builtin off
is that it is not hoisted out of a loop. It answers the proposal's open
question on crash semantics (`roc-reify-proposal.md:1107-1112`) with one flag
instead of a crash model.
The list is the `speculatable` column of `src/reify/prims.zig`. M10 adds
`List.is_empty`, which reads the length and cannot crash, and leaves
`List.append`, `List.map`, `List.keep_if`, `List.fold` and `Iter.collect` off
it, because each one calls a function or allocates.

`crash` written in a body stays a node where it was written, because the
author put it there. C2 would allow deciding a branch that always crashes as
unreachable; the normal form does not, so an interpreter target can still
report it (7.2). The one crash the author did not write is the rejection of
a literal by its conversion, which the language makes a compile-time error.
N13w (3.13) decides the branches that reach it, as C2 allows.

---

## 2. The shape of the normal form

```
Code(fn)
 ├─ slots             the types of the root's input slots, in slot order (3.18)
 ├─ rows              canonical order, root first
 │   └─ row f_i
 │       ├─ params    positional: p0, p1, ...; types only
 │       ├─ body      a region
 │       │   ├─ nodes n0, n1, ...    one def per operation, in canonical order
 │       │   │   └─ node = op + args (refs to params, earlier nodes, slots, inputs) + type + speculatable
 │       │   │        op ∈ Lit | Prim | Call(row) | Closure(row) | Record | Tuple | List | Tag
 │       │   │             | Wrap | Unwrap | Field | Index | Payload | Elem | OptField
 │       │   │             | Switch(arms, joins), with one output per value it delivers
 │       │   │             | And(regions) | Or(regions)
 │       │   │             | ForRange(region) | ForList(region) | Loop(region)
 │       │   │             | Lambda(region), in the inline and outline views only
 │       │   │             | Crash | Derived
 │       │   └─ end        Value(refs) | Jump(join, refs) | Return(ref) | Branch(switch);
 │       │                 in a loop body also Continue(refs) | Break(refs), one per loop output
 │       ├─ recursive  Bool
 │       └─ digest     content hash of this row's normal form
 └─ provenance         node → source regions and call path; compiler-only
```

"All in defs": every operation is a def with its own index, so a call's result
is always a def and never a nested expression. This is single-assignment form
over a region tree, close to an RVSDG (Reissmann et al., 2020): switches and
loops own sub-regions, and inside a region nodes have no order other than
their data dependencies. The canonical order of section 3.9 is a numbering of
that dependency graph, not a record of how the source was written.

What is gone, compared with `Code.Ir` (`src/build/roc/Builtin.roc:22810`):

| `Code.Ir` carries | Normal form carries |
|---|---|
| `Lambda(List({ name, ty }), ...)`, `Param(Str, _)`, `Local(Str, _)`, `Let(Str, ...)` | positional params and node indices |
| `$x#1`, `bind#N` versions | nothing: single assignment needs no versions |
| `Meta.region` on every node (`Builtin.roc:22687`) | nothing; regions live in the provenance table |
| `Binop`, `Unary`, `Call("Num.F32.sin", ...)` | `Prim("Num.F32.sin")` for every builtin, however it was spelled |
| `If`, `Match` with ordered branches, `Pattern` | `Switch` over a canonical decision tree |
| `For`, `While`, `Break`, `Return`, self tail calls | `ForRange` or `ForList` for a loop with a bounded counter, one general `Loop` for any other; numbered state slots; exits as region terminators, and the code after an exiting statement as a join region (3.11, 3.12) |
| `{ ..r, y: 3 }`, omitted default fields | a full `Record` construction (3.1) |
| a record, tuple or tag built only to be taken apart | nothing: construction followed by a read cancels (3.13) |
| aggregate parameters and loop state of private rows | one slot per scalar component (3.14) |
| `Call(Str, ...)` naming a user function | `Call(row)`, where a row has a digest and no name |
| nested expression trees | defs in canonical order; section 5.4 rebuilds trees on request |

What stays, because it is interface rather than spelling:

| Kept | Why |
|---|---|
| types on every node, including record field names and tag names | they are the function's type; renaming them is a breaking change in Roc already |
| nominal type names | a translator recognizes its own vehicle types, such as `Glsl.Vec3`, by them |
| builtin identities, fully qualified | they are Roc's public API |
| qualified names of the functions in the site's cut | the translator chose them as its primitives, and it recognizes them by these names (3.8) |
| the root row's parameter order | it is the order in `Code(fn)` |
| literal values and their types | they are the computation |
| `Derived(method, ty)` | it has no body to normalize |

---

## 3. Normalization steps

Each step is a rewrite that is valid in Roc under C2, the one declared
coarsening. The table names the equation each step absorbs; section 7 collects
them into R.

| Step | Rewrite | Absorbs |
|---|---|---|
| N1 | desugar to one form | spelling of operators, methods, pipes, `and`/`or` and the `if` they mean, `?`, `??`, `return`, interpolation, destructuring, record update, default fields, literals, `expect` |
| N2 | positional binders | renaming |
| N3 | single assignment | `var` and reassignment versus distinct bindings |
| N4 | dissolve `Let` into a dependency graph | the order of independent bindings |
| N5 | canonical placement and value numbering | where a binding is written relative to branches, and where speculatable work is written relative to loops; binding once versus writing twice, including once before a `match` versus once in every arm |
| N6 | dead-node removal | unused bindings |
| N7 | canonical decision trees | branch order of non-overlapping patterns; `if` versus `match` on a `Bool` |
| N8 | lambda lifting and row formation | local closure versus top-level helper; eta; helper names and locations |
| N9 | canonical order and numbering | everything above, made observable as equal values |
| N10 | provenance | nothing; it keeps the source for error reporting |
| N11 | three loop forms, each canonical | `for` versus `while`; a counted `while` versus `for` over a range; an index loop versus `for` over a list; `for` over a list versus over `List.iter` of it; loop-invariant and duplicate state; a `$done` flag versus `break`; a second counter versus a sum |
| N12 | self tail calls become loops | a tail-recursive helper versus a loop |
| N13 | known-value simplification | building a value and reading it back; matching a known tag; re-testing what a dominating test decided; wrapping and unwrapping a nominal; constants computed from literals; `!(a < b)` versus `a >= b` over integers; a test or an overflow that literal intervals decide |
| N14 | scalar replacement | `f(a, b)` versus `f({ a, b })` versus `f((a, b))` for private helpers; a record-valued `var` versus one `var` per field |
| N15 | flattening associative chains; leaf order | grouping of `Str.concat`, `List.concat`, wrapping arithmetic, bitwise operations, `and`, `or`; `a + 1` versus `1 + a` |
| N16 | builtin laws, opt-in layer L | a `for` loop versus `List.map`, `List.keep_if`, `List.fold`; `map` of `map` versus one `map` |

### 3.0 Order of the steps

The steps run in four phases. The second runs to a fixpoint, because each of
its rules can expose work for another: N13 cancels a record, which leaves a
node for N5 to merge, which lets N7 decide a test.

| Phase | Steps | Runs |
|---|---|---|
| construct | N1, N2, N3, N10, and the N11 lowerings | once, during the reifier's walk of the checked body |
| simplify | the rebuild, which applies N13, N15, N16 if enabled, N5 value numbering, N6, and the row rules N7, N11, N12 and N14 | to a fixpoint, one component of the call graph at a time, callees before callers |
| finalize | N8: the component checked again, parameters renumbered, the digest, identical rows merged | once per component, as soon as its fixpoint ends, before any caller is simplified |
| number | N5 hoisting out of loops, N9 | once per row |

The rebuild copies a row by walking from its result, so a node nothing reads
is never copied: N6 happens in every round, and every rule that counts uses
sees exact counts. The row rules are hooks on the rebuild, not passes after
it: a rule that rewrites a loop or a decision tree builds its result through
the same smart constructors, so the local rules it enables fire in the same
round. A round is needed only when one row rule enables another, and a later
round copies only the regions whose inputs changed; an unchanged region is
reused by its digest.

Every rule builds its result through the smart constructors, never directly,
so a result that is itself a redex is rewritten at once. The rules are one
declared table: for each, the op at its root, the patterns of its arguments,
its side condition and its result. The constructors dispatch on the table, and
the confluence tests of section 9 read their overlapping pairs from it.

Finalizing a component before its callers is what lets a caller see its
callees as they will be emitted. A `Call` is value-numbered by the canonical
row, so two calls to two identical helpers merge like two calls to one, and a
parameter the callee dropped is already gone from every call. The component is
checked again at this point, because N13 can delete a recursive call and N12
removes self calls: if it splits, its parts are simplified and finalized in
callee-first order. Components only shrink, so this ends. A caller is never
simplified a second time for a callee's sake.

The rebuild schedules late. Before each round, every node gets its latest
region: the innermost region that encloses all of its uses, but never inside a
loop the node was outside of. The rebuild builds the node there, and the
dominating facts N13 uses are that region's. So a fact applies to a node
exactly when it dominates every use, whether the source wrote the node inside
a branch or before it, and no rule reads where the source put a node. The
number phase then only hoists speculatable nodes out of loops (3.5), which
changes no region's contents and so enables no rule. Rules that compare
regions, such as N7's merge into `And` and `Or`, compare each region's end and
what it depends on structurally, pairing the parameters of the regions bound
inside the two. They also compare, one by one in the order they were built,
each region's loops that can end the row in `Return`, whether a value reads
them or not, because such a loop decides the row's value
(`src/reify/live.zig`, `exits`; `src/reify/equal.zig`, `Comparison.regions`).
So `if c { for x in xs { if x == k { return x } }; k } else k` keeps both
arms. A content digest cannot stand in for that comparison, because
it names a parameter by the region that binds it, so two arms that bind equal
regions of their own digest apart.

Every rule in the simplify phase decreases one measure, ordered
lexicographically: first the calls a row makes to itself when N12 applies to it
(N12 removes them all at the price of one loop), then the number of loops (N16
removes loops), then the number of general `Loop`s (N11 raises them to `ForRange` and `ForList`), then
aggregate-typed parameters and slots (N14), then the slots and outputs of loops (N11g to N11j, N11o), then the
`Return` terminators on the paths of loops (N11j turns one into `Break`), then
`Apply` nodes (N8i), then the tests in an order `match.before` rejects (N7b hoists them), then switches (N7, and N13's case-of-case), then
`Bool.not` nodes over an `And`, an `Or` or a `Bool` switch (N13t), then calls
of a row that only calls another row over its parameters (N8c), then `List.get` calls (N13m turns a bounded one into `Ok(Elem(..))`, which adds nodes), then nodes,
where each read of a parameter counts as one
(N13, N15, N11), then `is_gt` and `is_gte` nodes (N1l), then the integer
`is_lte` leaves of scrutinees (N13q), then the `Bool` switches whose
scrutinee N13s would flip, then the two-operand commutative calls whose
operands are out of order (N15c: a literal first and a non-literal last), then terminators (T3 replaces several by one), then
joins (T2 and the other join rules of 3.11 remove them), then arm and operand
regions (N7d's factoring), and last the nodes of the graph (N5 merges them, N6
removes them). Switches come before nodes because N7's mirrors remove a switch
and add a `Bool.not` node; `Apply` nodes come before switches because N8i
rebuilds the switch that chose a function with the call in each arm; the
forwarding calls come before nodes because the call one becomes can read a
parameter twice; arm and operand regions come after joins because T3 adds a
join region. A rule is oriented by this measure alone, with no path
order after it: a round whose rules only a path order would rank leaves the
measure where it was, which the driver reports as a compiler bug.

Every component but the last counts the term the row unfolds to, not its
graph. A graph count can rise: when an inner node of a left side has another
reader, it survives the rewrite, so `Switch(is_lte(a, b)) -> Switch(is_lt(b,
a))` adds a node when `is_lte(a, b)` is read elsewhere. Hash-consing rewrites
every occurrence of a node at once, and the unfolded count falls under that
rewrite. N5 and N6 leave the unfolding as it was and lower the last component.
`roc-reify-rule-derivation.md` 2.2 states the check a rule must pass.

So the phase terminates. A lexicographic measure gives no round count that can
be computed from the row the walk built, so the driver checks after every round
that the measure fell, and a round in which it did not is a compiler bug. The
number of rounds is capped by a constant of the language version (plan 2.3).

Termination is not enough for "identical": two bodies in R must reach the same
fixpoint from different starting points, so the rule set must also be
confluent. Every rule is an equation valid in Roc, so a pair of rules that does
not join leaves the normal form incomplete, never unsound. Such a pair is
repaired by adding the rule that joins it, which is Knuth-Bendix completion.
The overlapping pairs are enumerated from the rule table, not listed by hand,
and the R fuzzer of section 9 reports any pair that was missed as two unequal
normal forms. The critical-pair lemma is a theorem about terms; over a graph
with sharing, joinable critical pairs imply confluence only under extra
conditions (Plump, 1999), so the tests also run every rule order on small
graphs with shared nodes.

### 3.1 N1: one form per operation

The reifier resolves most of this already. `x + y` and `x.plus(y)` are one
`Binop` (`Builtin.roc`, `Ir.Binop` docs), and `Str.concat(a, b)` and
`a.concat(b)` are one `Call` (`roc-reify-design.md:155-160`). The normal form
goes the rest of the way:

| Written | Normal form |
|---|---|
| `x + y`, `x.plus(y)`, `Num.I64.plus(x, y)` | `Prim("Num.I64.plus")` |
| `x \|> f(y)`, `f(x, y)`, `x.f(y)` when `f` resolves to one callee | one `Call` or `Prim`, arguments in the callee's parameter order |
| `a and b`, `if a b else Bool.False` | one `And(a, b)`, whose second operand is a region run only when `a` is `True` |
| `a or b`, `if a Bool.True else b` | one `Or(a, b)`, the dual |
| `x?`, the `match` it means | one `Switch` on the `Try` tag, whose `Err` arm ends in `Return` (3.11) |
| an early `return` in a block | a `Return` terminator ending the arm it is written in |
| `x ?? d` | one `Switch` |
| `"${a}-${b}"`, the `Str.concat` chain it desugars to | the same chain |
| `{ uv, time }` in a parameter, `input.uv` and `input.time` | `Field` nodes on the parameter |
| `1_000`, `1000`, `0x3E8` of one type | one `Lit` |
| `!=` | `Prim("... .is_eq")` then `Prim("Bool.not")` |
| `{ ..r, y: 3 }` | `Record` with `y: 3` and `Field(r, f)` for every other field `f` of the type; reified bodies are monomorphic (proposal rule 4), so the field set is closed and known |
| a record literal that omits a field declared `port : U16 ?? 8080` | the same `Record` with `port: 8080` written in, so omitting a default and writing it are one form |
| `.port` read from a type with a default | `Field(port)`, because every construction now carries the field |
| `{ a: v, b: _ }`, or `{ a: v }`, where `b` is `b ?: T` | a `Record` that sets `a` only: its arguments are the fields it sets, and `aux` lists their positions in the type's order. A node that sets every field lists none |
| `{ ..r, a: v }` where `r` has an optional field `b` | a `Switch` on `Unwrap(OptField(r, b))`: the `Ok` arm is a `Record` that sets `b` to the payload, the `Err` arm one that leaves it unset. One level of switch for each such field |
| `{ a, ..rest }` in a pattern | `rest` is the `Record` of the fields the pattern did not name, each read with `Field` from the matched record, or by the `OptField` switch above for an optional field |
| `r.?a.b`, `r.?a.?b` | a `Switch` on `Unwrap(OptField(r, a))` whose `Err` arm is `Err(MissingField)` of the path's `Try` and whose `Ok` arm reads the rest. A last optional segment is its own `OptField`, whose `Try` is the path's |
| `"a${x}b${y}"` as a pattern | `Prim("Str.starts_with")` and `Prim("Str.drop_prefix")` for the prefix, `Prim("Str.split_first")` and a `Switch` on its `Try` for each delimiter, and `Prim("Str.is_empty")` for an exact end |
| a literal of your own type whose `from_numeral` or `from_quote` is a Roc function | a `Call` of its row, with the `Num.Numeral` the compiler builds as the argument, then a `Switch` on the `Try`: the `Ok` payload is the value, and the `Err` arm is a `Crash` |
| `expect cond` inside a body | nothing: an assertion for Roc's own test run has no meaning in a target (`roc-reify-proposal.md:1187-1192`) |

Evaluation order inside one operation follows the operator's definition, so
`x |> make().method(y)` evaluates receiver, pipe value, then written arguments
(`design.md:3905-3915`). Under C2 that order is not meaning: every argument is
evaluated, so the order changes at most which crash happens first.

### 3.2 N2: positional binders

Parameters are `p0 .. pk` in the row's parameter order. A value is referenced
by its node index. A pattern binder is not a binder in the normal form: it is a
`Payload`, `Field` or `Index` node inside the switch arm that established the
tag (section 3.7). No name survives, so no rename can change the value.

### 3.3 N3: single assignment

Each assignment to a `var` is already a separate name in `Code.Ir`
(`$x`, `$x#1`, ...). The normal form drops the names: each assignment is a node,
and a read of the `var` is a reference to the node that last assigned it. A
`var` assigned inside a loop becomes a loop state slot (section 3.8). So these
two bodies are one normal form:

```roc
|x| {
	$y = x * 2.0
	$y = $y + 1.0
	$y
}

|x| {
	doubled = x * 2.0
	doubled + 1.0
}
```

### 3.4 N4: a dependency graph, not a list of bindings

`Let(name, bound, rest)` is a nesting order. The normal form keeps only what
`rest` reads from `bound`. Two bindings neither of which reads the other have
no order in the graph. The order a translator sees comes from N9, which does
not consult source positions.

The one piece of order that is not data is which region a node is evaluated
in, and N5 decides it from the graph under C2.

### 3.5 N5: placement and value numbering

Value numbering merges identical nodes: same op, same args, same type. An
expression written twice and a binding read twice give one node. This is the
sharing that `examples/reifying/glsl/main.roc:20-21` wants: one texture fetch
read four times is one node, whatever the source did.

Two identical nodes merge in exactly two cases:

| Case | Merged into | Why it is exact under C2 |
|---|---|---|
| one sits in a region that encloses the other's | the enclosing one | the body evaluates the enclosing one whenever it evaluates the other |
| every arm of a `Switch` computes it, from operands available outside the switch | one node in the switch's region | the body evaluates it on every input that reaches the switch, so the merged node runs in exactly the same cases |

Two nodes that own regions are identical when their regions end alike over
equal values, so an `if` written twice is one node, and an `if` every arm
computes is one `if` before the switch.

Identical nodes in some arms but not all stay apart, because merging them would
place the work where some arm did not put it. The second case is what makes
`z = p // q` before a `match` whose every arm reads `z`, and `p // q` written in
every arm, one normal form.

Merging is defined over the region tree, not over the order the walk built
nodes in: the rebuild numbers values in dominator pre-order, visiting a
region's own nodes before the regions nested in it. So a node written after a
`Switch` in the source and an identical node inside its arm merge whichever
the walk met first.

Placement decides the region a node sits in, in two steps. For each node it
takes two regions: the latest, which is the innermost region enclosing all its
uses, and the earliest, which is the region its operands allow for a
speculatable node, and the region the body evaluated it in for any other node.

| Step | When | Node | Placed in | Why |
|---|---|---|---|---|
| late | every round of the simplify phase (3.0) | every node | the latest region, but no deeper in loops than the region the node stands in | sinking into a branch evaluates it in fewer cases, which C2 allows, and puts it under every fact that dominates its uses; sinking into a loop would repeat its work on every turn |
| hoist | once, in the number phase | speculatable | among the regions between the latest and the earliest with the fewest enclosing loops and lambdas, the innermost | it cannot fail, so hoisting it out of a loop that may run zero times is allowed; among regions at one loop depth, the innermost is one canonical spot and evaluates it in the fewest cases |

A node that is not speculatable is never hoisted: moving it out of a branch or
a loop would speculate. The hoist step runs after the fixpoint, because a node
hoisted out of a branch inside a loop would leave the facts of that branch
before N13 could use them. It ends by merging the identical nodes it brought
into one region, which changes no content digest.

This is Click's schedule (1995): as late as possible, then no deeper in loops
than necessary. The earliest region of a node that is not speculatable depends
on the source only through its loop depth, so a binding written before an
`if` and read in one branch, and the same binding written inside that branch,
give one normal form, whether or not it can fail. Work written outside a loop
and read only inside it stays outside, and moving it across the loop is outside
R. This holds for speculatable work too: written in a branch inside the loop,
it is simplified under the branch's facts and then hoisted, and written before
the loop, it is not under those facts.

Value numbering compares literals by their bits, so `-0.0` and `0.0` are two
nodes, and a NaN is never a switch key.

### 3.6 N6: dead nodes

A node that no result reads is removed, whether or not it can fail: C2 asks
for Roc's result only where Roc does not crash, so `_ = xs.len()` and
`_ = n // d` both vanish. The same holds for a call argument the callee never
reads (section 3.8): it is dropped with the parameter, and for a switch output
nothing reads: it is dropped from every arm. N6 needs no pass of its
own: the rebuild of 3.0 copies only what a row's terminators reach, so every
round of the simplify phase starts without dead nodes.

Roc itself would still run `n // d`, and crash when `d` is zero. A target that
wants Roc's crashes exactly, such as an interpreter, gets fewer of them; every
other target was never going to reproduce them.

### 3.7 N7: canonical decision trees

`Code.Ir.Match` keeps its branches "in the order they were written"
(`Builtin.roc`, `Ir.Match` docs). Reordering branches whose patterns do not
overlap is a meaning-preserving refactor that authors make often, so the normal
form compiles every `match` and every `if` into a decision tree that depends
only on which arm each input reaches:

1. A position is a path into the scrutinee: the scrutinee itself, a field by
   name, a tuple index, a payload of a tag (the tag name and the payload index), a list element. In the IR a
   position is a node: the scrutinee, or a chain of `Field`, `Index`,
   `Payload` and `Elem` nodes over it, which value numbering makes unique.
2. At each tree node, split on the leftmost-outermost position on which the
   outcome depends, given what the tests above already established. The split
   is on the constructor at that position.
3. Arms of a split are in the canonical order of the type: tags in the union's
   name order, `Bool.False` before `Bool.True`, literals ascending with one default
   arm, list-length tests by length.
4. At a leaf, the arms whose patterns remain possible keep their source order
   only where guards make order meaningful: the first guard that holds wins.
5. Values a pattern bound are `Payload`, `Field` and `Index` nodes in the arm
   that established them, numbered by N9.

N7 is defined over nested `Switch` nodes, not over patterns, which are gone
after the walk. N7b covers the part of a tree that N7a does not: `Builder.interchange`
(`src/reify/builder.zig`) takes a value switch with one output whose arm ends
in a switch on a position of the same root that `match.before` puts before the
position the switch tests, and builds the switch on that position first. Each of
its arms holds the inner arm for that constructor, or a copy of the arm that
does not test it. The positions go in the order of the field index, then the tag
name, then the payload index. It leaves alone two `Bool` switches (N7d and
N13o own their order), switches on two roots that are not both parameters of
the root row, a guard, which is not a position, and a switch with a join or
with more than one output. Two parameters of the root row are roots in
parameter order, the parameter half of N15c (`match.rootedBefore`), so
`match a { P => match t { .. }, .. }` and the match on `t` first meet when `a`
and `t` are the root's parameters. Other roots have no order that no
unrelated edit moves, so their switches stay as written. It never copies an arm that holds a loop, an `Apply`, a `Lambda` or a `Closure` (`match.copyable`), because the measure counts those before the switches a copy adds. `match.inversions` counts the tests left
out of order in a switch whose arms it may copy, and the measure above uses it before it counts switches, because
copying an arm adds switches. The walk builds a `match` as a cascade of switches in source
order, where the first arm whose tests hold wins, and N7 rebuilds every
tree of switches whose scrutinees are positions of one node into the canonical
tree. So the rule also applies to trees that exist only after simplification:
a `match` on a helper's result once the helper is inlined, a literal switch
N13 made from an `if` chain, and the result of case-of-case (3.13).

Rule 2 is a definition, not a column-choice heuristic: it depends on the
mapping from inputs to arms, and two matches with the same mapping produce the
same tree. It resembles the "necessity" criterion of Maranget (2008), stated
over the mapping and not over the clause matrix, because a rule stated over the
matrix depends on row order. `PatStr`, `PatListRest` and `PatGuard` compile to
`Prim` tests (a prefix test, a length test, a guard node) at their positions.

A condition written as nested `if`s and one written with `and` or `or` meet
through one more rule:

| Pattern | Becomes | Condition |
|---|---|---|
| `Switch(a) { False: Y, True: Switch(b) { False: Y', True: X } }` | `Switch(And(a, b)) { False: Y, True: X }` | `Y` and `Y'` compute the same value, compared structurally, and `X` reads from outside itself only what the outer switch can read |
| `Switch(a) { True: X, False: Switch(b) { True: X', False: Y } }` | `Switch(Or(a, b)) { True: X, False: Y }` | `X` and `X'` compute the same value |
| `Switch(a) { True: Y, False: Switch(b) { False: Y', True: X } }` | `Switch(And(Bool.not(a), b)) { False: Y, True: X }` | `Y` and `Y'` compute the same value |
| `Switch(a) { False: X, True: Switch(b) { True: X', False: Y } }` | `Switch(Or(Bool.not(a), b)) { True: X, False: Y }` | `X` and `X'` compute the same value |

So `if a then (if b then x else y) else y` and `if a and b then x else y` give
one normal form. The last two rows are the mirrors, in the way N13 has mirrors
for `And` and `Or` (3.13). Without them the rules do not join: from
`if !a { if b { x } else { y } } else { y }`, the first row gives
`And(Bool.not(a), b)`, while swapping the arms of the switch on `Bool.not(a)`
first gives `Switch(a) { True: y, False: ... }`, which only the third row
matches. The same pair arises from `if a <= b` over integers, whose switch
N13q turns into one on `b < a` with the arms swapped. The comparison covers
the region's terminator and everything it depends on (3.0), so it is exact,
and it gives the same answer whether a node `Y` reads was written inside the
arm or before the `if`. Every row requires that what `X` reads from outside
itself be visible outside the outer switch, because `X` becomes an arm of the
new switch there, and a node of the outer arm it reads would no longer be
visible to it. A constant of the outer arm is built again there, as in 3.15.

With n-ary `And` and `Or` (3.15), N7d has three more families of rows. `S`
is a run of operands, `y'` computes the same value as `y`, and a one-operand
`And(S)` or `Or(S)` is its operand:

| Pattern | Becomes |
|---|---|
| `Switch(a) { False: y, True: Or(S, y') }` | `Or(And(a, Or(S)), y)` |
| `Switch(a) { False: y, True: And(S, y') }` | `And(Or(Bool.not(a), And(S)), y)` |
| `Switch(a) { False: And(S, y'), True: y }` | `And(Or(a, And(S)), y)` |
| `Switch(a) { False: Or(S, y'), True: y }` | `Or(And(Bool.not(a), Or(S)), y)` |
| `Switch(a) { False: Switch(c) { X, Y }, True: Switch(d) { X', Y' } }` | `Switch(Switch(a) { False: c, True: d }) { X, Y }` |
| `Switch(a) { False: Switch(c) { X, Y }, True: Switch(d) { Y', X' } }` | `Switch(Switch(a) { False: negation(c), True: d }) { Y, X }` |
| `Switch(a) { False: And(S0, y), True: And(S1, y') }`, and the same over `Or` | `And(Switch(a) { False: And(S0), True: And(S1) }, y)` |

The first four rows give `if a { b or y } else { y }` the form of
`(a and b) or y`, which the nested-switch rows above cannot reach once N13o
has turned the inner switch into an `Or`. The merge rows give two switches on
the same pair of arms one switch, and require both pairs of arms to be
visible outside the outer switch, as above. `negation(c)` is the negation of
N13t (3.13), built directly. Factoring takes an operand both arms end in out
of the switch.

N7 is the most expensive step and the one to stage:

| Phase | Covers | Leaves outside R |
|---|---|---|
| 1 | a `match` whose patterns are each one tag or literal at the top, possibly with irrefutable payloads; `if`; `?` | reordering arms of nested or overlapping patterns |
| 2 | full decision trees as above | only guarded arms whose patterns overlap, where order is meaning |

### 3.8 N8: rows

A row is a function the root reaches, specialized to one type instantiation,
as today (`roc-reify-design.md:163-170`). The normal form changes three things
about rows: how they are formed, how they are identified, and their parameter
order.

Formation, lambda lifting:

| Written | Normal form |
|---|---|
| a top-level function called directly | `Call(row)` |
| a local function called directly | `Call(row)`; what it reads from the enclosing body becomes leading arguments |
| a lambda passed as a value | `Closure(row)` with captured values as its args |
| `\|x\| f(x)` where `f` is a row | `Closure(f)` with no captures: eta, valid because `f` is a known function, and building a closure is speculatable |
| a call of a row, not recursive, whose body only calls another row over its own parameters | that call: the call half of eta (N8c), so a wrapper leaves no row behind |
| a row with a function parameter, called with a known function | one row per known function, as the reifier already specializes (`roc-reify-proposal.md:1178-1185`); the specialization is keyed by the function's digest, not by the call site, so two call sites passing the same function share a row |
| a generic helper at one instantiation, or a copy written at that type | one row: rows are per instantiation and identified by digest, so making a helper generic changes nothing |
| a call through a function value, `f(x)` where `f` is not a known function when the walk reaches it | `Apply(f, x)`, which exists only during simplification |

A function value can become known only after simplification: read back from
`{ op: g }.op`, or chosen by a branch N13 decides. `Apply` lets the walk build
the call anyway, and three rules resolve it:

| Pattern | Becomes | Condition |
|---|---|---|
| `Apply(Closure(r, captures), args)` | `Call(r, captures ++ args)`, specialized as above when `r` takes a function parameter | none |
| `Apply` of a switch output, where every arm gives a known `Closure` for that output | a switch output whose every arm applies its own closure | the call runs in exactly the cases it ran after the switch, and its arguments are computed before the switch |
| an `Apply` that a row of the site holds once every component is final (N8j) | the site is refused, as proposal section 10 exclusion 1 refuses a function value nothing fixes | none: a normal row contains no `Apply` |

The second row is the rewrite of `roc-reify-prior-art-survey.md` 3.2, so
`(if hdr { tone_map } else { clamp })(color)` describes. A specialization made
this way is a new row: it is simplified and finalized on demand, before the
caller's round continues. It is keyed by the digest of the finalized row it
specializes, the parameter the closure is passed for, the digest of the
closure's row and the types of its captures, so two calls that pass one
function share it. Its finalize can renumber its parameters (N8f), so the call
is built with its arguments permuted to the new row's order.

N8j runs after every component is final, not at each component's fixpoint: a
specialization or the rows V1 simplifies again can still resolve an `Apply`
that an earlier component left.

Identity. A row has no name. Its identity is a digest of its normal form, in
which a call names its callee by digest. Recursive rows form strongly
connected components: a component is hashed as a unit, with calls inside it
named by position within the component. The positions are fixed by partition
refinement on digests computed with those calls held abstract, which is
bisimulation, the algorithm `src/postcheck/type_digest.zig` already runs on
recursive types. Members still tied when refinement stops are bisimilar: they
compute the same thing, so they become one row, and no order among them is
needed. The rule is exact and near linear, with no search over permutations.
Unison hashes mutually recursive definitions by position in the same way.

A digest is computed from content, not from N9's numbering or from placement,
so it exists as soon as a component's fixpoint ends (3.0). A region's digest
reads its end and its loops that can return, read or not, as the structural
comparison does (`src/reify/digest.zig`, `regionDigest`), so a helper with such
a loop and one without it have two digests. Two rows are merged
only when their digests are equal and a structural comparison confirms it: a
hash collision must never merge two computations. The same holds for every
comparison by region digest.

The cut. A translator declares its cut: the functions it reads as primitives,
as the item `code_primitives` of the type that owns the translator (section 12). A
function in the cut of the site is not a row. It is a `Prim` named by its
qualified name, such as `Glsl.Vec3.scale`, and its body is never read. The
translator's own library works this way: `Glsl.roc` maps `Glsl.Vec3.scale` to
`*` and `Glsl.Sampler.texture` to `texture`
(`examples/reifying/glsl/Glsl.roc:516-517`, `:552`), and the functions have CPU
bodies that must not be inlined into the description. The cut belongs to the
translator, not to the library, because what a target has natively decides it:
a GLSL translator keeps a math library's `lerp` as GLSL's `mix`, and a SQL
translator reads its body. Such a primitive is not speculatable, whatever its
body. Builtins are primitives in every cut (7.2).

Every function outside the cut is walked by its body, in any package. A
dependency's body is therefore part of what a translator reads: an upgrade
that changes the normal form of a function the site reaches can change the
translation, or stop it building at the site. This is the policy of plan 1.9,
and it differs from the reach rule of `roc-reify-refactor-safety.md` 4.3,
which read only bodies their authors exposed. The upgrade is explicit, because
a package is pinned by its URL and content hash, and a break names the site.

Consequences: renaming a helper, moving it to another module of the same
package, and reordering top-level definitions change no digest. Two helpers
written identically become one row. The `Test.id#1` serial, which counts in
walk order (`roc-reify-design.md:163`), disappears.

Parameter order. The root row keeps its parameter order, because that is the
type in `Code(fn)`. Every other row's parameters are renumbered in the order
N9 first reaches them in the row's body, the arguments at every call are
permuted to match, and a parameter the body never reads is dropped. The
argument expression is dropped with it, as N6 allows under C2. So a lifted local closure that captures `k` and
a top-level helper that takes `k` as its first parameter give the same row,
and reordering a private helper's parameters changes nothing.

A `Closure` fixes an order of its own: its captures, then the arguments of
each call of the function value. When N8f gives a row that a `Closure` names
another order, the `Closure` names a convention row instead. That row takes
the captures and then the arguments, and its body is only the call of the
renumbered row, so the `Closure` keeps its convention and the renumbered row
is the one every direct call and every other closure of the same computation
names.

Result ranges (N8k). At finalize, a row whose result is of a builtin integer
type records the union of N13u's intervals over its returns. Its callers are
simplified after it (3.0), so N13u reads the recorded interval as the fact on
each `Call` of the row. The interval is data the finalize step stores, computed
from the finalized body; a caller never reads the callee's body for it. A function
in the cut (N8h) records nothing. The returns are the body's value and each
`Return` on the row's paths and in its loops, not in its lambdas. A returned
literal is its value, a node has the interval N13u gave it when it was built,
and anything else, a switch output among them, has the type's full range, as
the source table of 3.13 states (`src/reify/ranges.zig`, `resultRange`). A row
whose union is the full range records nothing.

### 3.9 N9: canonical order

Every list the translator reads comes in an order computed from the graph
alone:

| List | Order |
|---|---|
| nodes in a region | post-order depth-first walk from the region's result, visiting a node's args in their positional order and a switch's arms in the order of 3.7; first visit numbers a node |
| loop state slots | the order the walk of the loop body, from its result, first reads each slot. This rule is not a fixpoint (renumbering the slots can change which the walk reads first), so until the slot rules of M6 the slots keep their order |
| switch outputs | the order the walk first reads each output |
| a switch's joins | the order the walk of its arms, in the order of 3.7, first reaches each join |
| rows | the order the walk first reaches a `Call` or `Closure` of each row, starting from the root; a component's members together, by their 3.8 positions |
| record fields | the type's field order, by name |
| input slots | the order in which the root first reads each slot: its nodes in index order, each node's arguments and then the ends of the regions it holds, and the body's end last (3.18) |

A walk that starts at the result numbers operands before their users, so every
def precedes its uses, which is the order a translator emits statements in.
Argument positions are part of an operation's meaning, so the walk reads no
source-order information. An edit changes the numbering only where it changes
the graph. The numbering of an unrelated part of the body can still shift when
nodes are added before it, which is why section 4.3 keeps external identities
off node indices.

### 3.10 N10: provenance

The compiler keeps a table from every node to the source regions it came from,
each with the call path that reached it. A node that value numbering merged has
several regions. A node that the `inline` view (section 5) moved into a caller
carries the call site as well. The table is not in the `Code` value: the value
carries only the key of its site, and the module that holds the site keeps the
table in its checked artifact (`CodeProvenanceTable`). No rule, digest or view
reads the table, and a translator has no accessor for it. Section 6 uses it.

| Event | Origins of the node (`src/reify/provenance.zig`) |
|---|---|
| the walk builds it | the expression the walk is building |
| hash-consing finds it again (N5a) | its origins and the new ones |
| a rebuild copies it | the old node's |
| a view inlines a call or a closure (V1, V2) | the callee node's, each reached through the call or closure |
| two rows merge (N8g) | its own, and those of every node of the dropped row that the row comparison found equal to it |

When two rows merge (N8g), the nodes are paired by the comparison that
found the rows equal (`src/reify/equal.zig`, `Comparison.matched`), not by
their positions in the two numberings. Rows merge before the number stage, so
two equal rows can share an equal node differently: one literal `3` that two
arms read, against one `3` in each arm (N5d is not built). The pairing is then
not one to one.

| What N10 guarantees after a merge | Why |
|---|---|
| every node of the dropped row is paired with at least one node of the kept row | the comparison visits every node the numbering reaches: what the region ends read, and its loops that can return, read or not; a debug build asserts it (`src/reify/rows.zig`, `mergeInto`) |
| a kept node holds the union of the origins of every dropped node paired with it | a shared `3` takes the origins of both per-arm `3`s |
| a dropped node gives its origins to every kept node paired with it | each per-arm `3` takes the origins of the shared `3` |
| no origin of the dropped row is lost | it lands on a kept node that computes the same value |

### 3.11 N11: three loop forms

`Code.Ir` has `For`, `While`, `Break` and `Return` (`Builtin.roc`, `Ir.For`
docs). The normal form has three loop nodes, and a loop body ends in a
terminator rather than a value:

```
ForRange(start, end, inclusive, slots, body)   body params: the index, then the slots
ForList(list, slots, body)                     body params: the index, the element, then the slots
Loop(slots, body)                              body params: the slots

  slots   initial values, one per state slot
  body    a region whose every path ends in one of
            Continue(next values)   run another turn
            Break(value)            the loop ends, and this is its value
            Return(value)           the enclosing row returns
```

`Return` can end a path of any region of a row, inside a loop or not.
`Continue` and `Break` end paths of a loop body only.

`ForRange` and `ForList` deliver their slots when the indices run out, and a
`Break` carries them too, so a bounded loop has one output per slot. A
general `Loop` ends only through `Break` or `Return`, so what it delivers is
what its `Break`s carry, and its outputs are its own: the node lists their
types, `Break` has one value for each, and they need not be the slots. This
is what lets a tail-recursive row (3.12) be a `Loop` that delivers the row's
result and no slot.

`ForRange` runs its body once for each index from `start` up to `end`,
excluding `end` unless `inclusive`; `ForList` runs it once for each element of
`list` in index order. When the indices run out, the loop's value is its
slots. A general `Loop` ends only through `Break` or `Return`.

Why three nodes, when one `Loop` can express all of them: a bounded counter's
start, test and step are the loop's structure, not computation in its body. As
a general `Loop`, every translator for sets and streams would have to
recognize them again, the speculatable classification of 1.1 would need an
exception for the counter step, and `a..=b` would need a done flag so the
counter does not step past the type's highest value. The two bounded nodes
carry that structure, and normalization loses nothing: the raising rules below
are exact, so every loop with a bounded counter reaches the same node, however
it was written. This is the reason `And` and `Or` are nodes and not `Switch`
encodings (3.1).

Terminators are not values for the same reason. A loop body that ended in a
`Tag` value of a `Continue | Break | Return` type would be control encoded as
data: N13's tag rules would read it, and every translator would have to tell
it from a user's tag of the same name.

#### Exits and joins

`break`, `continue` and `return` can appear in any arm of any `if` or `match`,
and code can follow the statement that holds them. Three things must hold for
that to normalize: the code after such a statement is never copied, it never
runs before the test that could skip it, and one computation has one shape.

The code after the statement cannot share the region of the switch. Nodes in a
region are ordered only by their data, so in
`if y == 0 { break } else if c { $s = a } else { $s = b }; z = x // y` nothing
would order `x // y` after the test, and a translator could divide by zero
where Roc did not. The code after goes into a join instead: a region with
parameters, owned by the switch, that the arms which continue end in by
jumping to it (Maurer et al., 2017). A switch that owns a join ends its
enclosing region, so every node after it is inside the join, and N5 places a
node that is not speculatable no earlier than the region it was written in.

A `Switch` has two forms:

| Form | Arms end in | The switch |
|---|---|---|
| value switch | `Value(outputs)` | is a node with one output per value it delivers; the region continues around it |
| exiting switch | a terminator, or `Jump(join, values)` | ends its region in `Branch`; its joins end like any region, and a join may jump only to a later join of the same switch, so jumps never form a cycle |

A switch has one output per value its arms deliver, not one switch per value:
`if c { $s = a; $t = b } else { ... }` is one switch with two outputs. So a node
that one arm computes for several outputs stays in that arm, and is neither
copied into several switches nor hoisted out of the arm. An output equal in
every arm leaves the switch (3.13), and an output nothing reads is removed
(3.6).

Six rules give the three properties:

| Rule | Form | Why |
|---|---|---|
| T1 | the walk builds a statement that exits in some arms as an exiting switch; the code after it is one join, and every arm that continues jumps to it | the code after is written once, however many arms continue: copying it into each would double the body for every such statement in sequence |
| T2 | a join that exactly one `Jump` reaches is inlined at that jump | `if c { break }; rest` and `if c { break } else { rest }` are one form, and nothing is copied, because only one arm receives the code |
| T3 | when every arm and join of an exiting switch that does not jump ends in the same kind of terminator, `Continue`, `Break` or `Return`, the switch becomes a value switch with one output per value of that terminator, and the region ends in one terminator of that kind over the outputs | `if c { $s = a; continue }; $s = b` and `$s = if c a else b` are one form |
| T4 | a join with no nodes of its own is substituted into each jump that reaches it | its end is one terminator or jump, so substituting it copies one end; it exposes T3 where a join only passes values on |
| T5 | an exiting switch none of whose arms and joins reaches a terminator becomes a value switch: jumps to the join that holds the code after become `Value`, and that join's nodes rejoin the enclosing region | after N13 decides the exiting arm away, the switch has the shape it would have had without it |
| T6 | a `Return(v)` in tail position becomes `Value(v)`: in the row's body, or in an arm of a value switch whose output the row returns | `return x` as the last statement and `x` are one form |

T1 is how the walk builds exits (N11f). T2 to T6 are smart constructors that
fire when a switch or a region is closed. They join: from
`if c { continue(a) }; continue(b)`, T2 inlines the join into the one arm that
reached it, which gives a switch whose arms end in `Continue(a)` and
`Continue(b)`, and T3 gives `Continue` of `Switch(c) { a, b }`. T4 reaches the
same form first when the join is only `Continue(b)`. Both are what
`$s = if c a else b` builds directly.

The same rules cover `return` and `?` outside loops, which are the same
problem: `x?` is a switch on the `Try` tag whose `Err` arm ends in `Return`, and
whose `Ok` arm reaches the rest of the body, through T2 when it is the only
arm that continues.

A general `Loop` whose body ends in `Continue` on every path is an infinite
loop in Roc, and stays one: the normal form does not decide divergence.

Every loop in the source lowers to one of the three:

| Written | Normal form |
|---|---|
| `while c { ... }` | `Loop`: the body ends in `Branch` on a `Switch` on `c`; `Bool.False` ends in `Break(state)`, `Bool.True` runs the written body and ends in `Continue` |
| `for x in a..<b` | `ForRange(a, b, False)` |
| `for x in a..=b` | `ForRange(a, b, True)` |
| `for x in xs` over a `List` | `ForList(xs)` |
| `for x in it` over any other iterator | `Loop` with an iterator slot starting at `it.iter()`; the body switches on `next`'s result |
| an iterator loop whose iterator is `List.iter(xs)` | `ForList(xs)`, as for `for x in xs` |
| `break`, or a loop ending normally | `Break` with the current state, narrowed by the exit rules below |
| `return v` inside a loop | `Return(v)` |

Inside a `ForRange` body, the index is known to be in range, and inside a
`ForList` body, below `List.len(list)`. These are dominating facts for N13,
like a `Switch` arm's.

Hand-written loops meet the lowered ones through two raising rules, which run
in the simplify phase:

| Pattern | Becomes | Condition, all exact |
|---|---|---|
| a `Loop` whose body ends in `Branch` on a `Switch` on `is_lt(s, b)`, where `s` is a slot of a builtin integer type starting at `a` | `ForRange(a, b, False)` with `s` as the index and the other slots kept | `b` does not depend on the slots; the `False` arm is `Break` of the other slots; every `Continue` passes `plus(s, 1)` or `plus(1, s)` for `s`. The checked `plus` cannot overflow under `s < b`, so dropping it is exact. The slot is the one the test reads, so at most one slot can match, and no order among slots is consulted. The test may also be `is_lte(b, s)` with the `True` arm leaving, which is how `if s >= b { break }` arrives: N13q turns the test of a value switch into `is_lt`, and an exiting switch keeps the form the walk gave it |
| `ForRange(Lit(0), List.len(xs), False)` | `ForList(xs)`, with every `Elem(xs, index)` in the body replaced by the element | `xs` does not depend on the slots |
| a `Loop` with an iterator slot that starts as `List.iter(xs)` (through `Iter.iter`, which is the identity), whose body switches on `Iter.next` of that slot, ends in `Break` of the other slots on `Done`, and passes the `rest` of the step as the iterator on every `Continue` | `ForList(xs)` with the other slots kept; the `item` the body reads is the element | the iterator and the step are read by nothing else. The procedures are recognized by the checker-authored `IteratorProcedureId` on the named primitive, never by a name |

With them, and N13's rule for `List.get` under a bound (3.13):

| Hand-written | Meets | Because |
|---|---|---|
| `while $i < n { ... $i = $i + 1 }` over an integer type | `for i in $i..<n` | the first raising rule |
| `for i in 0..<xs.len() { x = xs.get(i)? ... }` | `for x in xs` | the second raising rule, then `List.get(xs, index)` inside `ForList(xs)` is known `Ok` of the element, so the `?` switch is decided |
| `while $i < xs.len() { x = xs.get($i)? ... }` from `$i = 0` | `for x in xs` | both rules, then the same |

Before a raising rule can match, other rules bring the many spellings of a
counted loop to its pattern:

| Written | Brought to the pattern by |
|---|---|
| `while i < n`, `while n > i`, `while !(i >= n)` | N1l, N13q |
| `while Bool.True { if i >= n { break } ... }` | N13c takes the outer arm; N13q gives `is_lt` with the arms swapped; T2 moves the rest of the body into the arm that continues |
| `i = i + 1` or `i = 1 + i` | the raising rule accepts both argument orders; it matches, it does not reorder |
| a step written on several paths | N5c and T3 make it one node in one `Continue` |
| two counters that start equal and step together | N11i merges them into one slot |
| the bound threaded through as a slot that never changes | N11g |
| the counter not read after the loop | N11j narrows the `Break` |
| a tail-recursive helper, with the base case in either branch | N12, then the rows above |

The raising rule reads only what the loop computes, so its answer does not
depend on how the loop was spelled, and a loop it misses stays a general
`Loop`: a missed normalization, never an unsound one.

`while $i <= n` with `$i = $i + 1` does not meet `a..=b` in general. It
overflows when `n` is the type's highest value, and the range does not, so the
two mean different things in Roc, and it stays a general `Loop`. When N13u's
interval of `n` is below the type's highest value, the step never overflows
where the test holds, and the raising rule gives the inclusive `ForRange`.
The same holds for `if $i > n { break }`, which is `is_lt(n, i)` with the arm
for `True` leaving. The interval is the builder's at the place the loop is
built (`loops.Where.below_max`), so a bound that the loop body computes, even
one that does not change, has no interval yet, and the loop stays a general
`Loop` (`src/reify/loops.zig`, `raiseCounter`).

A counter read after the loop keeps the loop a general `Loop`, with either
test. This includes a sum that starts at the counter's initial value and
steps by 1: N11i merges it with the counter, so `var $s = 0` with
`$s = $s + 1` in `while $i <= n` stays a `Loop`, while the same sum in a
`for` over `0..=n` is a `ForRange` with two slots. They do not meet today.

Slots are normalized like nodes:

| Slot | Rule |
|---|---|
| continued unchanged on every path | loop-invariant: replaced by its initial value and removed |
| read by nothing after the loop and by no other slot or exit | dead: removed |
| equal initial values and equal next values under the assumption that the slots are equal | merged. This is optimistic value numbering over the loop (Alpern, Wegman and Zadeck, 1988), which decides the assumption exactly |
| of record or tuple type | split by N14 |

Exits are normalized too, so that a loop reads the same whichever construct
wrote it:

| Exit | Rule |
|---|---|
| a `Return(v)` terminator in a loop whose value is its row's result | becomes `Break(v)`: both end the row with `v`. It applies to a general `Loop` whose one output is the row's result type |
| an output of a general `Loop` that every `Break` gives as one value defined outside the loop | is that value, and the loop no longer delivers it. A loop whose outputs nothing reads is dropped as any unread node is, so the rule assumes a loop ends, as that drop does |
| `Break(state)` terminators, and the normal end of a bounded loop, in a loop whose value is read only through `Index` or `Field` | each carries only the components that are read, and the reads after the loop are removed. Exactly one exit runs, so the value is computed once, at the same point |

In Roc, `for x in xs` already means a loop over `xs.iter()` that switches on
`next` (`design.md:11384-11425`), so `for x in xs`, `for x in xs.iter()` and a
`while` loop over a `List.iter` value are one computation. The lowering
recognizes `List.iter` by the checker-authored `IteratorProcedureId` on the
call, never by the type's name (`design.md:5910-5920`). Its declared contract
is what makes the rewrite exact: the iterator yields every element in index
order, one per step, and never `Skip`s. An iterator built by an adapter, such
as `xs.iter().keep_if(p)`, has a different contract and stays a general
`Loop`, unless a layer L law (3.16) raises it.

#### Facts across turns

Two rules read what every edge into a loop's next turn passes, so a slot whose
role is fixed by those values leaves the loop:

| Rule | Pattern | Becomes | Condition |
|---|---|---|---|
| N11n, a decided leading test | a general `Loop` whose body starts with a `Bool` switch on a slot `s`, or on `Bool.not(s)` | each `Continue` whose value of `s` selects the exiting arm jumps to a join that holds that arm, with the other next values as its parameters; the switch is replaced by its continuing arm, and N11h removes `s` | the initial value and every `Continue` pass `s` as a `Bool` literal or as a value a dominating test decided, and the initial value selects the continuing arm |
| N11o, a derived counter | a slot `j` of a `ForRange(a, b)` body, with initial value `j0`, that every `Continue` passes as `plus(j, 1)` or `plus(1, j)`, and that nothing after the loop and no exit reads | each read of `j` in the body becomes `plus(i, minus(j0, a))`, where `i` is the index, and `j` is removed | `a` is the literal `0`, so the difference is `j0`, or N13u proves that `minus(j0, a)` fits its type |

N11n makes a loop controlled by a `$done` flag meet the same loop with a
`break` where the flag is set: the flag's edges are literals, so the leading
test is decided on each of them. It removes a switch, the measure's earlier
component, and the joins it adds come later in it.

N11o is exact without a range proof on the sum. `plus(i, minus(j0, a))` at a
turn equals the value the slot holds at that turn, which the body computed
without overflow on the edge before it, so the sum overflows nowhere the slot
did not. Only the difference can overflow where the body does not, which the
condition excludes. A step other than 1 would multiply the turn count, whose
product can overflow where the slot does not, so it stays a slot.

#### What a loop iterates over

The lowering erases which construct wrote a loop, and with it the intent a
translator for sets and streams wants: SQL and DBSP read "for each element of
`xs`" as a scan or an aggregation, not as a counter. The loop node carries that
intent, and `Code.Graph.iteration` reads it off the node:

| Node | `iteration` |
|---|---|
| `ForList(xs)` | `OverList({ list, item, index, exits_early })`: `item` and `index` are the body's parameters when the body reads them; `exits_early` when a `Break` or `Return` terminator is reachable in the body |
| `ForRange(a, b, inclusive)` | `OverRange({ start, end, inclusive, index, exits_early })` |
| `Loop` | `General` |

In the Roc API, `item` and `index` are `Read(Val)` when the body reads the
parameter and `Unread` when it does not, and `exits_early` is `True` when a
`Break` of this loop, or a `Return`, ends a path of the body, a nested loop's
`Break` and a lambda's body not counted. The accessor is
`Code.Row.iteration(row, node_index)` (`src/build/roc/Builtin.roc`).

Two properties keep the accessor from reopening the remark:

1. It reads the node and nothing else: never provenance and never regions,
   which still record the construct the author wrote. It is a function of the
   normal form, and any function of the normal form gives the same answer for
   every refactor in R. So `for x in xs`, `for x in xs.iter()`, a `while` over
   an index, and a tail-recursive helper over an index all give `OverList`.
2. The classification is done once, by the raising rules, which normalization
   needs anyway. No translator, and no second implementation in the compiler,
   matches a loop's shape.

Loops that do not meet in the normal form classify differently, as they
should: a loop stepping by 2 is `General`, and `while $i <= n` with no bound
on `n` (3.13) is `General` where `for i in a..=n` is `OverRange` (7.1). So are a loop that counts down, a
loop with a float counter, which is not a range, and a loop over a `Dict`,
`Set` or `Str` iterator, which a SQL translator then cannot read as a scan.
Non-tail recursion is not a loop at all, so there is nothing to classify.

### 3.12 N12: tail recursion as a loop

A row whose every call to itself is in tail position becomes a row whose body
is a `Loop`. The parameters become slots, a tail call becomes `Continue` with
the call's arguments, and every other path end becomes `Break` of the row's
value. The row's value is the loop. A `Return` in the body becomes a `Break`
too, by the exit rule of 3.11. A parameter
every tail call passes unchanged is invariant and is removed from the slots by
N11, and a loop that counts is raised to `ForRange` or `ForList` by 3.11.
N12 runs in the simplify phase, so a call that N13 moves into tail position is
covered too.

The row then has no call to itself. If it was its component's only member, it
is no longer recursive, so `inline` inlines it and a GLSL translator, which
forbids recursion, can emit it. A helper written as a loop and the same helper
written as tail recursion give one normal form.

N12 covers self tail calls only. Mutual tail recursion stays recursive: turning
it into a loop needs a dispatch slot, whose shape no source loop has, so it
would absorb no refactor.

### 3.13 N13: known values

A rule in this step replaces a node whose value, or whose taken branch, is
already known from the graph:

| Pattern | Becomes | Condition |
|---|---|---|
| `Field(Record(..., f: v, ...), f)` | `v` | none: the other components are dropped |
| `Index(Tuple(..., v, ...), k)` | `v` | the same |
| `Payload(Tag(t, ..., v, ...), t, k)` | `v` | the same |
| `Unwrap(Wrap(v))` | `v` | none |
| `Switch` on `Tag(t, ...)` or on `Lit` | the arm for `t`, or for the literal | none |
| `Switch` at a position a dominating arm already decided | that arm | the dominating arm tested the same node at the same position |
| `Switch` on an output of another switch `s`, where every arm of `s` gives that output as a known `Tag` or `Lit` (case-of-case) | `s`, with each of its arms continuing into the outer arm its value selects: an outer arm that one arm of `s` selects is inlined there, and one that several select becomes a join of `s` they jump to, with the tag's payload and `s`'s other outputs as its parameters | none: every test runs in the order it ran, each outer arm runs in exactly the cases it ran, and nothing is copied. The build holds this for a switch `s` with one output, no other reader (the rebuild tells the builder), and arms that select different outer arms. An outer arm that two arms select needs a second join, which an exiting switch cannot carry (3.11), so that case stays a switch on `s`'s output |
| `Switch` `o` on an output of a value switch `s`, where an arm of `o` ends in the crash of a rejected literal, and every value that `s` gives for the output, through its arms and the value switches they end in, is a known `Tag` or `Lit` that selects such an arm, except one value `v` (N13w) | `o` on `v`; `s` and its tests are dropped | the work `v` needs from inside `s` is speculatable, and `o` is the only reader of the output, as for case-of-case. C2 allows it: a path to a rejected literal crashes, so `v` is the result wherever the body has one, and nothing that can fail is evaluated where it was not |
| `Switch` on a `Bool` whose arms are `Lit(False)` and `Lit(True)` | the scrutinee | none |
| `Switch` on a `Bool` whose arms are `Lit(True)` and `Lit(False)` | `Prim("Bool.not")` of the scrutinee | none |
| `Bool.not(Bool.not(x))` | `x` | none |
| `Switch` on `Bool.not(c)` | `Switch` on `c` with the two arms swapped | none |
| a switch output that every arm gives as the same value | that value, and the output is removed | the value is available outside the arms, which the merge of 3.5 makes true whenever every arm computes it from values outside the switch |
| `Switch` on a `Bool` whose arms are `False: Lit(False)` and `True: b` | `And(scrutinee, b)` | none |
| `Switch` on a `Bool` whose arms are `True: Lit(True)` and `False: b` | `Or(scrutinee, b)` | none |
| `Switch` on a `Bool` whose arms are `True: Lit(False)` and `False: b` | `And(Bool.not(scrutinee), b)` | none |
| `Switch` on a `Bool` whose arms are `False: Lit(True)` and `True: b` | `Or(Bool.not(scrutinee), b)` | none |
| `And` with a `Lit(True)` operand, `Or` with a `Lit(False)` operand | the operand removed; one operand left is that operand | none |
| `And` with a `Lit(False)` operand, `Or` with a `Lit(True)` operand | that literal | none: C2 lets the other operands' work go |
| an `And` operand that an earlier operand, or a dominating arm, already decided `True`; an `Or` operand decided `False` | removed; with no operand left, the `And` is `Lit(True)` and the `Or` `Lit(False)` | the same fact rule as for `Switch`. The `Or` half is the dual that N13t needs: `Bool.not(And(a, a))` becomes `Or(Bool.not(a), Bool.not(a))`, and the two meet only if both halves remove the repeated operand |
| `Prim(p)` over `Lit` arguments, `p` speculatable | the `Lit` the compiler's interpreter computes | none |
| `Prim(p)` over `Lit` arguments, `p` a float builtin | the `Lit` whose bits Roc's float code gives, with Roc's one `NaN` for any `NaN` | none: `0.1 + 0.2` folds to `0x3fd3333333333334` at `F64` and to `0x3e99999a` at `F32`, and `-0.0 == 0.0` holds |
| `Str.is_eq` or `Str.concat` over `Str` literals | the `Bool` or `Str` literal | none |
| a chain of `plus_wrap`, `times_wrap`, `bitwise_and`, `bitwise_or`, `bitwise_xor` or `Str.concat` with two literals side by side | the chain with the two replaced by the literal they compute | none: the order of the other operands is kept |
| `Bool.not(x)` where a dominating arm or an earlier `And` or `Or` operand decided `x` | the opposite `Lit` | the same fact rule as for `Switch` (`Builder.decidedNot`) |
| a `Bool` that ends an arm or an operand, where a dominating arm or an earlier operand decided it | the `Lit` it decided | the same fact rule as for `Switch` (`Builder.decidedRefs`): `if c a else c` ends its `False` arm in `False` |
| `Prim(p)` over `Lit` arguments, `p` not speculatable | the `Lit` it computes | only when this evaluation does not fail: `7 // 2` folds, `1 // 0` stays, because folding it into a `Crash` would evaluate where the body might not |
| `List.get(xs, i)` under a dominating `is_lt(i, List.len(xs))`, `i` a `U64` | `Tag(Ok, Elem(xs, i))` | the index is in bounds. The bound comes from a dominating arm, from an `And` operand or `Or` operand, from `Bool.not` of the inverse test, or from `is_lte(List.len(xs), i)` in the other arm (`Builder.boundedGet`) |
| `List.get(xs, i)` in the body of `ForList(xs)` whose index is `i` | `Tag(Ok, element)`, where `element` is the body's element parameter | none |
| `Bool.not(is_lt(a, b))`, `Bool.not(is_lte(a, b))` | `is_lte(b, a)`, `is_lt(b, a)` | a builtin integer type |
| `Switch` on `is_lte(a, b)` | `Switch` on `is_lt(b, a)` with the two arms swapped | a builtin integer type |
| `Bool.not(And(x1, ..., xn))`, `Bool.not(Or(x1, ..., xn))` (N13t) | `Or` and `And` of the negations of `x1` to `xn` | none |
| `Bool.not` of a `Bool` switch (N13t) | the switch with each arm's value negated | none |
| `Switch` on a `Bool` `c` with two arms (N13s) | `Switch` on the negation of `c` with the two arms swapped | the negation has fewer `Bool.not` leaves; on a tie, fewer integer `is_lte` leaves; on a tie, `c` is an `Or`, or, when `c` is neither an `And` nor an `Or`, its first leaf is a `Bool.not` or an integer `is_lte` |

N13w is what makes a literal's conversion meet the conversion without its
rejection. The `Err` of `T.from_numeral`, `T.from_quote` or
`T.from_interpolation` is a crash that the compiler writes where the literal
stands (`src/check/code_reifier.zig`, `convertedWith`). The author did not
write it, so it is a `Crash` of kind `rejected_literal`
(`src/reify/ir.zig`, `CrashKind`), and a translator sees it as the `Crash`
it is. The tests of an interpolated literal's first stage run over the
literal's segments, so a stage that rejects in an `if`, in a `match`, in a
chain of tests or in a helper that returns a `Try` is a switch, or a tree
of switches, whose every value but one is the `Err` tag. N13w drops the tree,
and N13c then takes the `Ok` arm of the conversion's own switch, so every
spelling of the rejection describes as the conversion that never rejects. A
rejection whose path stays behind a call that is not inlined stays the
crash. A crash that the author wrote stays where it was written, and so do
the tests that reach it. N13w copies nothing: an arm of `o` that several
values select is a crash, and it is not copied, because `o` keeps its arms.
The normal-form check fails where N13w still applies
(`src/reify/match.zig`, `rejectedKept`).

Case-of-case is what makes a helper that returns a tag meet the code it
replaced. `parse(s)?`, with `parse` an `if ok Ok(v) else Err(e)`, is a switch on
the tag of a switch in the `inline` view; case-of-case turns it into
`if ok { ... } else { return Err(e) }`, which is what the author would write
without the helper. It needs joins: without them, an outer arm that two inner
arms select would have to be copied.

A dominating test is a `Switch` arm that encloses the node, an earlier operand
of an enclosing `And` or `Or`, a `Loop` body whose leading switch tested the
fact, or the body of a `ForRange` or `ForList`, whose index is in range. The
test facts are exactly these patterns, and the intervals of N13u below are
computed from them and from literals by interval arithmetic, not by a prover.

The two comparison rules keep `<=` for translators and still make `a >= b` and
`!(a < b)` one form over integers. `Bool.not` over a comparison flips it, so a
comparison used as a value keeps its operator; a comparison a `Switch` tests is
always `is_lt`, so `if a >= b x else y` and `if a < b y else x` meet. They join
with the rule that swaps the arms of a `Switch` on `Bool.not(c)`: from
`Switch(Bool.not(is_lt(a, b)))`, both orders reach `Switch(is_lt(a, b))` with
the arms swapped. Floats are excluded, because `!(a < b)` holds for `NaN` and
`b <= a` does not.

N13t puts every `Bool` value in negation normal form: a `Bool.not` sits only
on a leaf, which is anything but an `And`, an `Or` or a `Bool` switch, so
`!(a and b)` and `!a or !b` meet. The negation of a value negates each leaf:
it drops a `Bool.not`, flips an integer comparison, and puts `Bool.not` on
any other leaf. A scrutinee has a second form, because a switch absorbs one
negation by swapping its arms, and N13s picks between the two by counting the
leaves through `And`, `Or` and `Bool` switch arms. Each of its tests gives the
opposite answer on the negation of a scrutinee in negation normal form, so a
switch flips at most once, and `if !a or !b { x } else { y }` and
`if a and b { y } else { x }` meet. N13i and the switch half of N13q are the
cases of N13s whose scrutinee is one leaf. A rule that negates builds the
negation directly rather than as a `Bool.not` node for N13t to push down, so
N13s and N13t terminate with any other rule knocked out.

Constant folding uses Roc's semantics: `F32` arithmetic is folded as `F32`,
by the same code the interpreter runs. Roc's float builtins are its own
software implementations in strict float mode, not the host's math library
(`src/builtins/float_math/f32.zig:245`, `src/builtins/float_math/tan.zig:14-15`),
so a fold gives the same bits on every machine the compiler runs on, and
`sin` folds like `+`. This is the guarantee Roc already relies on for
top-level float constants, which compile-time evaluation computes with the
same code. The folder must call these implementations and never a Zig
intrinsic such as `@sin` or a host library, and a test pins the bits on every
CI platform.
A target that would have computed the value differently, such as a GPU with
relaxed precision, now receives the value Roc computes, which is the one a
Roc `expect` would check against. It also narrows a case the proposal refuses
today, a top-level value that has to be computed
(`roc-reify-proposal.md:1125-1134`). If the reifier describes such a value's
body where it is read instead of refusing it, folding turns
`limit = [1, 2, 3].len()` into a literal. A computed value whose inputs are not
literals stays a computation.

`Wrap` and `Unwrap` are the nominal constructor and its reverse. They cost
nothing at run time, but they change a node's type, and the type is interface,
so the nodes stay where they do not cancel.

A tag is identified by its name, not by its position in its union. A value
of a narrower tag union conforms to a wider slot: its tags keep their names,
so no node stands between the value and the slot, and a verifier checks each
edge with `Types.widens`. A tag switch has one arm per member of its
scrutinee's own type, in name order. Where a call is read at a wider union than
the row's result, inlining builds the helper's ends at the type of the call
(section 2.3 of `roc-reify-tag-names.md`), so a helper gives the same nodes and the
same types as the code written inline. `roc-reify-tag-names.md` has the rules,
and `src/build/roc/Builtin.roc:23930-23936` has the paragraph for translators.

Range facts (N13u). Every node of a builtin integer type has an interval with
literal bounds, kept on the fact stack beside the test facts, so it holds in
a region exactly when its sources dominate the region:

| Source | Interval |
|---|---|
| `Lit(n)` | `[n, n]` |
| a dominating arm of `is_lt`, `is_lte` or `is_eq` between the node and a literal | the half line or point that arm implies, meet with the node's other intervals |
| the index of `ForRange(a, b, inclusive)` | from the least value of `a`'s interval to the greatest value of `b`'s, less one when the range is exclusive |
| the index of `ForList` | `[0, max]` of `U64` |
| `plus`, `minus`, `times` and the `_wrap` forms over nodes with intervals | interval arithmetic; a checked op's interval is met with its type, because the op crashes outside it; a `_wrap` op whose interval leaves the type gets the type's full range |
| a `Call` of a finalized row | the row's result range (N8k) |
| anything else, loop slots of a general `Loop` included | the type's full range |

Loop slots get no interval from their edges: that needs widening, whose
answer depends on the widening order. A missing interval only leaves a
normalization undone; it is never a guess.

Intervals decide nothing on their own. They are conditions that rules read:

| Rule | Reads |
|---|---|
| a comparison of a node with a literal that its interval decides | becomes `Lit(True)` or `Lit(False)`, as N13d does for a test |
| a checked `plus`, `minus` or `times` proved to fit | speculatable in the regions of its facts (1.1) |
| N11l on `while $i <= n` | `n` below the type's highest value (3.11) |
| N11o | the difference `minus(j0, a)` fits |
| N15a on `plus` | a `plus` chain flattens when the sum of its operands' negative lower bounds and the sum of their positive upper bounds both fit the type, so every partial sum of every grouping fits |
| tier F rows the rule-derivation tool writes under interval conditions | such as `(x * 2) // 2 -> x` when `x * 2` fits, and `x % n -> x` when `0 <= x < n` (`roc-reify-rule-derivation.md` 3.4) |

Bounds against a value that is not a literal, such as `i < List.len(xs)`,
stay test facts for N13m. Intervals do not replace them.

The builder holds the sources in `src/reify/ranges.zig` and
`Builder.rangeOf`, and these readings fix what the table leaves open:

| Question | Reading |
|---|---|
| a dominating arm of an `And` or `Or` | the arm where an `And` is `True`, or an `Or` is `False`, gives each operand's fact, as an earlier operand does inside it and as N13m reads a bound |
| an arm of a literal switch on the node | the keyed arm is the point of its key; the default arm gives nothing |
| where a node's interval holds | in the innermost region whose fact it read and below; one that read no fact holds everywhere (`ir.NodeRange.holds_in`) |
| a node found again by hash-consing | it keeps the interval of its first construction, in a region that encloses the one it is read in, met with the facts where it is read |
| a node placement moves | the rebuild builds it again where it goes, with the facts open there, so its interval is the one that holds there; placement does not move a checked op proved to fit out of the region of its facts (`Store.fitFloor`) |
| facts that contradict | an empty interval: the region never runs, and it decides no comparison |
| the comparisons a literal decides | `is_lt`, `is_lte` and `is_eq` with exactly one literal operand; `is_gt` and `is_gte` reach them through N1l |
| a literal switch on an integer | a key outside the scrutinee's interval selects nothing, so its arm goes, and an interval that is one key's value selects that key's arm, as the comparison with the key would decide |
| the value a fact compares | the node of the test, or a node of one projection or builtin op with the same payload, types and operands built in another region: the copy an `And` operand builds is not the copy its arm builds (`Builder.sameValue`) |

L5 checks that the intervals only narrow: the reference evaluator, run on
each fuzz case's input, checks every integer a node with an interval
computes where that interval holds, and every result of a row with a result
range (`src/reify/eval.zig`, `check_ranges`).

### 3.14 N14: scalar replacement

A record or tuple that crosses a boundary the author controls is split into its
components:

| Boundary | Split when | Becomes |
|---|---|---|
| a parameter of a non-root row | the body only reads the parameter's fields or indices, and never passes it whole to a `Prim`, a `Closure` capture, or a result | one parameter per component, in N9 order; each call passes `Field` nodes, which N13 then cancels against the construction at the call |
| a loop slot | the body only reads its fields and continues it with a fresh construction | one slot per component |
| a nested record inside a split one | the same condition, recursively | components of components |

The root row's parameters are never split, because they are the type in
`Code(fn)`. A value passed whole to something opaque is not split, because
that something receives the aggregate. A tag union is not split, because its
components exist only in one arm.

So `f(a, b)`, `f({ a, b })` and `f((a, b))` give one row for a private helper,
and so do a `var` holding `{ x, y }` and two `var`s.

### 3.15 N15: associative chains

The builtin table declares which builtins are associative and speculatable,
and which literal is each one's identity and absorber:

| Builtin | Identity | Absorber |
|---|---|---|
| `Str.concat` | `""` | none |
| `List.concat` | `[]` | none |
| `plus_wrap` on every integer type | `0` | none |
| `times_wrap` on every integer type | `1` | `0` |
| `bitwise_and` | all ones | `0` |
| `bitwise_or` | `0` | all ones |
| `bitwise_xor` | `0` | none |

All ones is `-1` on a signed type and the type's maximum on an unsigned one.

A nested chain of one such builtin becomes one n-ary `Prim` with its arguments
flattened in their written order, and identity literals are dropped. A chain
with its absorber among its operands is the absorber, where every other
operand is speculatable, so dropping them drops no failure. A chain left with
one operand is that operand. `Str.concat` and `List.concat` chains flatten the same way, and `""` and `[]` are their identities. Order is kept, because none of these is declared
commutative in the normal form (section 7.2). Interpolation desugars to
`Str.concat` (N1), so `"${a}${b}c"` and `a.concat(b.concat("c"))` meet here.

Equal operands stay: `x & x` is not `x`, and `x ^ x` is not `0`. With order
kept, merging equal neighbours is not confluent with flattening. Over runs it
is the word problem of free bands, where `ababcbabc` reduces to both `abc` and
`abcbabc`. `xor(xor(a, b), xor(a, b))` is `0` by cancellation but
`xor(a, b, a, b)` by flattening, which has no equal neighbours (7.2).

`plus` and `times` are not in the table: they crash on overflow, and
regrouping can overflow where the written grouping does not. With `a = -1`,
`b` the type's highest value and `c = 1`, `(a + b) + c` succeeds and `b + c`
overflows, so the regrouped body fails where Roc does not, which C2 forbids.
A `plus` chain whose operands' intervals prove that no grouping overflows is
the exception (N13u). Float arithmetic is not associative.

Such a chain is one `Prim` over its operands in order (`Builder.rangeChain`),
and N15c, which reads two operands, does not apply to it. The chain flattens
after N15c has put a literal last in each two-operand `plus` it is built
from, so `(a + b) + c` and `a + (b + c)` meet, and `1 + (a + b)` is
`plus(a, b, 1)` while `(1 + a) + b` is `plus(a, 1, b)`: a regrouping that also
moves a literal stays apart, as it does for the chains of the table above. A
chain of more than two operands is checked `plus` only where N13u proved it
fits, which the verifier checks.

Leaf order (N15c). Commutative operands are not sorted in general (7.2), but
a literal and two leaves have an order that no unrelated edit can change. A
two-operand call of integer `plus` or `times`, or of `is_eq` over a builtin
integer type or `Str`, puts a literal operand last when the other operand is
not a literal, whatever that operand is, and puts two parameters of the root
row in parameter order. Every other pair stays as written. The literal half
lets N13n read `k == x` as `x == k`, so it needs no row of its own. The chain builtins of
the table above are excluded: sorting inside a chain before it flattens is not
confluent with flattening, because `1 +w (a +w b)` would flatten to
`plus_wrap(1, a, b)` and `(1 +w a) +w b` to `plus_wrap(a, 1, b)`. Parameters of
other rows are excluded too: N8 numbers them in first-read order, so an order
by position would change the order N8 reads, and a helper with reordered
parameters would stop meeting itself. Floats are excluded, because the bits of
a `NaN` result can depend on operand order. The root's order is its type, and
a literal is not a parameter, so N9's numbering stays stable. `a + 1` and
`1 + a` meet, and so do `x == y` and `y == x` over the root's parameters
(`Builder.paramOrder`). A root parameter means a parameter of the row whose
parameters are fixed (`ir.Row.fixed_params`): the root, in every view, where
an inlined helper's parameters stand for the root's values. A field of a
record parameter is not a parameter, so `input.x == input.y` stays as written.

`And` and `Or` flatten the same way, with their operands in order:
`And(a, And(b, c))` and `And(And(a, b), c)` both become `And(a, b, c)`.
Short-circuit conjunction is associative, and each operand still runs only when all
earlier ones are `True`. An `And` in an operand region flattens only when its
later operands read nothing that region computes: they become operands of the
outer `And`, and a node they read from the dissolved region would be copied
into each of them. A constant, a node that reads nothing and computes nothing
such as a literal, is the exception: its copy repeats no work, and its place
is not meaning, because N5d places it late and N5b hoists it. Its first operand moves into an operand region of its own,
with the nodes it reads.

### 3.16 N16: builtin laws, layer L

Some refactors trade a loop for a builtin, or one builtin call for another.
Each of these is a law about a builtin's semantics, so it is declared by the
builtin library, tested against the builtin's implementation by the soundness
fuzzer, and versioned with the library. Layer L is opt-in per language version.
Without it, these refactors are outside R (section 7.1).

The direction of each law matters. Lowering every builtin to `Loop` would make
loops uniform and destroy the structure that SQL and GPU translators need: a
`map` is parallel and a `Loop` is not. So each law points at the most
structured form a rule can recognize exactly:

| Law | Direction | Recognized shape |
|---|---|---|
| a `ForList` that appends one value per turn, `$out = $out.append(g(x))` into a slot starting at `[]` and read nowhere else in the body | up, to `Prim("List.map")` with `Closure(g)` | every turn appends once, no `Break` or `Return` |
| a `ForList` that appends its element under a condition | up, to `Prim("List.keep_if")` | the same, with the append inside one switch arm |
| `List.fold(xs, init, f)` with a known `f` | down, to `ForList(xs)` with `f` inlined | a fold has no structure beyond its loop, and `ForList` keeps the scan visible |
| `List.map(List.map(xs, f), g)` | to `List.map(xs, g ∘ f)`, where `g ∘ f` is a row built from both bodies | the inner list is read nowhere else |
| `xs.iter().map(f).collect()` into a `List` | to `List.map(xs, f)` | the iterator adapters carry declared lowering contracts (`design.md:5914-5918`) |
| `is_eq(List.len(xs), 0)`, `is_lte(List.len(xs), 0)`, `is_lt(0, List.len(xs))`, and a literal switch on `List.len(xs)` with the one key 0 (N16f) | to `List.is_empty(xs)`, `Bool.not(List.is_empty(xs))`, and the `Bool` switch on `List.is_empty(xs)` | `List.len` is a `U64`, so a length above 0 is one that is not 0 |

Map fusion interleaves the calls to `f` and `g`, which changes which one fails
first when both can. C2 does not constrain it: every call still runs on every
input where the body does not crash.

Laws change the shapes a translator matches. `examples/reifying/sql/Sql.roc:799`
matches `List.sum(List.map(rows, ...))`; with layer L on, the same computation
written as a fold arrives as a `ForList` over the list. A translator matches the
form after L, and `iteration` (3.11) is what tells it the loop is a scan.

The raising laws are recognizers, but not heuristics: each one is a pattern
over the normal form with an exact condition. A loop that matches is rewritten
every time, and a loop that does not match is never rewritten.

How a site opts in (M10). "Opt-in per language version" does not say who
opts in, so the reading here is the one 1.5 of the plan gives every other
choice of what a site gets: the site's declared type selects it. A site of
type `Code.Lawful(f)` holds the `graph` view normalized with layer L, and a
site of type `Code(f)`, `Code.Inlined(f)` or `Code.Outlined(f)` holds its
view without it. The checker stamps the choice on the site
(`src/canonicalize/NodeStore.zig`, `View.lawful`), the walk passes it to the
driver as explicit data (`src/check/code_reifier.zig`, `Options.laws`), and
the per-site memo key holds the view, so one function reified at two site
types gives two values. The laws are part of the language version: normal
form 13 adds them to the fingerprint (`src/reify/mod.zig`), so a change to a
law moves the version, as a change to any other rule does.

| Law | Side conditions it relies on | Exact, or by C2 |
|---|---|---|
| N16a | the loop is a `ForList` over `[]` with one slot; every turn ends in `Continue(List.append(slot, v))`; the slot is read once, by that append; the index is read nowhere; no `Break` or `Return` | exact: `List.map` in `Builtin.roc` calls the function on each element, first to last, and appends what it gives |
| N16b | as N16a, but the turn ends in `Continue` of a `Bool` switch whose one arm gives `List.append(slot, element)` and computes nothing else, and whose other arm gives the slot and computes nothing; the slot is read twice, by these arms | exact: `List.keep_if` tests each element, first to last |
| N16a, N16b row | the row the law makes holds the nodes of the loop body that the value reads (the cone); a constant outside the loop is copied; a speculatable node outside the loop that only the cone reads is copied; every other outside value is a capture. A cone that reads the index or the slot is no match | exact: a copied node outside the loop is speculatable, so to compute it once per element, or not at all on `[]`, changes no result and no crash; a capture is computed once, before the loop, as before |
| N16c | the function is a `Closure` of a known row; the row's body is inlined in the loop unless the row is recursive or can end in `Return` in a nested region, where the loop calls it | exact: `List.fold` in `Builtin.roc` is that loop, one call per element over the state so far |
| N16d | both functions are `Closure`s of known rows; the outer `map` is the only reader of the inner one; the new row holds `g`'s body over `f`'s body, each inlined as in N16c | by C2: each element now calls `f` and then `g` before the next element, so when two calls can crash, a different one can crash first. The IR has no effect operation, so the crash order is the only change |
| N16e | the `Iter.map` and the `List.iter` are known by the checker's `IteratorRole`, never by name; the result is a `List` | exact: `Iter.map` then `Iter.collect` calls the function on each element, first to last |
| N16f | the length is `List.len`, a `U64`, compared with the literal 0 by `is_eq` (either order), `is_lte(len, 0)` or `is_lt(0, len)`, or tested by a literal switch whose one key is 0. N13 writes `!(0 < len)` as `len <= 0`, and N13n writes `if len == 0` as the literal switch, so each of these is a critical pair that N16f joins | exact: `List.is_empty` is `len == 0`, and a `U64` above 0 is one that is not 0. `List.is_empty` cannot crash, so it is on the speculatable list (1.1) |

A row a law makes is simplified and finalized before the closure that names
it, as a specialization is (N8i). A `Closure` takes its captures first, so
where finalize orders the parameters otherwise, the closure names a
wrapper row that keeps that order (`src/reify/rows.zig`, `conventionRow`).
The measure counts the folds of a closure that N16c can still lower and the
literal switches on a length that N16f can still rewrite (`law_redexes`,
after `self_tail_calls`): N16a and N16b remove a loop, N16c removes a fold,
N16f over a switch removes a literal switch, and N16d, N16e and N16f over a
comparison remove nodes.

Limits of M10:

| Limit | Why |
|---|---|
| layer L applies to the `graph` view only; no `Code.Lawful` form of `inline` or `outline` exists | no translator needs one yet; a type for each pair is a later change of the builtin library |
| N16a and N16b raise only a loop whose function reads the element and outside values; a loop that reads the index, or a counter of its own, stays a loop | `List.map` and `List.keep_if` give the function no index |
| a value bound outside the loop that is not speculatable, `k // m` for example, is a capture of the closure, not part of the row | the loop computes it once, before its first turn; the row would compute it once per element |
| N16c lowers `List.fold` only; `Iter.fold` and folds of other owners stay calls | the laws of 3.16 name `List.fold` only |

### 3.17 N17: known lists

A `List` node holds its elements, so its length is known in the graph. A list
written as a literal, `[c.r, c.g, c.b]`, is one, and so is a list that list
builtins build from known lists. For these lists, the list builtins are
replaced by what their bodies in `Builtin.roc` compute:

| Step | From | To | Source of the equation |
|---|---|---|---|
| N17a | `List.len(List(e1..en))`, `List.is_empty(List(...))` | `Lit(n)`, `Lit(n == 0)` | `Builtin.roc:3748`, `:3763` |
| N17b | `List.get(List(e0..en-1), Lit(i))`; `List.first`, `List.last` | `Ok(ei)`, or the `Err` tag when `i` is not below `n` | `Builtin.roc:4246-4247`, `:4232`, `:4927` |
| N17c | `List.get(List(e0..en-1), x)` with `x` not a literal | a literal switch on `x` with keys `0` to `n - 1`, arm `k` giving `Ok(ek)`, and the default giving `Err(OutOfBounds)` | the same body, with `index < len` decided per key |
| N17d | `concat`, `append`, `prepend`, `single`, `with_capacity`, `set` at a literal index, `drop_first` and `take_first` with a literal count, over known lists | the `List` node of the result's elements | each builtin's body |
| N17e | `map`, `map2`, `map_with_index` over known lists with a known function; `keep_if` where every `p(ei)` is a `Bool` literal | the `List` node of the calls, in element order, and N8i makes each a direct call; for `keep_if`, the kept elements | the builtins' loops, which call the function once per element, in order |
| N17f | `fold`, `fold_rev`, `sum`, `any`, `all` over a known list | the chain of calls; `sum` as the `plus` chain from the first element, `(e1 + e2) + e3`, and `default()` for `[]`; `any` and `all` as n-ary `Or` and `And` of the calls | `Builtin.roc:4747-4754`, `:3300-3310`, `:4884`, `:4912` |
| N17g | `ForList(List(e1..en))` with `n` at most B, whose every path ends in `Continue` | the body once per element, in order, with the slots threaded from one copy to the next | the loop's own semantics |

Each row is exact in Roc under C2. A `List` node evaluates all of its
elements, and a builtin that calls a function calls it on every element, so
every call in the result runs where the builtin ran it. What the rules drop is
dead, which C2 allows (3.6).

Two steps grow the graph beyond what the author wrote: `List.repeat(x, Lit(n))`
in N17d, and N17g, which copies a loop body. Each applies only when `n` is at
most B, a constant of the language version, like K in `outline`. Every other
step is linear in the list the author wrote.

With N17 on, the list refactors below meet:

| Two sources | Normal form |
|---|---|
| `[c.r, c.g, c.b].map2(weights, \|a, w\| a * w).sum()` with `weights` a known list, and `c.r * w0 + c.g * w1 + c.b * w2` | one `plus` chain in `inline`. In `graph`, the lambda is a row called three times (tier B) |
| `for x in [a, b, c] { $s = f($s, x) }` and `[a, b, c].fold(s0, f)` | the same three calls |
| `[a, b].concat([c])` and `[a, b, c]` | one `List` node |

What stays apart, or unchanged:

| Case | Why |
|---|---|
| a list whose length depends on the input: a parameter, a `keep_if` whose predicate is not decided, a list built in a loop with an input bound | its length is not in the graph |
| `[31, 28, ...].get(m - 1) ?? 31` and `match m { 2 => 28, ... }` | N17c makes the lookup a literal switch on `m - 1`, which a translator without arrays accepts. It is not the `match` on `m`: the keys are shifted, and arms equal to the default stay |
| `Iter` pipelines over a known list | the `Iter` builtins have no N17 rows; layer L's N16e lowers `iter().map(f).collect()` to `List.map` first |
| a loop over a known list with a `Break` or a `Return`, or longer than B | it stays a `ForList` |

A translator that has arrays and reads a literal switch whose keys are `0` to
`n - 1` can emit a constant array for it. That is the translator's choice; the
normal form keeps one form.

### 3.18 N18: input slots

A site whose translator returns a `Code.Bound` (`roc-reify-proposal.md`
section 10.1) can read values that exist only when the program runs. Each one
is an input slot of the root, read as `Input(k)`.

| Rule | Statement |
|---|---|
| N18a | A name that the walk cannot replay and that the compiler does not fix is a slot. |
| N18b | `Field`, `Index` and `Unwrap` of a slot is a slot: the slot of its leaf with one more step. No node reads a slot through a projection. |
| N18c | Only the root row reads a slot. A lifted row receives a slot value as a `Closure` argument. |
| N18d | The slot list holds exactly the slots the final root reads, in the order of 3.9. |

N18b keeps two R rows where a slot stands: "bind a value once, or write the
expression twice" and "destructure a record or tuple, or read its fields". A
slot has no name. The site keeps, apart from the value, which run-time name and
which projections each slot reads, as it keeps the provenance table.

---

## 4. Order

The user question: the order of function calls does not matter in pure Roc but
matters in target languages. Is safety only the hope that well-meaning edits
will not reorder calls?

No. Source order is not in the normal form, so a reordering edit cannot reach
the translator. Each kind of order has a defined status:

| Order | In Roc | In the normal form | Reordering it in source |
|---|---|---|---|
| data dependency: `b` reads `a` | meaning | kept exactly: it is the graph | impossible without changing meaning |
| independent bindings | not meaning, or only through which crash happens first | erased; N9 numbers them from the graph | tier A, by C2 where they can fail |
| which branch evaluates a node | only through whether it crashes | erased by sinking (N5) | tier A |
| which side of a loop boundary evaluates a node that is not speculatable | how often it runs, and whether it runs when the loop runs zero times | kept (N5) | outside R |
| arguments of one call | meaning: parameter positions | kept | not a reordering, a different call |
| record fields in a literal | not meaning | the type's order | tier A |
| elements of a list, tuple, tag payload | meaning | kept | a meaning change in Roc too |
| top-level definitions, helpers | not meaning | erased: rows are digests in walk order | tier A |

### 4.1 A target whose operations have order

A GLSL statement list, a SQL plan, a DBSP circuit: a translator must emit
independent operations in some order. It emits them in N9 order, which a
reordering edit does not change. The target does not care which order it gets,
because the operations are independent in Roc, and the translator emits pure
target operations for pure Roc operations.

### 4.2 A target with effects

When target order is itself the meaning, such as draw calls or writes to a
buffer, the Roc body must say so as data, because pure Roc has no other way to
say it: a list of commands, a state value threaded from one step to the next,
a fold. Data order is kept exactly, so the order that matters survives and
nothing else does. If Roc ever reifies effectful functions (proposal 7.8), the
normal form would need explicit state edges, which RVSDG provides for exactly
this, and effectful calls would be ordered by those edges, not by source
position.

### 4.3 Positional identities that leave the translator

The silent failures of the refactor-safety analysis were positional numbering
that other code depends on: uniform slots, SQL `$1`/`$2`, DBSP operator IDs
restored from a checkpoint. Under R, node indices do not change, so none of
these break on a refactor. They can still shift on a real change elsewhere in
the body: adding a computation renumbers everything the walk reaches after it,
and a host program binding uniform 3 by position would then bind the wrong
value. The rule for translator authors, and the accessors that make it easy:

| Identity that leaves the build | Derive it from |
|---|---|
| input slots, bound by a host | the parameter's type: `Code.Graph.inputs` lists record fields by name |
| operator or state IDs persisted across builds | `Code.Graph.inline_digest(node)` in the `inline` view, stable under R and under helper extraction |
| names in emitted text | node indices; they are not API |

---

## 5. Keeping calls as defs

The preference is to leave calls as rows, and to let a translator that cannot
use them inline them. That works, and the cost is small. A third view, which
recomputes helper boundaries from the computation alone, removes even that
cost for a translator that wants functions in its output.

### 5.1 Three views

| View | Rows | Direct calls | Function values | Tier for helper extraction |
|---|---|---|---|---|
| `Code.graph` | recursive components, and non-recursive rows called from two or more places | `Call(row)`; a row called from one place is inlined | `Closure(row)` | A for a helper with one call site, B otherwise |
| `Code.inline` | recursive components, and rows whose body can end in `Return` | inlined, except into a recursive component | `Closure` of a non-recursive row becomes a lambda region in place | A |
| `Code.outline` | recursive components, and rows the compiler chooses (5.3) | `Call(row)` to the chosen rows | as in `inline` | A |

`inline` is defined on the normal form, not on the source: inline every call to
a non-recursive row, then rerun the simplify phase and N9 on the result
(section 3.0). Two properties make it exact:

1. The result equals the normal form of the source with every helper inlined by
   hand. Each inlined body lands in the calling region, which is where
   hand-inlined code would sit. Its nodes are then re-placed by the rule
   they would have followed anyway.
   The simplify phase then does across the old boundary what it would have done
   in hand-inlined code: N13 cancels the records built at the call and read in
   the body, and value numbering merges the rest.
2. So extracting or inlining a helper, in any combination, leaves
   `Code.inline` unchanged: tier A.

`graph` applies the same inlining to one class of rows: a non-recursive row with
exactly one call site after simplification. Inlining can merge two calls that
were distinct only because their arguments differed before simplification, so
the count is taken again until it stops changing. A row that a `Closure` names
stays a row. So does a row whose body can end in `Return`, until the rebuild
turns each `Return` into a jump to the code after the call. That puts the most common
refactor, extracting a helper to give a computation a name, in tier A of the
`graph` view. Tier B remains for exactly one case: a helper that replaces
two or more copies of a computation over different arguments, or the reverse.

Rows are needed regardless, for recursion, so the `graph` view adds no concept.
What it adds:

| Cost | Size |
|---|---|
| row digests and component canonicalization (3.8) | needed for recursive rows anyway |
| parameter renumbering (3.8) | one permutation per row |
| single-call-site inlining | one count per row, repeated to a fixpoint |
| the `inline` view | one extra run of the simplify phase; computed only if asked for |
| `inline_digest` for stable identities (4.3) | the content digest of each node of `inline`, computed while `inline` is built. It is defined only there: a node inside a shared row of `graph` has one inlined content per calling context, so it has no single digest, and computing one per context costs as much as building `inline` |
| tier B in the `graph` view | a translator that emits one target function per row changes its output text on extracting a shared helper, not its behavior |

The `graph` view does not reopen the remark. What it exposes is which
computations the author shared through a helper: helper names, locations,
parameter order, parameter shape and body spelling stay invisible. A correct
translator that emits a target function per row produces an equivalent program
either way. The failure mode that remains is a translator that refuses `Call`,
and that translator should read `Code.inline` or `Code.outline`.

### 5.2 Which translator reads which view

| Translator | View | Why |
|---|---|---|
| GLSL | `graph`: shared rows become GLSL functions, and recursive ones are refused, because GLSL forbids recursion; N12 turns self tail recursion into loops first | GLSL has pure functions, and debuggable output keeps the author's shared helpers |
| GLSL with output that must not change on any refactor, or with a size limit | `outline` | functions without tier B, and bounded size where `inline` would grow |
| GLSL emitting one expression, like `examples/reifying/glsl/Glsl.roc` today | `inline` | it has no function form, so `Call` would be a refusal |
| SQL | `inline`, with recursive rows as recursive CTEs or refused; `iteration` turns `OverList` loops into scans and aggregations | SQL functions are a deployment object, not an expression |
| DBSP circuit | `inline`, with `inline_digest` for operator IDs and `iteration` for loops over collections | checkpoints must survive helper extraction |
| symbolic differentiation | `inline` | the derivative of a helper call is the derivative of its body |
| a JavaScript or interpreter target | `graph` | the target has closures, so rows map one to one |

### 5.3 Rows the compiler chooses

`outline` is a function of `inline` alone. Any function of `inline` is
identical across every refactor in R, because its input is. So the outlining
rule does not have to be optimal, which would be NP-hard: choosing the best set
of functions is the smallest-grammar problem. It has to be deterministic, and
it has to preserve meaning.

The rule:

1. **Cones.** The cone of a node is the node and, transitively, its arguments
   in the same region or in regions it owns, stopping at parameters, slots, and
   nodes that something outside the cone also reads. A cone is a tree of work
   whose only inputs are its stopping points.
2. **Places and keys.** A place is a node whose cone has at least K nodes and
   can be a row (the table below). The key of a place at depth d reads its
   cone from the root down to depth d: the op, payload, types and immediates
   of each node at depth d or less, a literal by its type alone, and every
   other value (a stopping point, a node deeper than d, a region parameter) as
   a leaf, by its type and its number in the order of first occurrence. One
   more key, at depth D + 1, is the key at depth D that also reads each
   literal's value. The places are sorted by their keys at depths 0 to D + 1,
   then by site order. A group at depth d is a run of two or more places with
   one key at every depth up to d. A run equal to the run at depth d - 1 that
   holds it is that group. So groups at different depths hold one another,
   and a group splits only in this way: selection takes the depth that gains
   most. The last depth keeps places that differ only in their literals apart
   from the ones that do not, so a literal hole never hides a row without
   one. D is 3.
3. **Generalization.** The generalization of a group is the least general
   generalization (Plotkin) of its places. A walk visits the cones of all
   places in step from their roots. It meets tuples of values, one value per
   place, and gives each tuple one of these kinds:

   | Tuple | Kind |
   |---|---|
   | nodes of the places' cones with one op, payload, types, immediates, output and region shape (region kinds, parameter types, end kind, counts) | a node of the generalization; the walk goes on into its arguments and regions |
   | literals with one value | a literal, copied into the row |
   | parameters at one place of regions of one node of the generalization | that parameter |
   | anything else | a hole |

   One tuple is one hole, so a hole that is the same value at every place is
   one parameter: `a * a + b` and `c * c + d` give `h0 * h0 + h1`, and
   `a * b + c` with `a * a + d` gives `h0 * h1 + h2`. The values of a hole
   have one type. Holes are numbered in the order the walk first meets them:
   depth first, a node's arguments in order, then per region its end and the
   nodes nothing reads.
4. **Holes that keep meaning.** A `Call` evaluates its arguments before its
   body. So a hole moves its values out of the cone into the caller, ahead of
   the call. These rules make a tuple a hole, or stop it from being one, and
   the walk runs again until none applies:

   | Rule | Why |
   |---|---|
   | a node of a place that the walk meets in two tuples of nodes, or in a tuple of nodes and a hole, is a hole wherever it is met | otherwise the row evaluates it twice where the place evaluated it once |
   | a node that the value of a hole reads at a place, and that a tuple of nodes holds, is a hole | otherwise the caller and the row both evaluate it |
   | no speculation: a value of a hole at a place is a stopping point, a literal, a node in the region of the place's root, or a node whose region is inside the cone and that moves: it, and every node it reads in such a region, is speculatable, owns no region, and reads no parameter of a region inside the cone. Otherwise the tuples of nodes that read the hole are holes | a stopping point and a node in the root's region run on every path where the root runs; a literal and a speculatable node cannot crash, so evaluating them where the place did not is allowed. This keeps the promise of this section: nothing that can fail runs where it did not |
   | a tuple that is not a node at a place that cannot be a hole (a parameter of a region of the generalization, the target of a `Jump` or a `Branch`, a node nothing reads) makes the tuple of nodes that holds the place a hole | such a place is not a value the caller can pass |

   The group has no generalization when its roots become a hole. A place whose
   image (the nodes its tuples of nodes hold) meets the image of an earlier
   place in site order, or of a taken occurrence, leaves the group, and the
   generalization is computed again.
5. **Candidates.** With c places, s nodes in the generalization (literals not
   counted) and h holes, the gain is c × (s - 1) - c × h: each place saves its
   s nodes but one, and passes h arguments. A group is a candidate when c ≥ 2,
   s ≥ K and the gain is above 0.
6. **Selection.** Candidates are taken in order of gain descending, then s
   descending, then the hash of the generalization's shape, then the first
   place in site order, then the depth. A candidate whose evaluation predates a
   take is evaluated again against the occurrences taken since, and goes back
   into the order; a candidate is taken when its evaluation is current.
7. **Rows.** Each chosen generalization becomes a row whose parameters are its
   holes in hole order, copied from its first place. Each place becomes a
   `Call` with the values of its holes as arguments, and a value that moves is
   built just before the call. Then the whole rule runs again on the result,
   so repetition inside the new rows is found too.
8. **Numbering.** N9 numbers the result, and rows are identified by digest as
   in 3.8.

The rule preserves meaning because a `Call` evaluates its body where the cone
stood, and its arguments just before: every node of the generalization runs in
the same region as before, and a value that moves is speculatable (rule 4), so
nothing that can fail speculates. It never outlines across a recursive
component, because `inline` never breaks one.

Each pass terminates and the passes end. A take of c places of a
generalization with s nodes and h holes removes c × s nodes and adds s nodes
in the row and c calls, so the node count falls by (c - 1)(s - 1) - 1, at
least 2. The size the debug check reads counts the arguments of calls too, as
3 × nodes + arguments. A positive gain means h ≤ s - 2, so a take lowers it by
at least 3(cs - s - c) - c(s - 2) = s(2c - 3) - c, which is above 0 for
c ≥ 2 and s ≥ 3. A hole argument counts less than a node because it is a
reference, not work: counted alike, two calls of `ripple` (`examples/reifying/glsl/`),
4 nodes over 2 holes, would not lower the size.

| Gain | Cost |
|---|---|
| functions in the output, identical under every refactor in R | the functions are not the author's, so emitted GLSL is harder to read; the dump maps them back |
| bounded output size: inlining a call tree duplicates bodies, exponentially in the worst case, and outlining shares them again | stability is global: adding one use of a shape anywhere can change which rows are chosen everywhere, on a real edit, never on a refactor in R |
| a helper called over different arguments (`step(input.a)` and `step(input.b)`) is one row | per pass, O(D × m log m) for the keys of m nodes, plus the walks of the groups (below) |

K, D, the gain, the selection order and the hole numbering are part of the
language version, like R.

`src/reify/views.zig` (`outlineSelect`) builds the rule (M9 and V3b of the
plan). K is 4 (`views.outline_min_size`) and D is 3 (`views.outline_key_depth`).
The rule above leaves these points open, and the build reads them as the
table says:

| Point | Reading |
|---|---|
| literals | a literal is not a stopping point, and it does not count in the size. Literals with one value at every place are copied into the row. Literals that differ are a hole, whose argument is the literal: a literal cannot crash, so the hole is always allowed, and the row keeps the node that reads it. Stopping above the literal would cost the same argument and lose that node. So `x * 3` and `x * 4` generalize to `x * h0` |
| which cones a row can be | a cone with one output, no `Return` to the row, no `Continue` or `Break` of a loop outside it, no `Jump` to a join outside it, and no `Call` or `Closure` of its own recursive component. Other nodes are not places |
| keys | a key is a hash, so two keys can collide. A collision only puts places in one group; the walk compares values, so it never treats two computations as one |
| overlap | a place overlaps a taken occurrence when their images share a node. A place whose root is a value of a hole of another, or the other way round, does not overlap it: the outer call reads the inner one |
| the end of a pass | the made rows and their callers are finalized again (3.8), and the next pass reads the result. The pass stops when it takes nothing. A debug check asserts that each pass lowers 3 × nodes + call arguments (`views.SiteSize`) |
| cost | the keys are O(m × a^D) for nodes of at most a arguments, the sort O(D × m log m). A walk of a group of c places is O(c × w) for w tuples, run once per rule 4 round and once per change of the group's places; a round adds at least one hole. Selection evaluates a candidate again after each take that predates its evaluation |

### 5.4 Rebuilding expression trees

"All in defs" is the right shape for the normal form, and the wrong one for a
translator that emits nested expressions. `Code.Graph.to_tree` undoes the defs
under a fixed rule, so the tree is as canonical as the graph:

| Node | In the tree |
|---|---|
| literal, parameter | substituted at every use |
| used once, in the same region | substituted at the use |
| used once, in a nested switch arm or `And`/`Or` operand | substituted at the use: it runs in fewer cases, which C2 allows |
| used once, inside a loop body or a lambda | stays a def outside, because substituting it would repeat its work on every turn |
| used more than once | stays a def, so shared work stays shared |

A translator that wants no defs at all can substitute shared ones itself. The
normal form never duplicates work on its own.

---

## 6. Errors without names

A translator refuses a node, not a line:

```roc
code.refuse_at({ row: row.id, node: index }, "GLSL 330 has no `Str.concat`")
```

`refuse_at` lowers to a crash that carries the site key, the row and the node.
When the compiler evaluates a top-level value and meets it, the compiler looks
the node up in the provenance table and reports each region it came from, with
the call path. When a program meets it at run time, it is an ordinary crash
with the message. `test/cli/StagedRefusal.roc` gives this report:

```
── ✗ translation refused ────────────────────── test/cli/StagedRefusal.roc:25:12

A translator refused code that this expression built.

step = |x| x * 3
           ^^^^^

The translated code reached it through these calls:

    step(x) (test/cli/StagedRefusal.roc:28:14)

The translator gave this reason:

    this target has no multiplication
```

| Source of the node | The report highlights | The report names |
|---|---|---|
| in this module | the source | the calls it was inlined through |
| in another module | the innermost call in this module on its path, or the top-level value | the module, line and column, and the calls |
| none: the translator named a node that the graph does not have | the top-level value | that the node is not in the graph |

The translator author debugs emitted `n7` names with a compiler dump that the
translator cannot read. `roc reify --dump main.roc:40` prints the normal form
with source names and regions as comments:

```
row f0 (p0 : { time : F32, uv : { x : F32, y : F32 } }) -> F32
  n0 = Lit 0.5 : F32                  # base, half        main.roc:43, 44
  n1 = Field uv p0                    # uv                main.roc:41
  ...
```

This settles the proposal's open question on refusals as diagnostics
(`roc-reify-proposal.md:1164-1172`): `refuse_at` is the method whose refusal the
compiler reports at a region, and the region comes from the compiler, not the
translator.

---

## 7. R, the safe refactors

Every row is an edit that preserves meaning in Roc under C2. "A" means the normal form is identical.

| Refactor | `graph` | `inline`, `outline` | Absorbed by |
|---|---|---|---|
| rename a local, parameter or pattern binder | A | A | N2 |
| reformat, comment, move code within a file | A | A | regions only in N10 |
| reorder independent bindings | A | A | N4, N9, C2 |
| bind a value once, or write the expression twice | A | A | N5 |
| bind a value once before a `match` or `if` whose every arm reads it, or compute it in every arm | A | A | N5 |
| drop a binding nothing reads | A | A | N6, C2 |
| move a binding into or out of a branch | A | A | N5, C2 |
| hoist loop-invariant speculatable work out of a loop or lambda | A | A | N5 |
| destructure a record or tuple, or read its fields | A | A | N1 |
| `and`/`or` and the `if` they mean; `?`, `??`, early `return` and the `match` they mean | A | A | N1, N7, N13 |
| group `a and b and c` either way; nested `if`s or one condition with `and`/`or` | A | A | N15, N7 |
| `if a Bool.False else b` or `!a and b`; `if a b else Bool.True` or `!a or b` | A | A | N13 |
| `a >= b` or `!(a < b)` over integers, and an `if` on either with its branches swapped | A | A | N1, N13 |
| `x.f(y)`, `f(x, y)`, `x \|> f(y)`; an operator and its method | A | A | N1 |
| `var` with reassignment, or a chain of distinct bindings | A | A | N3 |
| reorder `var` declarations | A | A | N3, N9 |
| reorder record literal fields | A | A | N9 |
| reorder non-overlapping `match` arms | A | A | N7, phase 1 for flat matches, phase 2 in general |
| add or remove an annotation that does not change solved types | A | A | types come from the checker |
| literal spelling: `1_000`, `1000`, `0x3E8` | A | A | N1 |
| rename a helper; move it to another module in the package; reorder top-level definitions | A | A | N8 |
| any refactor inside a function in the site's cut | A | A | 3.8: the function is a primitive by name |
| turn a local closure into a top-level helper, or back | A | A | N8 |
| reorder a private helper's parameters; drop an unused one | A | A | N8 |
| `List.map(xs, \|x\| f(x))` and `List.map(xs, f)` | A | A | N8, eta |
| make a helper generic, or specialize it by hand | A | A | N8 |
| pass the same known function from two call sites | A | A | N8 |
| `{ ..r, y: 3 }` or the full record | A | A | N1 |
| omit a defaulted field, or write its default | A | A | N1 |
| add or remove `expect` inside a body | A | A | N1 |
| `for` or `while`; `while` with a counter or `for` over `a..<b`; an index loop or `for` over a list | A | A | N11, N13 |
| `for x in xs` or `for x in xs.iter()` over a `List` | A | A | N11 |
| `continue` in each branch of an `if`, or one after it; `if c { break }` followed by the rest of the body, or the rest in its `else` | A | A | N11, T2, T3 |
| a tail-recursive helper or a loop | A | A | N12, N11 |
| `return x` as the last statement, or `x` | A | A | T6 |
| a helper that returns a tag or a `Try`, matched or unwrapped with `?` by its caller, or the helper's tests written in place | A for a helper with one call site, B otherwise | A | 5.1, case-of-case (3.13) |
| reject a literal in its conversion with an `if`, a `match`, a chain of tests or a helper's `Try`, at any depth | A | A | N13w (3.13), C2 |
| call a function chosen by an `if` or read from a record literal, or call each function directly | A | A | `Apply` (3.8) |
| drop a loop variable nothing reads, or one that never changes | A | A | N11 |
| build a record, tuple or tag and read it back, or use the parts directly | A | A | N13 |
| match on a value whose tag is known, or take the arm | A | A | N13 |
| repeat a test a dominating branch already made, or drop it | A | A | N13 |
| name a constant computed from literals, or write its value | A | A | N13 |
| wrap a value in a nominal and unwrap it, or use it directly | A | A | N13 |
| pass a private helper `a, b`, `{ a, b }` or `(a, b)`; one record `var` or one `var` per field | A | A | N14 |
| regroup `Str.concat`, `List.concat`, wrapping arithmetic, bitwise chains; add or drop `""` | A | A | N15 |
| `a + 1` or `1 + a`; `x == y` or `y == x` over the root's parameters, for builtin integers and `Str` | A | A | N15c |
| regroup a `plus` chain whose operands' intervals prove no grouping overflows | A | A | N13u, N15a |
| `while $i <= n` or `for i in a..=n`, when `n`'s interval is below the type's highest value | A | A | N13u, N11l |
| a loop controlled by a `$done` flag, or the same loop with `break` where the flag is set | A | A | N11n |
| a second counter `$j` from `j0`, stepped by 1 with the index of `for i in 0..<n`, or `i + j0` computed in the body | A | A | N11o |
| a `for` loop that appends, or `List.map`, `List.keep_if`; `List.fold` or its loop; two `map`s or one | A | A | N16, only with layer L |
| `x.len() > 0` or `!x.is_empty()`; `x.len() == 0` or `x.is_empty()` | A | A | N16f, only with layer L |
| extract a helper used from one place, or inline it | A | A | 5.1 |
| extract a helper that replaces two or more copies over different arguments, or inline it | B | A | 5.1, 5.3 |
| reorder the two constants of the remark | A | A | folded literals are `Lit` nodes; N4, N9 |

### 7.1 Outside R, and why

| Edit | Why it stays out | What happens |
|---|---|---|
| move work that is not speculatable across a loop boundary | changes how often it runs, and whether it runs for zero turns | output changes |
| rename a record field, tag or nominal type | interface, in Roc already | output changes; a translator that recognized the name may refuse |
| `x * 2` to `x + x` for floats; reassociate `(a + b) + c` | float rounding; regrouped integer sums overflow where the written ones do not (3.15), unless N13u proves they do not | output changes |
| `x.len() > 0` to `!x.is_empty()`, without layer L | different builtins; equal by a theorem about their bodies, which layer L declares (N16f) | a translator that knows one may refuse the other |
| a `for` loop to a builtin, without layer L | the equation is a law about the builtin (3.16) | output changes; may refuse |
| general recursion to a loop, or mutual tail recursion | different structure (3.12) | output changes; may refuse |
| `while $i <= n` to `for i in a..=n`, when `n`'s interval reaches the type's highest value | differ in Roc when `n` is the type's highest value (3.11) | output changes |
| a second counter stepped by other than 1, or from a start whose difference N13u does not prove | the product or the difference can overflow where the slot does not (3.11) | output changes |
| a `$done` flag set in a way no dominating test decides | the leading test is not decided on that edge (3.11) | output changes; the flag loop stays a general `Loop` |
| reorder overlapping guarded arms | meaning | output changes |
| upgrade a dependency whose function outside the cut changed its normal form; rename a function in the cut | not a refactor of your code | output changes, or the build stops at the site, at the upgrade (3.8) |

Every row fails loudly at `roc build` or changes the output of an edit that
changed what the code computes. None depends on spelling or position.

### 7.2 Deliberately not normalized

Some equations hold in Roc, or nearly, and are still left out, because
absorbing them costs more than the refactor they would absorb:

| Equation | Why it is left out |
|---|---|
| operands of commutative operations, `a + b` and `b + a`, beyond the leaf pairs of N15c | sorting operands by digest makes N9's numbering shift under unrelated real edits, which costs every translator stability to absorb one refactor that authors of reified code rarely make |
| float reassociation, `x * 2` and `x + x` | not true in Roc |
| equal operands of a chain merged or cancelled, `x & x` and `x`, `x ^ x` and `0` | with operand order kept, it is not confluent with N15a's flattening (3.15); a canonical operand order would make it so, which the first row leaves out |
| a canonical form for boolean formulas, such as a reduced BDD | canonical only for a fixed variable order, which would have to come from the walk, so it adds no invariance N7 and N13 lack |
| merging identical work in some sibling branches but not all | it places work where some branch did not evaluate it, which is speculation. Work in every arm is merged (3.5), because binding it once before the switch is a refactor in R |
| a branch that always crashes, treated as unreachable | C2 would allow it, but the author wrote the `crash`, and an interpreter target reports it. The crash of a rejected literal is the compiler's, and N13w decides it (3.13) |
| inlining a builtin's body | a builtin is a primitive; its body is not API, and a translator recognizes it by identity |
| loop unrolling, loop fusion outside layer L | optimizations, not refactors anyone makes to reified code. The exception is a loop over a list of known length, which N17g unrolls, because a loop over `[r, g, b]` and three statements is a refactor authors make |
| outlining in the `graph` view | it would replace the author's shared helpers, which is what `outline` is for |
| mutual tail recursion as one `Loop` with a dispatch slot | the slot's tags are the compiler's, so an author's state loop over its own tags would not meet it (3.12) |
| a callee's set of result tags, read by its callers | it removes only arms the callee never returns; a helper matched by its caller meets its tests in place only by case-of-case in `inline` (5.1), so no refactor moves into R |
| a call of a row whose result is always parameter `k`, replaced by argument `k` | a row that can crash would lose a `crash` its author wrote; a speculatable one is already reduced to the parameter, so only calls of an identity row would change |
| `OptField` of a `Record` node, which names the fields it sets | the answer is `Ok` of the field or `Err(MissingField)`, but the result has to be built as a `Try` of a type the table's `Tmpl` has no template for; the description keeps the read, and a translator that wants the answer reads the `Record`'s field names |

---

## 8. The remark, point by point

| The remark says | The normal form |
|---|---|
| "no such thing as a safe refactor" | R is published, each entry names the step that absorbs it, and a fuzzer checks it on every build of the compiler (section 9) |
| "any change to any AST node" | a translator cannot see an AST node. It sees a graph whose nodes are operations, and an AST change that leaves the operations alone leaves the graph alone |
| "even just reordering two unrelated constants" | constants fold to `Lit` nodes, and unrelated nodes have no order in the graph. N9 numbers them by what reads them, so the reorder yields an equal value |
| "could break the entire program" | within a package, what remains in section 7.1 changes operations and breaks at build time next to the edit. Across packages, a translation changes only at an upgrade the user makes, and a break names the site (3.8) |

What the design concedes: the `graph` view keeps shared helper boundaries
visible (tier B), and `outline` exists for a translator that cannot accept
that. C2
promises Roc's result only where Roc does not crash, and a dependency upgrade
can change a translation if a body the site reaches changed its normal form,
or if a function in the cut was renamed. A compiler upgrade
that changes a rule changes normal forms too; the version number of section 10
says when. Each of these is
named, bounded, and a choice the language states rather than an accident of
the implementation.

---

## 9. Soundness and testing

Two properties, tested separately, both with small typed constructs composed at
random, as `AGENTS.md` requires of fuzzers:

| Property | Statement | Test |
|---|---|---|
| sound | C2: where the body does not crash, the normal form gives its result; where the body does not crash, the normal form does not crash either | an evaluator for the normal form, run against the Roc interpreter on random inputs to random bodies; where Roc crashes, anything is allowed |
| absorbs R | for every refactor in R, the normal form is equal | random bodies, random refactors drawn from R, applied as source rewrites; assert equal `graph` (or equal `inline` for tier B), and equal digests |
| not too coarse | edits outside R change the normal form when they change meaning | the soundness test covers it: a merge of inequivalent bodies is a soundness failure |
| confluent | the simplify phase reaches one fixpoint from any starting point | the overlapping pairs of the rule table, each normalized with either rule first; every rule order on small graphs with shared nodes; the exploration of `roc-reify-rule-derivation.md`, which groups small terms by their values and requires every proved-equal pair to share a normal form; and the R test, which starts N13 to N16 from different shapes of one computation. A failure names the two rules that did not join (3.0) |
| laws hold | every law in layer L is true of the builtin's implementation | the soundness test with the law's two sides as the two bodies, on random inputs |
| views agree | `graph`, `inline` and `outline` of one body mean the same | the evaluator run on all three |

Every step in section 3 is defined by a rule, and every tie is broken by a
total, source-independent order, so the steps involve no heuristics, and the
fuzzer can compare values with plain equality.

---

## 10. Where it runs

| Question | Answer |
|---|---|
| input | checked CIR, read by the walk in `src/check/code_reifier.zig`, which already resolves static dispatch, specialization and folded constants |
| output | the normal form, plus the provenance table, inside the opaque `Code` value |
| `Code.Ir` | removed. The walk builds the normal form directly (`roc-reify-normalization-plan.md` 1.3), which also removes the versioning burden of proposal 7.6: the stable object is the normal form, which does not grow when Roc adds sugar |
| language | Zig, in a module the walk builds into. It consumes the checker's explicit data and reconstructs nothing |
| cost | N1 to N6, N8 and N9 are linear up to hashing. N7 is as expensive as match compilation, exponential only in pathological patterns. The component canonicalization of 3.8 is bisimulation, near linear. The simplify phase is a rebuild repeated to a fixpoint per component, each round linear in the regions that changed, with the number of rounds bounded by the measure of 3.0. Slot merging in N11 is optimistic value numbering, near linear. `inline` can grow exponentially with call depth; `outline` is O(n log n) per pass over that size |
| `is_eq` and `to_hash` on `Code` | over the normal form only, which delivers rule 6 of the proposal (`roc-reify-proposal.md:115-119`). A `Code` value also carries the key of the site that produced it, so `refuse_at` reports that site's regions even when rows are shared with other sites. Equality must ignore the key, so both are written by hand in `Builtin.roc` rather than derived, and provenance is keyed by site and node |
| versioning | R, C2 and the speculatable list are part of the language version. Adding an equation to R changes normal forms, so it ships like any semantics change. A `Code` value carries the normal-form version, `Code.version`, so a translator can put it in a cache key, and golden files change exactly when it does |

### 10.1 Translator API sketch

```roc
Code(_fn) :: { ... }.{
	graph : Code(fn) -> Graph
	refuse_at : Code(fn), NodeRef, Str -> a   # reports at the regions of this value's site (section 6)
	version : Code(fn) -> U32                       # the normal-form version

	# The site's declared type selects the view (roc-reify-normalization-plan.md 1.5)
	Inlined(_fn) :: { ... }.{
		inline : Inlined(fn) -> Graph
		refuse_at : Inlined(fn), NodeRef, Str -> a   # as Code.refuse_at, in the inline view
		inline_digest : Inlined(fn), NodeRef -> Digest   # a node's content digest in inline
	}
	Outlined(_fn) :: { ... }.{
		outline : Outlined(fn) -> Graph
	}

	Graph :: { ... }.{
		rows : Graph -> List(Row)               # canonical order, root first
		row : Graph, RowId -> Row
		inputs : Graph -> List({ name : Str, ty : Ty })   # root parameter fields, by name
		slots : Graph -> List(Ty)                         # the root's input slots, in slot order (3.18)
		iteration : Graph, NodeRef -> Iteration   # the NodeRef names a loop node; read off the node
		to_tree : Graph, RowId -> Tree
	}

	Row := { id : RowId, params : List(Ty), body : Region, recursive : Bool, digest : Digest }

	NodeRef : { row : RowId, node : U32 }   # a node by its row and its index in that row's nodes

	Region := { params : List(Ty), nodes : List(Node), end : End }   # params only for loop bodies and joins

	End := [
		Value(List(Val)),           # a row body's result, a value switch's outputs, an And or Or operand
		Jump({ join : U32, args : List(Val) }),   # to a join of the enclosing exiting switch
		Return(Val),                # ends the row, from any region
		Continue(List(Val)),        # loop bodies only
		Break(Val),                 # loop bodies only
		Branch(U32),                # ends in this exiting Switch node (3.11)
	]

	Val := [
		Param(U32),
		Node(U32),
		Out({ node : U32, k : U32 }),        # output k of a Switch node
		Arg({ owner : U32, k : U32 }),       # param k of the loop body or join the node owner holds; in ForRange, param 0 is the index; in ForList, param 0 is the element and param 1 the index
		Input(U32),                          # input slot k of the root (3.18)
	]

	Node := { op : Op, args : List(Val), ty : Ty, speculatable : Bool }

	Op := [
		Lit(Lit),
		Prim({ owner : Str, method : Str }),   # Num.F32 and sin; Glsl.Vec3 and scale
		Call(RowId),
		Closure(RowId),             # args are the captured values
		Record(List(Str)),          # the names of the fields the node sets, in the type's order
		Tuple,
		List,
		Tag(Str),
		Wrap(Str),                  # into the named nominal type
		Unwrap,
		Field(Str),
		Index(U64),
		Payload(Str, U64),
		Elem,                       # a list element under a proven bound: args are the list and the index
		OptField(Str),
		Switch({ at : Val, arms : List({ key : Key, region : Region }), joins : List(Region), outputs : List(Ty) }),   # joins only in an exiting switch
		And({ first : Val, rest : List(Region) }),     # each region runs only if every earlier operand is True
		Or({ first : Val, rest : List(Region) }),      # each region runs only if every earlier operand is False
		ForRange({ start : Val, end : Val, inclusive : Bool, slots : List(Val), body : Region }),
		ForList({ list : Val, slots : List(Val), body : Region }),
		Loop({ slots : List(Val), body : Region }),    # slots hold initial values
		Lambda(Region),             # only in inline and outline, where a Closure of a non-recursive row is inlined; its params are the lambda's
		Crash,
		Derived(Str, Ty),
	]

	Key := [Tag(Str), Lit(Lit), Len(U64), AtLeast(U64), Default]

	Iteration := [
		OverList({ list : Val, item : [Read(Val), Unread], index : [Read(Val), Unread], exits_early : Bool }),
		OverRange({ start : Val, end : Val, inclusive : Bool, index : Val, exits_early : Bool }),
		General,
	]
}
```

A region ends in an `End`, not in a value, so control never travels as a tag:
`Continue` and `Break` end paths of a loop body, and `Return` any path. A
switch with an arm that ends in one is an exiting switch: it ends its region,
and the code after it is a join its other arms jump to (3.11). A `while`
condition is the switch the body's `Branch` ends in. `Arg` names the
parameter's owner, so a nested loop or join never shadows an outer one. `Prim` carries n
arguments for a chain N15 flattened. `Prim` names its owner and method apart,
so a translator's table is keyed by method and reads the type from the node;
the rest of this document writes `Prim("Num.F32.sin")` for
`Prim({ owner: "Num.F32", method: "sin" })`. A translator for a target
without short-circuit evaluation, such as SQL's `AND`, reads `speculatable` on
the operands to decide whether it may evaluate them eagerly.

---

## 11. Worked examples

A shader, then the same shader after several refactors from R.

```roc
wobble : { time : F32, uv : { x : F32, y : F32 } } -> F32
wobble = |{ uv, time }| {
	wave = Num.F32.sin(uv.x * 10.0 + time)
	base = 0.5
	base + wave * 0.5
}
```

```roc
wobble = |input| {
	half = 0.5
	ripple = phase(input).sin()
	half + ripple * half
}

phase = |input| input.uv.x * 10.0 + input.time
```

Renamed locals, a destructure turned into field reads, two bindings reordered,
a method call for a function call, one literal named and reused, and a helper
extracted. `Code.inline` gives, for both:

```
row f0 (p0 : { time : F32, uv : { x : F32, y : F32 } }) -> F32
  n0 = Lit 0.5 : F32
  n1 = Field uv       p0
  n2 = Field x        n1
  n3 = Lit 10.0 : F32
  n4 = Prim Num.F32.times  n2 n3
  n5 = Field time     p0
  n6 = Prim Num.F32.plus   n4 n5
  n7 = Prim Num.F32.sin    n6
  n8 = Prim Num.F32.times  n7 n0
  n9 = Prim Num.F32.plus   n0 n8
  result n9
```

`n0` is first, because the result's first operand is `0.5` in both bodies:
`base` in one, `half` in the other. The `0.5` literal the first body writes a
second time is the same node, by value numbering, and `to_tree` gives the one
GLSL expression
`0.5 + sin(uv.x * 10.0 + time) * 0.5` for both bodies.

`Code.graph` gives the same for both: `phase` has one call site, so the view
inlines it. `Code.outline` gives the same too, because no shape occurs twice.

### 11.1 Three loops

```roc
sum_to : U64 -> U64
sum_to = |n| {
	$total = 0
	for i in 0..<n {
		$total = $total + i
	}
	$total
}
```

```roc
sum_to = |n| {
	$i = 0
	$total = 0
	while $i < n {
		$total = $total + $i
		$i = $i + 1
	}
	$total
}
```

```roc
sum_to = |n| go(0, 0, n)

go : U64, U64, U64 -> U64
go = |acc, i, n| if i < n go(acc + i, i + 1, n) else acc
```

All three sources give the same normal form, in every view. N12 runs before
any view is built (3.0), so `go` is already a non-recursive row: `inline`
inlines it, `graph` inlines it because it has one call site, and `outline`
finds no shape that repeats. A tail-recursive helper called from two places
would stay a row in `graph` (tier B), and `outline` would make its repeated
loop a row. Here the normal form is:

```
row f0 (p0 : U64) -> U64
  n0 = Lit 0 : U64
  n1 = ForRange n0 p0 exclusive slots [n0]     # slot0 is the index, slot1 the total
         t0 = Prim Num.U64.plus slot1 slot0
         Continue t0
  result n1
```

| Difference in the source | Removed by |
|---|---|
| `for` over a range, `while`, tail recursion | N11, N12 |
| the `while` and recursive versions test and step the counter by hand | N11 raising: a slot starting at `0`, tested by `is_lt` against `p0` and continued with `plus(slot, 1)` is the index of a `ForRange` |
| `$i` and `$total` declared in either order; `acc` before `i` | N3, N11: the counter becomes the index, whichever position its slot had |
| `n` passed unchanged to every call of `go` | N11: an invariant slot is its initial value, `p0` |
| `go` a separate row | N12 makes it a loop, so it is no longer recursive, and its one call site inlines it |
| the recursive version ends with `acc` through a return | N11 exit rules: `Return` becomes `Break`, and a `Break` of the other slots on the failed test is the normal end of the range |
| `Lit 1` written inside the loop | N11 raising: the step is part of `ForRange` |

The remaining `plus` is not speculatable, because a sum can overflow `U64`,
so the loop is not speculatable either and stays where every source put it.
The counter's `plus` is gone: under `slot0 < p0` it cannot overflow.
`iteration` gives `OverRange({ start: n0, end: p0, inclusive: False, ... })`
for all three.

---

## 12. Open questions

| Question | Options |
|---|---|
| Is C2 acceptable to the language? | accept it for reified bodies only, which is enough; or reject it, and the strict variant returns: a `may_fail` flag on every builtin, obligations for dead nodes that can fail, failing nodes pinned to their region, and moving or dropping them leaves R |
| Which builtins are on the speculatable list? | the ones in 1.1. Leaving a builtin off is always sound; it only keeps that builtin from being hoisted out of loops |
| Should layer L ship with the first version? | it is separable: N1 to N15 stand without it. Shipping it later is a versioned change of R, like any law added after |
| Which laws belong in L? | the five of 3.16 are the ones a loop-to-builtin refactor needs, and N16f adds `len() > 0` and `len() == 0` against `is_empty()`. Further candidates are theorems about builtins that the library would have to state and test |
| Commutative operators? | only leaf pairs, by N15c: a literal last, the root's parameters in order. The rest is left out (7.2). Revisit only if real translators show that authors reorder other operands |
| What is K in `outline`? | decided for now: K = 4, measured on the examples (table below). K must be 3 or more, so that a pass lowers the site's measure. The examples do not tell 3 and 4 apart, and K = 5 loses the one row of the GLSL example. The measurement of M9 found that a cone takes in every argument only it reads, so `step(input.a)` and `step(input.b)` had two shapes. V3b answers it by anti-unification (5.3, rules 3 and 4): the differing arguments are holes, so both are one row, and the GLSL shader's two calls of `ripple` are one row. Measure again when a translator reads `outline` |
| Should `graph` inline single-use rows? | yes in this design, because it moves the most common helper extraction into tier A. The price is that a GLSL translator reading `graph` never emits a function the author called once |
| Do translators need names for emitted identifiers? | no in this design: the dump and provenance cover debugging. A name exposed for emission becomes observable again |
| Should the rules be derived rather than accumulated? | yes: the gate of `roc-reify-rule-derivation.md` section 6 passed on 2026-09-27. That document defines an offline tool, `zig build reify-rules`, that finds unjoined critical pairs and equal small terms that normalize apart, proves them in a most-defined semantics in which every rule is an equation, and writes the first-order rules as table rows. After the gate, a tier F rule enters the table through the tool, and a hand-written tier F row, such as N15a's rows over operand runs, states its reason |
| How does a translator declare its cut? | decided: a well-known associated item `code_primitives` on the nominal type that owns the function with the `Code(f)` parameter, found through that type as `iter` and `to_inspect` are. It is public, like every well-known name, and it tells a translator's users which functions it reads by name. It is a direct reference to one top-level function, or a tuple of such references; anything else, and a function listed twice, is a compile error at the item. A type without it has an empty cut. The checker resolves it and records the cut in the checked artifact, as it records `IteratorProcedureId`; the reifier reads the checked expression, not an evaluated value. The cut is per type: two translators with different cuts are two types. Rejected: a private module constant read by name, which no Roc mechanism is like; a second `Code` type parameter with a `Code.prim` intrinsic (new surface), a package header entry (one cut per package, which `Glsl` and `Interp` in one package cannot share), and a cut passed to a `Code` function at run time (the normalizer would have to run in every backend, as plan 1.5 rejects for views) |
| Where does the `graph` view stop being worth it? | if no translator ends up reading it, drop it and keep only `inline`; the normal form's definition does not change |

K was measured with `ROC_REIFY_OUTLINE_STATS=3,4,5,6,8,12` (a Debug compiler
only), which reifies each site in `outline` at each K and prints its size,
over `roc check` of each `main.roc` and of each fixture. "Nodes" counts the
nodes of all rows of all sites, literals not counted. "Rows" counts the rows
that `outline` made. The measurement is of normal form 15 (V3b).

| Source | Sites | Nodes in `inline` | K = 3 | K = 4 | K = 5 | K = 6, 8, 12 |
|---|---|---|---|---|---|---|
| `examples/reifying/glsl/` | 8 | 165 | 163, 1 row | 163, 1 row | 165, 0 rows | 165, 0 rows |
| `examples/reifying/sql/` | 42 | 141 | 141, 0 rows | 141, 0 rows | 141, 0 rows | 141, 0 rows |
| `examples/reifying/dbsp/` | 22 | 107 | 107, 0 rows | 107, 0 rows | 107, 0 rows | 107, 0 rows |
| `examples/reifying/hello/` | 3 | 6 | 6, 0 rows | 6, 0 rows | 6, 0 rows | 6, 0 rows |
| `test/cli/Staged*.roc` | 153 | 584 | 569, 5 rows | 569, 5 rows | 569, 5 rows | 584, 0 rows |

The GLSL row is `ripple`: the shader `rippled` calls it twice over two field
reads, `frag.fragTexCoord.y` and `frag.fragTexCoord.x`, and `settings.time * 2.0`
is one value at both places. The row has 4 nodes and 2 holes, the field read
and the shared product, and the site falls from 16 nodes to 14. No other site
of the examples repeats a computation of 3 nodes or more. The five rows of the
fixtures are all in `test/cli/StagedOutlinedView.roc`, as in M9. The
`step(input.a)` and `step(input.b)` pair of the M9 measurement is not in an
example (the DBSP example calls `step` at run time, not at a `Code` site);
`L3 V3b` in `src/compile/test/code_reifier_test.zig` holds it, and it is one
row.

---

## Sources

- Mitchell Wand, "The Theory of Fexprs is Trivial", Lisp and Symbolic Computation 10(3), 1998
- Nico Reissmann, Jan Christian Meyer, Helge Bahmann, Magnus Själander, "RVSDG: An Intermediate Representation for Optimizing Compilers", ACM TECS 19(6), 2020
- Luc Maranget, "Compiling Pattern Matching to Good Decision Trees", ML Workshop, 2008
- Bowen Alpern, Mark Wegman, Kenneth Zadeck, "Detecting Equality of Variables in Programs", POPL 1988 (value numbering)
- Donald Knuth, Peter Bendix, "Simple Word Problems in Universal Algebras", 1970 (completion of a rewrite system)
- Detlef Plump, "Term Graph Rewriting", in Handbook of Graph Grammars and Computing by Graph Transformation, volume 2, 1999 (critical pairs over graphs with sharing)
- Luke Maurer, Paul Downen, Zena Ariola, Simon Peyton Jones, "Compiling without Continuations", PLDI 2017 (join points)
- Cliff Click, "Global Code Motion / Global Value Numbering", PLDI 1995 (placement)
- Moses Charikar et al., "The Smallest Grammar Problem", IEEE Transactions on Information Theory 51(7), 2005
- Unison, content-addressed definitions and hashing of mutually recursive cycles: [unison-lang.org, the big idea](https://www.unison-lang.org/docs/the-big-idea/)
- Dhall semantic integrity checks: [dhall-lang standard](https://github.com/dhall-lang/dhall-lang/blob/master/standard/README.md)
