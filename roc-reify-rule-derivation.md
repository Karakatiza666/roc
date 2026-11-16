# Normalization rules: derived, not accumulated

The rules of `roc-reify-normal-form.md` grew by counterexample: a review found
two spellings that did not meet, or two rules that did not join, and added a
rule. This document replaces that with one offline tool, `zig build
reify-rules`, that finds the missing rules itself, proves them, and writes them
as rows of the plan's rule table (I13). A person reviews the rows it writes.

The tool is built in three phases, then judged at a gate (section 6) after
three iterations. The gate decides from measured numbers whether the tool
becomes how rules are added, or shrinks to a critical-pair checker in CI while
rules stay hand-written. Neither outcome leaves open research.

| Question | Answer | Section |
|---|---|---|
| What does the tool do? | finds unjoined critical pairs of the rule table, and pairs of small terms that are equal but normalize apart; proves each pair; generalizes it; writes a table row, its tests, or a ledger entry | 3 |
| What makes a rule correct? | it is an equation in the IR's most-defined semantics, it decreases the measure of normal-form 3.0, and it passes the speculation check | 2 |
| What is outside the tool? | rules that read context (dominating facts, placement) or instantiate binders (loops, joins). The tool tests them and files failures against them; it does not write them | 2.3 |
| What does it depend on? | the IR, the builder, the rule table and `eval.zig` of the plan, and the `z3` binary. Nothing else | 4 |
| When is it built? | D0 with the plan's M0, D1 and D2 with M4, gate at the end of M4; D5 (k = 6) and D6 (k = 7) as the plan's M15 and M16, in its core | 5 |
| How do we know the strategy works? | a gate after three iterations with eight measured criteria, among them rediscovery of knocked-out rules and of the four critical pairs the reviews found by hand | 6 |
| Why does it stop? | per signature and size bound the candidate space is finite and each admitted rule removes at least one candidate; k and the signature are fixed per milestone | 7 |

---

## 1. Method, and what it takes from where

The method is Knuth-Bendix completion run by our own normalizer, plus theory
exploration in the style of Ruler and QuickSpec, validated as Alive and Optgen
do. The choices below keep the tool small and inside the repository.

| Part | Taken from | Used as | Not used, and why |
|---|---|---|---|
| critical pairs, orientation by a reduction order | Knuth and Bendix (1970); Bachmair, Dershowitz, Plaisted (1989) | step 1 of the loop, over the rule table's own patterns | external completion tools (MædMax, KBCV, Ctrl): they need a translation of the table into their formats and back, and their results would still have to become table rows. Revisit only if step 1 diverges in a way the report cannot show |
| enumerate small terms, group by values on fixed inputs | Ruler (Nandi et al., 2021), Enumo (Pal et al., 2023), QuickSpec (Smallbone et al., 2017) | step 2, over irreducible terms only | equality saturation (egg, egglog) as the engine: fingerprints by evaluation find equations that no rule states, which saturation cannot |
| prove, with witnesses | Optgen (Buchwald, 2015), Alive2 (Lopes et al., 2021) | step 3: exhaustive at 8-bit width, then `z3` over 64-bit vectors and floats | Alive2 itself: it validates LLVM IR, not this IR |
| generalize a proved pair | anti-unification (Plotkin, Reynolds, 1970); Hydra (Mukherjee, Regehr, 2024) | step 4: literals and subterms lifted to pattern variables while the proof still holds | synthesized side conditions beyond the fixed condition language of 3.4 |
| complete up to a bound | Optgen | the guarantee of section 7 | |
| proofs of termination and confluence | TTT2, CSI, CeTA | not in the first version | the measure of normal-form 3.0 already proves termination; certificates are a later option if the gate passes and a reviewer asks for them |
| where canonicity must stop | Lindley (2007), Scherer (2017) on sums; Plump (1994) on sharing | the scope limits of 2.3 and section 8 | |

Canonicity is always relative to a stated theory, because program equivalence
is undecidable. Here the theory is equality in the most-defined semantics of
2.1, over the signature of the current milestone, up to term size k.

---

## 2. The formal core

### 2.1 Semantics: every rule is an equation

Completion is sound only for equations. Some rules make a body more defined:
dropping a dead `n // d` removes a crash. So the IR gets a semantics in which
those rules are equations, and the only refinement stays in the walk:

| Layer | Semantics | Relation |
|---|---|---|
| Roc body | strict: every binding runs, a crash ends the program | |
| the walk | builds the IR | the one refinement: the IR equals the body wherever the body does not crash. Tested by the plan's L5 differential |
| the IR | most-defined: a constructor does not force its components until one is read; a `Switch`, `And` or `Or` whose result does not depend on an undecided test has that result (Plotkin's parallel operators, 1977); a builtin is strict in its arguments; a crash is ⊥ | every rule is an equation here |
| placement and emission | strict, in the regions N5b chose | agree with the IR because N5b hoists only speculatable nodes |

`eval.zig` (plan I6) gains a `most_defined` mode that implements this row. Its
result type is a value or ⊥. A `Switch` with a ⊥ scrutinee evaluates every arm
and returns their common value if all agree and none is ⊥, else ⊥. `And` and
`Or` return `False` and `True` as soon as any operand decides them. `Field`,
`Payload` and `Index` evaluate only the component read. Only the tool and its
tests use the mode.

A pattern variable matches a node, and a node can crash, so every variable
ranges over the values of its sort and ⊥. An equation holds only if it holds
at ⊥ too: `minus(x, x) = 0` fails at `x = ⊥`, and is admitted, if at all, only
under the condition that `x` is speculatable.

### 2.2 Correct rule, preferred direction

A rule `l -> r [φ]` enters the table only when all three checks pass:

| Check | Definition | Implemented by |
|---|---|---|
| equation | `l = r` under φ in the most-defined semantics, for every input | step 3 of the loop |
| orientation | `l ≻ r`, where ≻ compares the components of the measure of normal-form 3.0 in order, and nothing after them: the driver checks that measure after every round, so a rule only a path order would rank is not oriented. Each component is counted on the term the pattern unfolds to, not on the graph, and compares by its count only when no variable occurs more often in `r` than in `l`; otherwise the rule fails orientation. A positional component, `is_lte` scrutinees or flipping scrutinees, is counted with the pattern's root in every context that changes the count. N15c's component, calls with a literal first operand and a non-literal second, reads which variables are literals: one under "the variable is a literal" or as a literal switch's key is, one under "the variable is not a literal" is not, and the rule must decrease with every other variable at such an operand taken both ways | `derive/order.zig`, a pure function of two patterns and the variables their conditions make literals |
| speculation | wherever strict evaluation of `l` does not crash, strict evaluation of `r` does not crash either, for every assignment of values and ⊥ to the variables | step 3 of the loop, in a strict encoding beside the most-defined one |

Orientation counts on the unfolded term for the reason normal-form 3.0 gives:
under sharing a graph count can rise. The measure's last component, the
graph's nodes, belongs to N5 and N6, and a rule is not judged by it.

An equation that fails orientation in both directions (commutativity is the
typical case), or fails the speculation check in the preferred direction, goes
to the ledger as unoriented. With these three checks the emitted form computes
the body's result wherever the body does not crash, and never evaluates a crash
the body did not, which is C2. A `crash` written in the body stays a node, so
"a branch that always crashes is unreachable" is not an equation, and
normal-form 7.2 follows from the definition.

The equation set E is the table's rules read as equations plus the ledger's
unoriented entries. No separate equation file exists.

### 2.3 Tiers: which rules the tool writes

| Tier | Rules | Written by | The tool's role |
|---|---|---|---|
| F, first-order | N1k, N1l, N13a to N13c, N13e to N13i, N13n, N13o, N13p's literal operands, N13q, N13s, N13t, N15a, N15b, N15c's literal-last half, N7d's merge, and every rule the tool finds | the tool | finds, proves, generalizes, writes the row and its tests |
| E, evaluation | N13j and N13k: a builtin over literals, when it does not fail there, to its value | two hand-written rows whose result the builder computes with the evaluator's arithmetic | none: a computed result has no term form to orient or pair, so step 1 skips the rows and the normalizer applies them |
| C, context | N5, N13d, N13m, N13p's operands an earlier operand decided, N13u's intervals, N15c's root-parameter half, N7 decision trees, placement | hand-written algorithms | explores terms that contain them; a candidate that only context can join is filed against the algorithm with its witness. The intervals are context, but a tier F row can read one as a condition (3.4) |
| B, binders | N11 (N11n and N11o included), T1 to T6, N12, N13r, N14, N8 (N8k included) | hand-written algorithms | same as tier C |

Tier F is larger than it looks. A switch arm reads its payload through
`Payload`, `Field` and `Index` nodes (normal-form 3.2), not through bound
variables, so a `Switch` with closed arms, and the known-constructor rule
`Payload(Tag(t, v), t, 0) -> v`, are first-order terms. Only rules that
substitute into a region's parameters leave tier F.

A candidate that needs a new symbol, as nested `Bool` switches needed `And`
and `Or` and copied outer arms needed joins, is a divergence (3.5). Choosing
the symbol is the one decision the tool leaves to a person.

---

## 3. The loop

One iteration is one run of `zig build reify-rules -- --sig <S> --k <k>`
followed by triage of its report. The run is deterministic: the same table,
signature, k and input set give the same report.

```
  table + ledger ──▶ 1 critical pairs ──┐
        ▲            2 explore ─────────┤ candidate pairs
        │                               ▼
        │                          3 prove ──fails──▶ witness added to the input set
        │                               ▼
        │                          4 generalize
        │                               ▼
        │                          5 classify ──divergence──▶ person decides (3.5)
        │                               ▼
        └──── admit: row + tests ◀── 6 triage ──▶ ledger entry
```

### 3.1 Step 1: critical pairs

| Item | Concrete form |
|---|---|
| input | the tier F rows of `rules/table.zig`, whose argument patterns are first-order terms with pattern variables |
| instances | a row is read as its first-order instances (`term.instances`): a run of `And` or `Or` operands or of a chain builtin's operands (N15a), a sequence variable, takes zero to two fresh variables, an identity or absorbing operand is its literal at `I64`, and a variable under N13s's polarity condition takes each shape the condition accepts among the leaves (a variable, its negation, an integer `is_lt` or `is_lte`) and the `And`, `Or` and `Bool` switch of two leaves. Overlaps, orientation and joins are checked for every instance |
| overlap | for each ordered pair of rows (a row with itself included) and each non-variable position of the first left side, unify the second left side there; the plan's L6 overlap list is the same enumeration |
| conditions | a pair of conditional rows overlaps only where both conditions can hold: a sort condition picks a sort that meets both. A variable that a row needs to be a literal and that unification left a variable takes each literal the rows' instances name, `False`, `True`, and one integer above them all, which stands for the literals no row names; each choice is its own instance. A condition that reads a node (speculatable, a speculatable run, the root's type) is read on the built peak |
| peak | the unified term, built with the builder's rules-off mode. A term with regions (`And`, `Or`, `Switch`) that occurs twice is built once and read at both places, as in a body that binds it once: two builds would be two nodes, one per region, which a repeated pattern variable does not match. The builder decides whether each row rewrites the peak at its position (`Builder.rewrites`), so a pair exists only where the rows' conditions hold on the peak as the builder builds it, and an instance either row refuses is no overlap. The reducts are built the same way |
| join | both one-step results normalized by the real normalizer with every rule enabled; unequal normal forms make a candidate |
| cost | quadratic in the tier F rows, each pair one small normalization: seconds for the rule counts of the plan |

A step 1 pair is compared modulo the ledger's step 1 entries only. A
signature's entries name that signature's members, such as `tag#1` for `B`
in S1, and step 1's pattern terms give each union one member. A step 1 entry
is over pattern terms, which every signature instantiates, so step 2 uses
both kinds.

A candidate from step 1 is already an equation, because both sides are
reducts of valid rules. When its variables and nodes have the signature's sorts,
with at most the signature's base variables of each sort, it goes through steps
3 to 5 like a candidate of step 2, with every variable defined: it is proved,
generalized, classified and admitted by `--admit`. A refutation there means a
wrong row, and the tool stops. Any other step 1 group is filed or ledgered by
a person.

### 3.2 Step 2: exploration

| Item | Concrete form |
|---|---|
| signature S | a set of sorts and ops, fixed per milestone (table in 5); variables: two per sort; literals: a fixed list per sort |
| enumeration | typed terms bottom-up by size (node count), each new term built in the builder's rules-off mode only from irreducible subterms, and kept only if the normalizer leaves it unchanged: the enumeration visits normal forms only, as QuickSpec and Optgen prune. It builds no term that a well-formed body cannot contain: a `Payload` of a member its union can never be, by the tags it builds, the arms its switches can run, and what a dominating switch decided, is a compiler bug (`eval.zig`), and, being ⊥ on every input, it would join every term around it into one group |
| fingerprint | the term's results in `eval.zig`'s `most_defined` mode on a fixed input set: 64 assignments of the term's variables, containing ⊥ for each variable, 0, 1, -1, the minimum and maximum of the width, a divisor 0, both tags of each union, and for floats `NaN`, `-0.0`, `0.0` and the infinities, then seeded random values. Values compare by bits, and ⊥ equals only ⊥ |
| candidates | terms grouped by sort and fingerprint; in each group every term is paired with the group's smallest term, because each is already a normal form and any two differ. A second pass groups by the fingerprint over the inputs where no variable is ⊥, and pairs the terms the first pass did not: such a pair is claimed with every variable speculatable, which the builder assumes of a variable, so `Bool.is_eq(x, x) = True` is found although constant folding leaves no ground witness of it |
| cost | exponential in k; the table in 5 fixes k per signature so that a run takes under 15 minutes on one core |

### 3.3 Step 3: proof

| Sort of the variables | Proof |
|---|---|
| `Bool`, tags, records of these | exhaustive over all assignments |
| integers | exhaustive at 8-bit width for up to two integer variables, as a fast filter; then `z3` over 64-bit vectors, and at every builtin width if the pair contains a width-dependent op. A pair whose literal switch has a variable for a key, as generalization makes it, has no row to evaluate, so `z3` alone decides it |
| floats | `z3` over IEEE floating point |

The SMT encoding gives each term a pair (defined, value), following 2.1: a
strict op is defined when its arguments are and its own condition holds; a
`Switch` is defined when its scrutinee and chosen arm are, or when every arm is
defined and all agree. A literal switch takes the arm of the first key equal to
its scrutinee, else its default arm, and its keys count with its scrutinee. A variable gets a free defined bit. A pair is proved
when `z3` reports the negation unsatisfiable. The speculation check of 2.2
uses a second, strict encoding of the same terms, in which a node is defined
only when every node its region runs is defined, and proves that `l` defined
implies `r` defined. The exhaustive checks evaluate both encodings with ⊥
among the assignments. A counterexample joins the input set in `derive/inputs.zon`, so
the next run separates the pair by fingerprint. A `z3` timeout counts as
unproved and is listed in the report.

Checked arithmetic is defined where SMT-LIB's overflow predicates (`bvsaddo`,
`bvsmulo`, `bvsdivo` and their unsigned forms) are false, and a quotient also
needs a nonzero divisor. The same test at twice the width is exact too, but
`z3` times out on it for `times` and `//`.

A `z3` answer depends only on its script, so the prover keeps each answer by
script and sends the scripts the loop is about to need ahead of time, on
`--jobs` processes at once (12 by default): the first proof of every candidate
pair the ledger does not cover, every width of one claim, and every way to lift
one subterm in step 4. The loop reads the answers in its own order, so the
report does not depend on `--jobs`.

Memory is bounded per process, with no coordination between them:

| Process | Bound |
|---|---|
| each `z3` | `-memory:<MB>`, from `--z3-memory` (2048 by default). A query that reaches it answers `(error "out of memory")` and is listed as unproved, like a timeout |
| the tool | each candidate's search modulo the ledger, proofs, generalization and classification allocate in an arena reset after it; the result keeps copies of a new group, a counterexample and an unproved reason. An answer sent ahead is freed when read, or when its lift or its pair is no longer needed |

### 3.4 Step 4: generalization

Starting from the proved pair, under the speculatable conditions a pair of
the second pass carries, the tool replaces one literal or one subterm
occurring in both sides, or in the left side only, by a pattern variable of
its sort, proves the result
again, and keeps it if proved. It repeats until no replacement proves. When a
replacement proves only under a condition, the tool tries the conditions of the
fixed condition language, in this order, and keeps the first that proves.
The weaker conditions come first, so the kept rule is the most general: every
literal is speculatable, and every nonzero literal is a literal. Last, each
condition whose variable no longer occurs, or that the proof does not need,
is dropped.

| Condition | Example use |
|---|---|
| the op is speculatable | N5c-style merges, `is_eq(x, x) = True` |
| the variable is a literal | N13j |
| the literal is nonzero | division rules |
| from phase D4: the variable's interval excludes 0; is at least 0; lies below a literal bound; a checked subterm's interval fits its type | `y // (x // x) -> y` when `x` is nonzero, `x % n -> x` when `0 <= x < n`, `(x * 2) // 2 -> x` when `x * 2` fits |

The interval conditions come after the literal ones, weakest first, and the
builder checks them by N13u's intervals (normal-form 3.13). The prover encodes
each as an assumption on the variable's bit vector.

A literal switch's key is a literal like any other, and a lifted key stays a
variable in the key position: the switch's form makes it a literal, so the
row needs no condition for it.

Once no replacement proves, the tool replaces the owner of every integer
builtin, and of every literal switch's scrutinee, by a pattern owner under
"the owner is a builtin integer type" (N13q, N1l), and keeps that when it
proves at every integer width. The
condition "the sort is not a float type" (N13n) joins the language with S2,
the first signature with floats.

Pairs that generalize to the same equation, up to renaming, form one group in
the report.

### 3.5 Step 5: classification

| Class | Test | Report says |
|---|---|---|
| F rule | the generalized equation is first-order, orients under ≻, and passes the speculation check | a ready table row, and the generated tests of 3.6 |
| unoriented | proved, but fails orientation both ways, or speculation in the preferred direction | a ledger entry with its criterion |
| context or binder | the smallest witness contains a loop, a join or a test that dominates the redex, or the group's witnesses join once the tier C or B algorithms run; an equation whose every variable a condition fixes to a literal is constant folding (N13j) | a filed issue against the named algorithm, with the witness as its test |
| divergence | the same equation shape, up to nesting depth or arm position, appears at two consecutive sizes; or step 1 produced, in three consecutive iterations, rules that are instances of one shape | the shape, its instances, and the stop: no row is admitted from this group until a person decides |
| out of scope | the equation is about a builtin's body outside layer L, or sorts operands of a commutative op | a ledger entry, per normal-form 3.16 and 7.2 |

A candidate pair whose two normal forms are equal modulo the ledger's
equations is not reported, so one ledger entry does not return as a new group
for every instance of it. The report decides this by searching, from each
side, the terms that at most two ledger steps in either direction reach, each
normalized after its step, of size at most three more than the larger side.
A step by a rejected entry is not normalized after: it must land on a normal
form, because a rejected entry relates normal forms that deliberately differ.
Where the table rewrites the result, the table misses a row for the other
side, such as `plus(x, 0) = x` beside `plus(0, x) = x` under the rejected
commutativity of `plus`, and the pair is reported. An open entry stands for an
algorithm still to come, so its step is normalized after. A step must also
leave a well-sorted term: a side that is a variable matches a subterm of any
sort, so `or_(x0, x0) = x0` read right to left would put `or_(u, u)` where a
union `u` stood, and the search drops such a step.
The search runs from both sides because normalizing cannot undo a rewrite, so
a step can apply to one side only. The set is finite, so the search is exact
within the bound.

### 3.6 Step 6: triage and admission

The person running the iteration takes each group of the report and does one
of three things. Each is one command, so triage is review, not writing:

| Action | Command | Writes |
|---|---|---|
| admit | `--admit <groups>` | the row in `rules/table.zig`; its fires, condition and knockout tests of plan 5.3 in `src/reify/derive/derived_test.zig`, generated from the witnesses recorded in `derived.zon`; a line in the ledger's admitted list with the iteration number. A rejected entry whose pair the new row joins, such as unconditional `minus(x, x) = 0` when its form under "`x` is speculatable" is admitted, is removed in the same command and named in its output, so the review sees both |
| reject | `--ledger <groups> <criterion>` | an entry in `src/reify/rules/ledger.zon`: the equation, the criterion, the witness pair, which the L3 suite then asserts stays unequal. An entry has no conditions, so a conditional equation is recorded as its witness pair, which fixes the owner and the literals its conditions name; an integer owner alone is stated by the entry's owner variable `o0` |
| file | `--file <groups> <algorithm>` | an entry in the ledger's open list, with its witness pair, recorded as for reject. The change to the algorithm that joins the pair removes the entry; the check of 4 fails until it does |

`<groups>` is one group id or several, comma-separated, all ids of one
report: a batch is for groups that no admission in it joins, such as the
identities of different builtins, and the next report checks that it was.

A row the tool admits is data: root op, argument patterns, condition and
result, which the table's dispatch interprets as it does every hand-written
tier F row. The tool generates no Zig code beyond the row and the tests.

The admission criteria are part of the language version, like R:

| Criterion | Rejects |
|---|---|
| proved by step 3 | anything else, timeouts included |
| orients and passes the speculation check | an equation usable only by speculating |
| in scope | a law about a builtin body outside layer L; operand sorting for commutative ops |
| tier F | nothing: a context or binder candidate is filed, not rejected |

After triage the next iteration runs. At fixed S and k the iterations end when
the report has no group left. Then k rises by one, up to the milestone's k in
5.

---

## 4. Code layout

The tool is a separate build step. The compiler does not import it, so the
compiler contains no inference, as `AGENTS.md` requires.

| File | Content | Uses |
|---|---|---|
| `src/reify/derive/main.zig` | the program: arguments, one run (with `--knockout <row>`, one without that row), the triage command | all below |
| `src/reify/derive/loop.zig` | one iteration of 3, grouped for triage | all below but `report` |
| `src/reify/derive/report.zig` | argument parsing, the report and its proposed commands | `loop` |
| `src/reify/derive/term.zig` | first-order view of table patterns; unification; the term text format | `rules/table.zig` |
| `src/reify/derive/cp.zig` | step 1 | `term`, `builder`, `equal` |
| `src/reify/derive/sig.zig` | the signatures of `signatures.zon`, and the build of a term into a row | `builder` |
| `src/reify/derive/enumerate.zig` | step 2's enumeration of irreducible terms | `sig` |
| `src/reify/derive/fingerprint.zig` | step 2's input set and fingerprints | `eval.zig` in `most_defined` mode |
| `src/reify/derive/explore.zig` | step 2's grouping into candidate pairs | `enumerate`, `fingerprint` |
| `src/reify/derive/smt.zig` | the SMT-LIB encoding of both semantics | `sig` |
| `src/reify/derive/prove.zig` | step 3 and the speculation check of 2.2: exhaustive checks in both encodings; SMT-LIB text written to `z3` over a pipe, on `--jobs` processes at once, with each answer kept by script | `eval.zig`, `smt` |
| `src/reify/derive/generalize.zig` | step 4 | `term`, `prove` |
| `src/reify/derive/classify.zig` | step 5, and the text of a proposed row | `prove`, `order` |
| `src/reify/derive/triage.zig` | the search modulo the ledger, which checks a conditional equation's conditions on each match, and the files triage writes | `term` |
| `src/reify/derive/recall.zig` | criterion 1 of 6.1: `--recall` knocks out each first-order row and runs steps 1 to 5 without it, from an empty ledger | `loop` |
| `src/reify/derive/holdout_test.zig` | criterion 5 of 6.1: the holdout pairs of 6.3 have one normal form | `sig` |
| `src/reify/derive/order.zig` | the orientation check of 2.2 | `ir`, `prims` |
| `src/reify/derive/derived_test.zig` | the fires, joins and knockout test of every admitted row | `derived.zon`, `sig` |
| `src/reify/derive/signatures.zon` | the signatures S1 to S3 of 5 | |
| `src/reify/derive/inputs.zon` | the counterexamples that grow the input set | |
| `src/reify/derive/derived.zon` | the witnesses of admitted rows | |
| `src/reify/rules/ledger.zon` | admitted, rejected and open entries | |

| Check | Where it runs |
|---|---|
| step 1 on the current table: every unjoined critical pair is equal modulo the ledger | every `zig build test`; it replaces the critical-pair row of plan 5.7 |
| steps 2 to 5 at the current milestone's S and k: no group left | a scheduled CI job, and before merging a change to the rule table |
| the ledger's rejected pairs still unequal | L3, every `zig build test` |
| the holdout pairs of 6.3 meet | every `zig build test` |
| the ledger's open pairs still unequal; a pair that now meets names its entry to remove | every `zig build test` |

`z3` is the only external tool. It is pinned by version and needed only by
`zig build reify-rules`, not by `zig build` or `zig build test`.

---

## 5. Phases and signatures

| Phase | With plan milestone | Work | Done when |
|---|---|---|---|
| D0 | M0 | `most_defined` mode of `eval.zig`; the builder's rules-off mode, compiled only into the tool and test builds beside the knockout switch; `term.zig`; `order.zig`; the report skeleton | every M0 table row passes orientation; the evaluator's tests cover ⊥ in each op kind |
| D1 | M4, first half | step 1; the CI check of 4 | criterion 2 of 6.1 passes |
| D2 | M4, second half | steps 2 to 6; `prove.zig` with `z3`; the three triage commands | one iteration runs end to end on S1 at k = 3 |
| gate | end of M4 | three iterations on S1 (k = 3, 4, 5), then the criteria of 6 | the gate record of 6.3 is filled in and a decision taken |
| D3 | each plan milestone after the gate that extends a signature, if the gate passes | each milestone extends the signature, runs the tool to an empty report at its k, and admits its tier F rules through it | the milestone's exit condition in plan section 4 includes an empty report |
| D5 | M15 | S1 and S2 at k = 6: S1 first, then S2; `--recall` again, for rows whose left side has a size of 6 or less; each run's time and peak memory kept in 5.2 | S1 and S2 reach an empty report at k = 6 |
| D6 | M16 | S1 and S2 at k = 7, which enumerates G6's terms; a group that only N13r joins is filed against N13r, which lands with plan M5 | S1 and S2 reach an empty report at k = 7 |
| D4 | M11 | the interval conditions of 3.4, read on the built peak as step 1 reads the other conditions (3.1); the S2 ledger entries rejected for a missing condition are tried again | S2 reaches an empty report at k = 5 with the interval conditions |

| Signature | Milestone | Sorts | Ops | k |
|---|---|---|---|---|
| S1 | M4 | `Bool`, `I64`, a union `[A(I64), B]`, a record `{ x : I64, y : Bool }`, a tuple `(I64, Bool)`, a nominal `N` over `I64` | `Bool.not`, `And`, `Or`, `is_eq`, `is_lt`, `is_lte`, `is_gt`, `is_gte`, `plus`, `minus`, `Switch` on `Bool` and on the union, `Tag`, `Payload`, `Record`, `Field`, `Tuple`, `Index`, `Wrap`, `Unwrap`; literals `0`, `1`, `True`, `False` | 5; 6 in D5; 7 in D6 |
| S2 | M5 | S1 plus `F64`, `Str`, a three-tag union | S1 plus `times`, `div_trunc`, `plus_wrap`, `times_wrap`, `bitwise_and`, `bitwise_or`, `bitwise_xor`, `Str.concat`, literal switches on `I64` and `Str`, nested switches; literal `-1` | 5; 6 in D5; 7 in D6 |
| S3 | M6 and later | S2 plus `List(I64)` | S2 plus `List.len`, `List.get`, and region-level terms with one loop, for filing tier B candidates only | 4 |

S2 is built in stages. The first stage has S1's sorts and adds the integer
builtins and the literal `-1`. The second adds literal switches on `I64` with
one key, each an integer literal of the signature that no chain builtin owns
(`0` and `1`); the key counts as one node of the term's size. An operand of a chain builtin (`times`,
`div_trunc`, the wrapping and bitwise ops) is a variable, a literal or the
same builtin, and a comparison never reads one. These are the terms whose
laws the normal form claims (3.15); a mixed term such as
`plus(times(x, y), 1)` holds no law that the builder could use.

Budget for building the tool: D0 to D2 together take at most three weeks of
work. If D2 does not run end to end by then, the gate is taken with the parts
that run, and criterion 7 fails.

### 5.1 Source coverage: R against the signatures

The derivation reaches a refactor of R (normal-form 7) only when a signature
holds the ops of both sides at a size within its k. The rest are left to the
hand-written tiers and to L3 and L4. Each R row, by where it enters:

| R row | Absorbed by | Tier | Enters the derivation | Holdout pair |
|---|---|---|---|---|
| `and`/`or` and their `if`; nested `if`s or one condition; `if a Bool.False else b`; `a >= b` or `!(a < b)`, with branches swapped | N1c, N1l, N7d, N13e to N13t, N15b | F | S1 | 12 pairs, all meet |
| build a record or tag and read it back | N13a | F | S1 | 2 pairs, meet |
| build a tuple and read it back; destructure a tuple | N13a, N1f | F | S1 | 1 pair, meets |
| wrap a value in a nominal and unwrap it | N13b, T4.1 | F | S1 | 1 pair, meets |
| match on a value whose tag is known | N13c | F | S1 | 2 pairs, meet |
| repeat a test a dominating branch made | N13d, over switches and over `And` and `Or` operands | C | S1 | 1 pair, meets since iteration 8. The operand half is an algorithm, not rows: as first-order rows it leaves pairs only Boolean absorption joins (6.3) |
| name a constant computed from literals | N13j, N13k | E | S1 for integers and `Bool`; S2 adds floats, S2 and S3 `Str` and `List` | 1 pair, meets |
| `if x == 1 ... else if x == 2` as `match x` | N13n, N7c, and the `/N13n` mirrors of the rows over `Bool` switches (plan 3.7) | F, C | S2's second stage for one key (`switch_lit`), from iteration 7; step 1 checks the mirrors and N13n on S1's terms. A switch with two keys, which N7c builds, is not enumerated | none yet |
| a helper that returns a tag or a `Try`, matched by its caller, or its tests in place | N13r | B | S1 and S2 hold its terms, but the smallest is `switch_(switch_(c, tag#1(), tag#0(x)), a, b)`, of size 7, over S1's k of 5 | none |
| regroup `Str.concat`, `List.concat`, wrapping arithmetic, bitwise chains; add or drop `""` | N15a | F | S2 for the wrapping and bitwise chains; `Str.concat` waits for S2's `Str`, and no signature has `List.concat` or a `Str` literal, so the identity `""` is never built | none yet |
| `x.f(y)`, `f(x, y)`, `x \|> f(y)`; an operator and its method; destructure a record; record update; defaulted fields; `expect`; literal spelling; `!=` | N1a to N1k | the walk | the two sides are one term before the builder sees them | the plan's L3 pairs |
| rename a binder; reformat; reorder independent bindings, `var`s or record fields; `var` or a chain of bindings | N2, N3, N4, N9, N10 | no rule: the IR has no names, order or positions to differ | none needed | L3 |
| bind a value once or twice; once before a `match` or in every arm; move a binding into or out of a branch; drop a dead binding; hoist loop-invariant work | N5, N5c, N6 | C | the term language has no sharing or placement, so both sides are one term; the hand-written algorithms are tested by L1 and L6 | L3 |
| reorder non-overlapping `match` arms | N7a, N7b | C | flat arms are indexed by tag, so both sides are one term; nested patterns wait for S2's nested switches | L3 |
| loops: `for` or `while`, `.iter()`, `continue` and `break` placement, tail recursion, `return x` last, a loop variable nothing reads | N11, N12, T1 to T6 | B | S3 files tier B candidates with one loop; no signature has `Return` or exits | L3 |
| helpers and closures: extract, inline, move, rename, reorder or drop parameters, make generic, eta, the same function from two sites, `Apply` of a function chosen by an `if` or read from a record | N8, N8i | B | no signature has `Call`, `Closure` or `Apply` | L3 |
| pass a helper `a, b`, `{ a, b }` or `(a, b)`; one record `var` or one per field | N14 | B | no signature has row parameters or loop slots | L3 |
| a loop that appends, or `List.map` or `List.keep_if`; `List.fold` or its loop; two `map`s or one | N16 | B, layer L | no signature has `List.map`, `List.keep_if`, `List.fold` or closures | L3 |
| `len() > 0` or `!is_empty()`; `len() == 0` or `is_empty()` | N16f | F, layer L | S3 has `List.len`; `List.is_empty` joins it with M10 | none yet |
| `a + 1` or `1 + a`; `x == y` or `y == x` over the root's parameters | N15c | F for a literal operand, C for parameters | S1 for `plus` and `is_eq`, S2 for `times`, from iteration 7 (the literal half); the ledger's commutativity entries for `plus` and `is_eq` stay rejected for two variables | none yet |
| regroup a `plus` chain that no grouping overflows; `while $i <= n` with `n` bounded | N13u, N15a, N11l | C, B | D4's interval conditions over S2 for the chains; the loop needs S3 | L3 |
| a `$done` flag loop or its `break`; a second counter or `i + j0` | N11n, N11o | B | S3 files tier B candidates with one loop | L3 |

The rows of 7.1 and 7.2, which must stay apart, enter as rejected ledger
entries when a run finds them: in S1 so far, the commutativity of `plus`,
`is_eq`, `And` and `Or`. Float reassociation and `x * 2` against `x + x` wait for
S2's floats.

Tier F and E rules that no signature can reach, which the signatures of 5
gain before the milestones that absorb their R rows:

| Gap | Rule | Needs |
|---|---|---|
| G1 | N13a on tuples | closed: S1 has `(I64, Bool)` with `Tuple` and `Index` |
| G2 | N13b | closed: S1 has the nominal `N` over `I64` with `Wrap` and `Unwrap`. Its one nominal proves `Wrap(Unwrap(x)) = x` by sort, so the row writer states `same_ty` on a `Wrap` root, which the table needs over every nominal |
| G3 | N15a identities | closed for the integer chains: S2 has `plus_wrap`, `times_wrap`, `bitwise_and`, `bitwise_or` and `bitwise_xor` with `0`, `1` and `-1`. Open for `Str` literals including `""` and `List.concat` with `[]` |
| G4 | N13j over floats, and the float row of 8 | `F64` literals: `NaN`, `-0.0`, `0.0`, the infinities, `1.0` |
| G5 | N13m | a `U64` sort for the index of `List.get` and the result of `List.len` |
| G6 | N13r | k = 7 on the switch-over-switch terms, which D6 runs; until plan M5 builds N13r, the groups only it joins are filed against it |

### 5.2 D3 record

Each extension of a signature after the gate, and the iteration that brings
its report back to empty.

| Iteration | Signature change | k | Groups | Admitted | Filed | Recall (6.1, criterion 1) |
|---|---|---|---|---|---|---|
| 4 | S1 gains G1 and G2: `(I64, Bool)` with `Tuple` and `Index`, the nominal `N` over `I64` with `Wrap` and `Unwrap`; x8 to x11 follow the old variables, and each stored input gains their defaults | 3, 4, 5 | 1 at k = 3, 0 at k = 4, 1 at k = 5 | T4.1, `Wrap(Unwrap(x)) = x` under `same_ty` | tuple eta, `tuple(index#0(x), index#1(x)) = x`, under N13a beside the record one | 46 of 70 rows found; 46 of the 49 with a witness (94%). The N13a tuple row, N13b and T4.1 are found; the misses are the three N13t rows of 6.3 |
| 5 | S2's first stage: S1's sorts; `times`, `div_trunc`, `plus_wrap`, `times_wrap` and the bitwise ops; literal `-1`. Chain builtins read only variables, literals and themselves, and only a chain reads `-1` (5). N15a is written by hand as n-ary rows over sequence variables: flattening, identities, and absorbers under a speculatable run | 3, 4, 5 | k = 5 first gave 1495 groups; after the chain restriction and N15a, 135; after `-1` was restricted, 24; after triage, 7, which were admitted, then 0. k = 3 and 4 end at 0 | T5.1 to T5.3, T5.6 to T5.12 (`div_trunc` chains), T5.16 and T5.17 (`times` by 0) | none. Rejected: commutativity of the six chain builtins; idempotence of `bitwise_and` and `bitwise_or` and cancellation of `bitwise_xor`, which are not confluent with order-kept flattening (the free band word problem); 17 unoriented `times` and `div_trunc` groups; `div_trunc` by 0; two step 1 pairs that need a nonzero condition on a variable. Four `times` claims stay unproved: `z3` answers `unknown` | not run: recall tests hand-written rows, and the tool admitted every new row here but N15a's, whose sequence variables it cannot state (6.3) |
| 6 | none: step 1 checks every pair on a peak the builder builds, with conditional rows at each named literal and repeated terms with regions built once and shared (3.1), and a step 1 pair over the signature's sorts goes through steps 3 to 5 | 3, 4, 5, on S1 and S2 | step 1 first gave 17 unjoined pairs, then 12 more once repeated terms were shared; after triage, 0 at every k on both signatures | T6.1, T6.2: `is_eq` of two integer comparisons that negate each other is `False`, from pairs of T3.2 and T3.3 with N13q | removed rows, their equations rejected: T3.4, T3.5 and T3.13, `is_eq(or_(x, y), x) = or_(x, Bool.not(y))` in three arrangements, whose form over n operands does not orient, so they are not confluent with N15b; T3.2 and T3.3, `is_eq(Bool.not(x), x) = False`, which N13t's negation of an `And`, `Or` or `Bool` switch x steps around. Rejected: `is_eq` commutativity over step 1 terms; five equations those removals leave apart. Filed against N15b: absorption, `and_(or_(x, y), y) = y`, and `or_(is_eq(x, y), y) = or_(y, Bool.not(x))`, which need rows over operand runs. Four `times` claims stay unproved, as in iteration 5. Peak memory of the tool 1.5 GB | not run, as in iteration 5 |
| 7 | S2's second stage: one-key literal switches on `I64` (`switch_lit`), with keys `0` and `1`. The table gains N15c's literal half, under the new condition `not_lit` and the measure component `unordered_leaves`; N13n loses its row for `k == x`; the table derives the `/N13n` mirrors (plan 3.7); the tool lifts keys to variables, proves keyed switches with `z3` alone, and counts the builder's N7 steps on a literal switch as rewrites | 3, 4, 5, on S1 and S2 | step 1 first gave 496 unjoined pairs, 240 after N15c, and 0 with the mirrors. The tool proposed 34 mirror rows at k = 3 but could not state N7d's `movable` conditions or its operand runs, so the table derives them instead. S1 then gave 5 groups at k = 5 and S2 36: the rejected entries were written with a literal first, and N7 on a literal switch did not count as a rewrite. After both fixes, 1 group on S1 and 7 on S2; after triage, 2 on S2 at k = 5, two of the filed equations at the key `0`; then 0 at every k on both | none by `--admit`: 39 mirror rows are derived (32 of N7d, 4 of N13o, one each of N13e, N13f and N13t), and N15c's three rows are written by hand, because the tool does not try `not_lit` | removed as redundant under N15c: T1.9, T3.12, T5.2, T5.17, the literal-first twins of T1.10, T3.11, T5.1, T5.16. Rejected: `minus(x, minus(y, x)) = plus(minus(x, y), x)`, the old entry with the literal last. Filed against N13d: eight witnesses of six equations in which a literal switch's keyed arm reads the scrutinee as its key. Two `times` claims stay unproved. Peak memory of the tool 5.4 GB, up from 1.5 GB, from step 1's pairs over the mirrors; a run takes 3 to 4 minutes | not run, as in iteration 5 |
| 8 | none: the builder gains N13d. A `Bool` or tag switch whose scrutinee a dominating arm or an earlier `And` or `Or` operand tested is that arm; an `And` operand that an earlier operand or a dominating arm decided `True` is removed, and an `Or` operand decided `False`. Each counts as an algorithm step, as N7 on a literal switch does | 3, 4, 5, on S1 and S2 | 0 at every k on both, with no triage | none | the open entries `and_(x0, x0) = x0` and `or_(x0, x0) = x0` now join and leave the ledger. The holdout pair for a repeated test now meets. The ledger's open entries filed against N13d stay open: each reads a tested value as its literal inside an arm, which N13d's switch half does not do | not run, as in iteration 5 |

---

## 6. Meta-testing: does the strategy work?

The tool can run correctly and still not be worth having: it may find nothing
the reviews did not, or bury the person in noise. The gate measures both after
the first three iterations, and ends in a decision.

### 6.1 Criteria

| # | Criterion | How it is measured | Passes when |
|---|---|---|---|
| 1 | knockout recall | for every tier F row in the M4 table: disable it with the table's knockout switch (plan 5.3), run steps 1 to 4 on S1 at k = the row's left-side size + 1. The row counts as found when the tool proposes an admissible group whose admitted rule makes the row's L1 fires test pass again | at least 90% of rows found; every miss is explained by a stated limit (size over k, needs context) |
| 2 | rediscovery of the hand-found pairs | step 1 reports the four pairs the reviews found by hand, each under the knockout of the rows that join it: with the mirrors of N7d and N13o knocked out, N7d with N13i, N7d with N13q, and N13o with N13i; with the arm-swapped half of N13q and N13s, which generalizes it, knocked out, N13q with N13i and N1l. | all four reported, each with a correct proposed row |
| 3 | soundness | admitted rules that the L5 differential or any later test shows wrong | zero. One failure stops admission until `prove.zig` is fixed and every admitted row is proved again |
| 4 | new finds | valid, admissible groups at S1, k ≤ 5, that no hand-written rule or R row covered | at least one; or a report empty at k = 5 before any admission, which proves the hand rules complete up to 5 over S1. Either result is informative, and the gate records which |
| 5 | holdout | the R rows and L3 pairs in S1's scope, chosen and frozen before iteration 1 and never used as a seed or witness: the fraction whose two sides meet after iteration 3 | 100% of those within size k; any miss is a filed tier C or B issue |
| 6 | precision | the decisions of an iteration after iteration 1: the groups a person gives a command, taking the report again after each admission, which removes the groups the new row joins. Noise is a decision that a later fix to the tool, not to the table, undoes | at most 60 decisions per iteration, and at most 25% noise |
| 7 | cost | wall time of one run on S1 at k = 5; triage time per iteration; tool size; the build budget of 5 | a run under 15 minutes on one core; triage under one day; `src/reify/derive/` under 5000 lines outside tests; D0 to D2 within three weeks |
| 8 | convergence | group count per iteration at fixed k; divergences raised | the group count falls every iteration at fixed k; at most two divergences over the three iterations, each resolved by a recorded decision |

Criteria 1 and 2 test the method against rules whose answer is known.
Criterion 5 tests it against refactors it never saw, which is the property the
normal form exists for. Criterion 4 asks whether it adds anything over the
hand process. Criteria 6 to 8 ask whether it is affordable.

Criteria 6 and 7 are restated after the first measurement of 6.3, which
failed them: 6 counted every group of a report, most of which one admission
removes without a decision, and 7 limited the whole directory to 4000 lines.
The gate record keeps both measurements.

The holdout for criterion 5 is written into the gate record before iteration
1: the R rows on `and`/`or` and nested `if`s, on `if a Bool.False else b`, on
`a >= b` and `!(a < b)`, and on negated conditions with swapped branches, with
their L3 pairs.

### 6.2 Decision

| Outcome | Decision |
|---|---|
| all eight pass | continue: D3 runs; from M5 on, a tier F rule enters the table through `--admit`, and a hand-written tier F row needs a stated reason in its review |
| 1 or 2 fails, the rest pass | the encoding of patterns or signatures is wrong: fix it once and repeat the gate once. A second failure is handled by the next row |
| 1, 2 or 5 fail after the repeat, or 6 or 7 fail | stop the exploration: keep D1's critical-pair check in CI, which costs seconds and catches the class of bug the reviews caught by hand; delete steps 2 to 6; rules stay hand-written with the plan's L1 and L6 tests |
| 3 fails | stop admission at once, whatever else passes; fix the prover; repeat the gate |
| 8 fails with repeated divergence | the signature needs a new symbol before the tool can help; record the decision of 3.5, then repeat the gate once |

### 6.3 Gate record

Filled in during the gate and kept in this section. Group counts are those
of each iteration's first report; noise counts the groups that left the
report without a triage command of their own, because another group's row
joined them or a fix to the tool removed them.

| Item | Value |
|---|---|
| holdout rows and pairs | the 14 pairs of `src/reify/derive/holdout_test.zig`, over the refactors named in 6.1. They were written down after iteration 3, not before iteration 1; no run used them as a seed or a witness, but the enumeration visits every term of size ≤ 5, the smaller pairs included |
| iteration 1 | k = 3; 29 groups; admitted 11 (T1.1 to T1.11), rejected 6, filed 9; noise 3 (10%); run seconds; triage under 4 h, with the D2 build, whose commit admitted T1.1 to T1.7 |
| iteration 2 | k = 4; 30 groups; admitted 2 (T2.1, T2.2), rejected 2, filed 6; noise 20 (67%); run seconds; triage 31 min |
| iteration 3 | k = 5; 132 groups, 114 once constant folding (N13j) landed; admitted 13 (T3.1 to T3.13), rejected 29, filed 16 net; noise 56 of 114 (49%); run 7 s; triage 6 h 49 min, with the folding tier, defined candidates and the enumeration filter built during it |
| criterion 1 | 39 of 68 first-order rows found (`--recall`, k = left size + 1 up to 5, from an empty ledger). 23 rows have no witness: 13 have left sides of size 6 to 10 (N7d, the flipped half of N13q), and N13a's tuple row and N13b have none because no signature has a tuple or a nominal (5.1, G1 and G2), and in 8 other rows cover every S1 term of size ≤ k (N13e, N13f, N13i, N13s, two N13p rows, two N15b rows). Of the 45 rows with a witness, 39 are found (87%). The 6 misses (N13a's field and payload rows, the three N13t rows, N13g) are equations the tool proves, but it cannot state them as rows: a record or tag root, n-ary `And` and `Or`, and a `Bool` scrutinee that generalization lifts to a union. That is an encoding miss, not a stated limit |
| criterion 2 | pass: `cp.zig` asserts the four hand-found pairs under their knockouts |
| criterion 3 | pass, provisionally: no admitted row is known to be wrong. Every one is proved, and `derived_test.zig` passes; the L5 differential does not exist yet |
| criterion 4 | pass: 26 admitted rows cover equations that no hand row covered, such as `Bool.is_eq(x, x) = True` and a switch on a literal |
| criterion 5 | pass: 14 of 14 pairs meet, including one of size 8 |
| criterion 6 | fail: 132 groups at k = 5 against a limit of 40, and 49% noise in iteration 3 and 67% in iteration 2 against 25% |
| criterion 7 | fail on size: `src/reify/derive/` has 5013 lines, 4281 outside tests, against 4000. Pass on run time (7 s at k = 5; `--recall` takes 25 min over 10 processes), on triage time (under a day per iteration) and on the build budget (D0 to D2 in one day) |
| criterion 8 | pass: within each k the group count fell with every admission, and no divergence was raised. The three iterations ran at k = 3, 4 and 5, so no two share a k |
| decision and date | 2026-09-26: criteria 1, 6 and 7 fail. The owner chose to fix the encoding, restate criteria 6 and 7, and repeat the gate once |
| repeat, encoding fixed | the row writer states `component` patterns (N13a), and the table gains two switch patterns: `same_arms`, which generalizes N13g to a switch on any scrutinee, and `tag_arm`, the new N13c row for a switch on a known tag. First-order rows for N13p's decided-operand half were tried and dropped: each left 72 to 278 critical pairs unjoined, joinable only by Boolean absorption, which normal-form 7.2 leaves out. That half stays context |
| repeat, criterion 1 | pass: 43 of 69 rows found. Of the 46 rows with a witness, 43 are found (93%). The 3 misses are the N13t rows, whose witnesses repeat a test (`and_(x0, x0)`, `switch_(x0, x0, x1)`) that only a context algorithm decides (N13p's decided-operand half, N13d): the stated limit "needs context". 23 rows have no witness: N13a's tuple row and N13b (G1, G2), 13 rows over k, and 8 that other rows cover within k |
| repeat, criterion 6 as restated | pass: 26, 10 and 58 decisions in iterations 1 to 3. No committed decision was undone by a fix to the tool; the entries removed since were joined by table changes (T1.9, constant folding, N13c, N13g) |
| repeat, criterion 7 as restated | pass: 4401 lines outside tests (5192 in all), under 5000. Run time, triage time and budget as before |
| repeat, criteria 2 to 5 and 8 | as before; criterion 5 now has 20 pairs, 19 of which meet. The open one, a test a dominating branch made, waits for N13d |
| decision and date | 2026-09-27: every criterion passes as restated. D3 runs: from M5 on, a tier F rule enters the table through `--admit`, and a hand-written tier F row states its reason in its review. Before S2's iterations, the signatures gain the tier F and E gaps of 5.1 (G1 to G6) |

---

## 7. Why it stops, and what it guarantees

| Loop | Stops because |
|---|---|
| step 1 inside a run | the table is finite; each pair is one normalization, which terminates by the measure |
| iterations at fixed S, k, inputs | the irreducible terms of size k over S are finite. An admitted rule is valid, so it never separates two terms that shared a normal form, and it rewrites at least its witness, so the number of irreducible enumerated terms falls in every iteration that admits. An iteration that admits nothing, and files or rejects every group, ends the sequence |
| raising k | capped per signature by the table of 5 |
| divergence | detected by the shape test of 3.5 and handed to a person, not iterated |

An empty report at signature S and size k states, recorded with the language
version:

> For every two terms of size at most k over S that step 3 proves equal in the
> most-defined semantics, the normalizer gives one normal form, unless the two
> normal forms are equal modulo the ledger's entries, each recorded with the
> criterion that excludes it.

This is Optgen's "complete up to cost k" applied to equality. It replaces "the
R fuzzer found nothing" with a statement anyone can check by rerunning the
tool. The guarantee is relative to S, k and the prover: fingerprints only
propose pairs, and only proofs admit rules, so a wrong rule never enters the
table through the tool.

---

## 8. Limits

| Limit | Consequence | Handling |
|---|---|---|
| sums have no finite convergent system in general (Lindley, Scherer) | two independent tests in either order cannot be joined by a first-order rule | N7's canonical test order stays a tier C algorithm; such groups are filed against N7 |
| tiers C and B are hand-written | their correctness is tested, not derived | step 2 explores terms that contain them and files every miss with a witness |
| tiers share symbols | no modularity theorem proves the combination confluent | step 2 normalizes with all tiers enabled, so a missing join shows up as a group |
| sharing | critical pairs over terms do not cover graphs with shared nodes (Plump, 1994) | the plan's L6 sharing row stays |
| k bounds the guarantee | a missing rule larger than k is not found | the plan's L3 and L4 still run; their failures become seeds for the next iteration |
| floats | most float identities are false, and proofs are slow; `z3` has one `NaN`, so a float proof holds only up to the `NaN` bits, which fingerprints compare | S2 adds floats only with `z3` floating point and the special values in the inputs; timeouts are listed, not admitted; a float rule whose sides can give `NaN` is admitted only if the exhaustive `F32` check over the special values agrees by bits |
| the most-defined semantics is not what Roc runs | a reader may confuse the two | it exists only to validate rules; 2.1 is the one statement of how the layers relate |

---

## 9. Sources

- Donald Knuth, Peter Bendix, "Simple Word Problems in Universal Algebras", in Leech (ed.), Computational Problems in Abstract Algebra, Pergamon, 1970, pp. 263-297
- Leo Bachmair, Nachum Dershowitz, David Plaisted, "Completion Without Failure", in Resolution of Equations in Algebraic Structures, vol. 2, Academic Press, 1989
- Detlef Plump, "Critical Pairs in Term Graph Rewriting", MFCS 1994, doi:10.1007/3-540-58338-6_102
- Gordon Plotkin, "LCF Considered as a Programming Language", TCS 5(3), 1977 (parallel operators)
- Chandrakana Nandi et al., "Rewrite Rule Inference Using Equality Saturation", OOPSLA 2021, doi:10.1145/3485496
- Anjali Pal et al., "Equality Saturation Theory Exploration à la Carte", OOPSLA 2023, doi:10.1145/3622834
- Nicholas Smallbone, Moa Johansson, Koen Claessen, Maximilian Algehed, "Quick Specifications for the Busy Programmer", JFP 27, 2017, doi:10.1017/S0956796817000090
- Sebastian Buchwald, "Optgen: A Generator for Local Optimizations", CC 2015, doi:10.1007/978-3-662-46663-6_9
- Andres Nötzli et al., "Syntax-Guided Rewrite Rule Enumeration for SMT Solvers", SAT 2019, LNCS 11628
- Julie Newcomb, Andrew Adams, Steven Johnson, Rastislav Bodík, Shoaib Kamil, "Verifying and Improving Halide's Term Rewriting System with Program Synthesis", OOPSLA 2020, doi:10.1145/3428234
- Nuno Lopes, Juneyoung Lee, Chung-Kil Hur, Zhengyang Liu, John Regehr, "Alive2: Bounded Translation Validation for LLVM", PLDI 2021, doi:10.1145/3453483.3454030
- Manasij Mukherjee, John Regehr, "Hydra: Generalizing Peephole Optimizations with Program Synthesis", OOPSLA 2024, doi:10.1145/3649837
- Gordon Plotkin, "A Note on Inductive Generalization", Machine Intelligence 5, 1970; John Reynolds, "Transformational Systems and the Algebraic Structure of Atomic Formulas", Machine Intelligence 5, 1970
- Sam Lindley, "Extensional Rewriting with Sums", TLCA 2007
- Gabriel Scherer, "Deciding Equivalence with Sums and the Empty Type", POPL 2017, https://arxiv.org/abs/1610.01213
- Sarah Winkler, Georg Moser, "MædMax: A Maximal Ordered Completion Tool", IJCAR 2018 (the external completion tool to revisit, section 1)
- René Thiemann, Christian Sternagel, "Certification of Termination Proofs Using CeTA", TPHOLs 2009 (certificates, if a later review asks for them)
