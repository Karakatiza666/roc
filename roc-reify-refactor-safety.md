# Reification and the safe refactor

The objection:

If we did incorporate reification, it would mean there would be no such thing as a
safe refactor in the language anymore; any change to any AST node, even just
reordering two unrelated constants, could break the entire program.

This document takes the objection as correct against the design as written,
states it precisely, shows where the prototype already exhibits it, checks
every alternative design against it, and describes the one shape of the feature
that answers it. It edits no other document; section 6 lists what
`roc-reify-proposal.md` would have to change.

---

## 1. The objection, stated precisely

A safe refactor is a change that preserves meaning: rename a local, reorder
two independent bindings, extract a helper, inline one, replace `a and b` with
the `if` it means. Roc programmers make these changes without reading every
caller, because nothing in the language can tell the two versions apart.

Reification is a function from a body's syntax to a value. Once a program can
observe syntax, two bodies that mean the same thing but are written differently
are no longer interchangeable, and every refactor becomes a potential change of
behavior somewhere else.

This is a known result, not a matter of taste. Mitchell Wand, "The Theory of
Fexprs is Trivial" (1998), proves that in a calculus where a program can reify
its operands, contextual equivalence collapses to alpha-equivalence: the only
terms interchangeable in every context are those identical up to renaming.
The creator's sentence is that theorem in plain words, and the "reordering two
unrelated constants" example is one of the equivalences it says are lost.

Three features of the current design make the collapse reach the whole
program, not only the reified function:

| Feature | Where | Consequence |
|---|---|---|
| The description is transitive | every callee the root reaches is described, across modules and packages, "even one the described module never imports" (`roc-reify-proposal.md:1150-1156`) | a refactor inside a dependency changes what your translator reads |
| The description keeps syntax | local names "as the author wrote them" (`roc-reify-proposal.md:115-119`); a region on every node (`src/build/roc/Builtin.roc:22687`); `Let` nesting in written order | renaming, moving or reordering code changes the value |
| Reification is invisible at the definition | S1 reifies any statically visible function named at a `Code` position (`roc-reify-proposal.md`, section 3) | the author of a helper cannot know a translator reads it |

Proposal 7.2 claims reification "cannot change what the program means" and that
a reader need not know it happened. Both claims hold for the reified function's
own run-time behavior and fail for the translator's output, which is part of
the program's meaning.

---

## 2. What each refactor does today

| Refactor, meaning preserved | Effect on the description | Effect on the program |
|---|---|---|
| Rename a local | `Local("wave")` becomes `Local("ripple")` | GLSL text changes: the translator emits the Roc name (`examples/reifying/glsl/Glsl.roc:241`) |
| Reorder two independent bindings | `Let` nesting changes | emitted statements reorder; golden tests and any cache keyed on output bytes change |
| Reorder two calls to one generic function | row serials `Test.id` and `Test.id#1` swap, because they count in walk order (`roc-reify-design.md:163`) | a translator that names emitted functions after rows swaps them |
| Move code, add a comment | every region after the edit shifts | a translator that embeds locations in output changes |
| Extract a helper | a `Call` and a new row appear | a translator that refuses calls, or a GLSL translator that emits one expression, now refuses the build |
| Inline a helper | a row disappears | the reverse |
| `x.len() > 0` to `!x.is_empty()` | a different callee name | a translator that knows `len` and not `is_empty` refuses the build |
| Fold to a `for` loop with a `var` | `Call` of the fold becomes `Ir.For` | the GLSL translator refuses loops (`examples/reifying/glsl/Glsl.roc:375`) |
| Same refactor inside a dependency | same, transitively | your build breaks on a dependency upgrade that changed no signature |

Every row is a meaning-preserving edit. Four of them break the build, and the
rest change the output. Nothing is silent in the sense of a wrong answer at run
time, because translation happens during `roc build`. But the break lands at
the `Code` site, which can be in another module or another package than the
edit.

---

## 3. How the alternative designs fare

The alternatives in `roc-reify-fold-alternative.md` and
`roc-reify-whole-design-alternatives.md` differ sharply on this axis, and the
DSL route of proposal 7.1 is the baseline.

| Design | What a translator can observe | Refactor safety |
|---|---|---|
| DSL over static dispatch (proposal 7.1) | a value of type `Sym` | safe: a refactor of the code that builds a `Sym` preserves the value, and values are compared by content |
| Tracing (virtualized syntax, `roc-reify-prior-art-survey.md` section 4.1) | what the body does to symbolic inputs | safe up to sharing: a trace records behavior, not spelling |
| Current proposal | syntax, names, regions, order, row identities | unsafe, as section 2 shows |
| Fold alternative | the same syntax, one method call per construct | unsafe; the footprint check makes the break earlier, not rarer |
| D1 second backend | the lowered program | safer against surface refactors, which lowering erases, and unsafe against compiler upgrades, which change lowering |
| D2 primitive cut | a dataflow graph over the translator's primitives, all else inlined | mostly safe: helper boundaries, local names and binding order disappear in the graph |
| D3 code is data | syntax, reflected at run time | unsafe, and breaks can move to run time |
| D4 typed boundary | syntax, with a row in the type | unsafe, but every break is a type error with a stated cause |
| D5 categories | a combinator term | safe against names and order; unsafe against the shape of the term |

The pattern is the finding. The designs that are safe are the ones whose
observation is extensional: they see what a body does, not how it is written.
The DSL and tracing are safe for exactly the reason the proposal set them
aside: a DSL term is a value, not a description of code.

---

## 4. The answer: observe a quotient, not the syntax

Wand's theorem applies when the observer sees syntax. It does not apply when the
observer sees syntax modulo a declared set of equations. Dhall is built on this:
it normalizes every expression and hashes the alpha-beta-normal form, so a
refactor that preserves the normal form preserves the hash, and the language
states which refactors those are. The response to the objection has three parts.

### 4.1 Declare the safe refactors

Roc publishes a set R of meaning-preserving refactors that reification
guarantees not to observe. The candidates, with how a normal form absorbs each:

| Refactor in R | How the normal form is invariant under it |
|---|---|
| rename a local or a parameter | binders are positional; names are not in the value |
| reorder independent bindings | the body is a dataflow graph with a canonical order, not a list |
| bind a value once or write it twice | the graph is hash-consed, so sharing is canonical |
| drop a binding nothing reads | dead nodes are removed |
| extract or inline a non-recursive helper | non-recursive callees are inlined |
| destructure or read fields | both are projections |
| `and`, `or` and the `if` they mean | one form |
| `?`, `??`, early `return` and the `match` they mean | one form |
| move code, reformat, comment | regions are not in the value |
| add or remove a type annotation | solved types are the same |
| reorder unrelated top-level definitions | recursive rows are keyed by content hash, not by name or walk order |

This is D2's graph with the primitive cut set to the builtins, which is why D2
came out mostly safe in section 3. The normal form is roughly what tracing
would record, reached without symbolic values, and it keeps structured control
where tracing cannot.

### 4.2 Make the quotient the only thing a translator can see

The description becomes opaque. Its accessors return the normal form only:

```roc
Code(fn) :: Code.Graph.{
	graph : Code(fn) -> Code.Graph               # the normal form, nothing else
	refuse_at : Code(fn), Code.Node, Str -> Code.Refusal
}
```

A translator never reads a name or a region, so it cannot branch on one. When it
refuses a node, `refuse_at` hands the node back to the compiler, which reports
it at every source region that normal form node came from. Names a translator
emits are its own (`v0`, `v1`). Names that are API stay visible, because they
live in types: the record field `fragTexCoord` that becomes a GLSL `in` is part
of the parameter's type, and renaming a field is already a breaking change in
Roc today, for derived codecs as much as for this.

The guarantee becomes testable: for every refactor in R, the normal form is
identical, so every translator's output is byte-identical. This suits the fuzzer
rule in `AGENTS.md`: generate small typed bodies, apply random refactors from
R, and assert equal normal forms.

### 4.3 Bound how far observation reaches

Inlining makes helpers invisible, but a recursive callee stays a row, and a
callee's body still determines the graph. The remaining exposure is a
dependency's implementation. Two precedents treat a body as interface
explicitly: Swift's `@inlinable` puts a function's body into its module's public
interface, and Rust's `const fn` makes the body's const-evaluability a semver
promise. The same rule here:

| Callee | Described |
|---|---|
| in the same package | by its body, inlined into the normal form |
| a builtin | as a primitive, by identity and type; its body is never read |
| in another package, marked as exposing its body | by its body; changing the normal form of that body is a breaking change of that package |
| in another package, not marked | refused at the site, naming the callee |

Within a package, the author owns both sides: a refactor that changes the
normal form breaks their own build, in their own CI, beside the edit. Across
packages, only bodies their authors published are read, so a dependency upgrade
cannot break a translation unless the dependency's author changed something
they declared as API.

---

## 5. What stays unsafe, stated

The quotient cannot be complete: contextual equivalence is undecidable, so some
meaning-preserving refactors change the normal form.

| Refactor outside R | Why it stays out | Failure mode |
|---|---|---|
| `x * 2` to `x + x`, reassociating `(a + b) + c` | not an equivalence in Roc: integer `+` crashes on overflow, and float addition is not associative | output changes, and it should, because the target's arithmetic differs too |
| `x.len() > 0` to `!x.is_empty()` | two different builtins; proving them equal is a theorem about their bodies | a translator that lacks one refuses the build, at the site |
| a recursive function rewritten as a fold | different recursion structure | the same |
| a function read at a site starts to use a primitive the translator lacks | the operation genuinely changed | the same |

Every row fails loudly, at build time, on a refactor whose operations really
changed. Of the creator's example, the reordering is absorbed, and so is every
other rename, move and restructuring in R. What remains is changing which
operations run, which a reader of a translated context has reason to expect to
matter.

---

## 6. What the proposal would have to change

| Proposal item | Change |
|---|---|
| Rule 6, structural | from a planned `is_eq` over the description to the description itself being a normal form, with no names and no regions |
| Section 4, `Code.ir` exposes the expression | exposes the normal form; the syntax-shaped `Ir` is not public |
| 7.2, the macro comparison | withdraw "reader must know it happened: no" for callees; state R instead |
| 7.6, `Ir` stabilizes | the stable object is the normal form, which is smaller than `Ir` and does not grow with sugar |
| 13, reification across a module boundary | replace "the table spans modules" with the reach rule of section 4.3 |
| New: section on refactor safety | publish R, the reach rule and the section 5 table |

What it costs:

| Cost | Who pays |
|---|---|
| translators lose local names, so emitted GLSL is harder to debug | translator authors; mitigated by the compiler mapping nodes back to regions |
| translators lose helper boundaries, so no GLSL helper functions or SQL user-defined functions from non-recursive helpers | targets that want them |
| a normalizer and hash-consing inside the reifier | compiler authors |
| a marker for bodies exposed across packages | the language: one declaration form, new syntax or a header entry |
| S1 on a cross-package function without the marker is refused | users, who get a message naming the missing marker |

Status, after milestone M13 of `roc-reify-normalization-plan.md`: the
proposal makes these changes, in its sections 1, 3, 4, 7.2, 7.10 and 13.
The reach rule of 4.3 and its marker were replaced by the policy of
`roc-reify-normalization-plan.md` 1.9, so the last two rows of the cost table
are not paid:

| Item of 4.3 | What the prototype does instead |
|---|---|
| a body is read only within a package, or where its author exposed it | every body is read, in any package, except the functions in the translator's cut |
| a marker for bodies exposed across packages | none. The translator declares its cut with the item `code_primitives` of its type |
| a cross-package function without the marker is refused | it is walked; a dependency upgrade that changes its operations stops the build at the site |

---

## 7. Verdict

The objection is correct against the design as written, and the prototype
already shows it: renaming a local changes emitted GLSL, and row serials depend
on walk order. It is not a flaw in the implementation. It follows from letting a
program observe syntax, and Wand proved it.

The feature survives the objection only in the shape of section 4: translators
see a declared quotient of the body, never its spelling, and bodies are read
only within a package or where their authors published them. Without that, the
DSL of proposal 7.1 is the refactor-safe design, and it keeps its advantage for
that reason alone, whatever it costs in ergonomics.

---

## Sources

- Mitchell Wand, "The Theory of Fexprs is Trivial", Lisp and Symbolic Computation 10(3), 1998
- Dhall semantic integrity checks: [dhall-lang standard, integrity checks](https://github.com/dhall-lang/dhall-lang/blob/master/standard/README.md)
- Swift `@inlinable`: [SE-0193 Cross-module inlining and specialization](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0193-cross-module-inlining-and-specialization.md)
- Rust `const fn` and semver: [Cargo SemVer compatibility](https://doc.rust-lang.org/cargo/reference/semver.html)
