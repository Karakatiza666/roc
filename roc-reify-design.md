# Code reification: the pure-function surface a description covers

A translator is a compiler written in ordinary Roc that runs during `roc build`.
It receives a `Code(f)`: a reified, typed, closed, monomorphic description of a
pure Roc function, shaped like the `Ir`, `Ty`, `Lit` and `Pattern` unions
declared in `src/build/roc/Builtin.roc:23625`.

This file is the checklist for that surface. Every box is a feature of pure Roc
that a description could carry. A ticked box is one the compiler carries today.

Effects stay out of scope by design. An effectful function, `dbg`, a hosted
lambda and `x!` are refused, and nothing here proposes describing them.

A construct a target cannot run is still described, because a named node costs
one translator a rejection, and a refusal costs every author the construct.

**Legend**

- `[x]` the compiler describes it, proven by a probe or a test
- `[ ]` the compiler refuses it, and the quoted text is the diagnostic's own
  reason line, or, where the box says so, the compiler panics on it: a defect
  rather than a designed refusal

---

## 1 Literals

- [x] Integer literal of every width, in decimal, `0x`, `0o` and `0b`, with or
      without a type suffix. Reified as `Lit.Int(I128, Ty)`.
- [x] Fractional literal at `F32` and `F64`. `Lit.Frac(F64, Ty)`.
- [x] `Dec` literal. `Lit.Fixed(Dec)`.
- [x] String literal of one segment. `Lit.Str(Str)`.
- [x] `Bool.True` and `Bool.False`, as `Lit.Bool`. Bool is the one tag union
      with a literal, because a translator emitting a boolean wants the value
      rather than the two tags Roc represents it with
      (`src/check/code_reifier.zig:5783`).
- [x] String interpolation, and any string of more than one segment. The
      checker leaves the segments flat, text and value alternating, and every
      one is a `Str`, so the literal describes as the concatenation it is: one
      `Builtin.Str.concat` per join, under the name a written `a.concat(b)`
      takes. A segment the author left empty joins nothing and is dropped, so
      `"${v}"` describes as `v` (`src/check/code_reifier.zig:6313`).
- [x] A literal of a type of your own, through `from_numeral` or `from_quote`.
      The conversion the checker wrote is named, and the number or the text
      the author wrote stands as its one argument, because the `Num.Numeral`
      it declares is an opaque a translator has no reason to model
      (`src/check/code_reifier.zig:6400`). A numeral names no width, so it
      takes the widest form `Lit` holds, `I128` or `F64`
      (`src/check/code_reifier.zig:6573`): a fractional one rounds to `F64`
      where the author's `from_numeral` would have seen exact digits.
- [ ] A literal of a type of your own through `from_interpolation`. "a custom
      string interpolation". The conversion runs in two stages (design.md,
      "An interpolated string literal converts in two stages"):
      `from_interpolation` reads the segments while the compiler runs and
      hands back an assembler, and the value is that assembler applied to the
      interpolated values. The assembler is a function value the compiler
      computes, and the `Ir` is first order, so no node can apply it.
- [x] A literal of a type of your own in a `match` pattern.
      `Code.Pattern.PatGuard(Pattern, Ir, Meta)`: the pattern binds the matched
      value and the condition beside it is that type's equality against its
      conversion of the literal, which is the form the checker already wrote
      it in (`src/check/code_reifier.zig:6064`).
- [x] An embedded file. One imported as `List(U8)` describes as
      `Code.Lit.Bytes(List(U8))`, a single literal holding the blob rather than
      one `Int` node per byte, because a file is as large as it is
      (`src/check/code_reifier.zig:1515`). One imported as `Str` describes as a
      `Str` literal, through the same arm any text literal takes.

## 2 Names a body may read

- [x] A parameter of the reified lambda. `Ir.Param(Str, Meta)`.
- [x] A binding the body introduced. `Ir.Let(Str, Ir, Ir, Meta)` and
      `Ir.Local(Str, Meta)`.
- [x] An argument the template call fixed, read as the literal it was called
      with rather than as a name (`Binding.Kind.constant`).
- [x] A top-level value of this module or of one it imports, written as a
      literal or as a record, tuple, list, tag or nominal built from literals,
      folded into the description as the value it holds
      (`src/check/code_reifier.zig:2194`).
- [x] A top-level value that has to be computed, `limit = 7.0 * 2.0` or
      `limit = xs.len()`, of this module or of one in its package. It is not
      evaluated first: its definition names only things the compiler fixes,
      so the walk builds that definition where the name stands, by the same
      path that folds a literal (`src/check/code_reifier.zig:2194`).
      `x > limit` describes as `x > 7.0 * 2.0`, and a constant the definition
      reads folds in turn, so `List.len([1, 2, 3])` stands where `limit` did.
      The order of compile-time evaluation does not change, and two sites
      that read different constants describe differently. Two cases stay
      refused. A computed value of another package is a body of that package,
      which the walk does not read (N8h): "a computed constant of another
      package". A top-level value that computes a function names no
      definition, so a call on it has no row to name: "a top-level constant
      that computes a function" (`src/check/code_reifier.zig:4010`).
- [x] A value the block around a lambda written at a `Code` position binds,
      read by that lambda. The statement that bound it is replayed at the head
      of the lambda's body, so it describes as a `Let` and a read of it as a
      `Local` (`src/check/code_reifier.zig:7189`), and a statement the lambda
      does not read stays out. A function the block binds is lifted into a row
      that takes what it captured first. A `Let` is the one reading that holds
      everywhere: the site's `f` leaves no room for an added parameter, and
      folding the value needs a constant the compiler evaluated, which a block
      is only inside a top-level constant. A translator that wants the value
      computed once hoists the `Let`.
- [ ] A name the compiler does not fix: a function parameter, a branch or loop
      binder, or a `var`, whether the lambda reads it or a replayed statement
      does. Refused as a capture, naming it
      (`src/check/code_reifier.zig:4242`).

## 3 Operators

- [x] `+`, `-`, `*`, `/`, `//`, `%`. `Ir.Binop` named `plus`, `minus`, `times`,
      `div_by`, `div_trunc_by`, `rem_by`.
- [x] `==`. `Binop` named `is_eq`.
- [x] `!=`. `Ir.Unary("not", ...)` over that `Binop`, whether the type derives
      its `is_eq` or writes it. Which of the two the author wrote rides on the
      dispatch plan (`src/check/code_reifier.zig:1549`).
- [x] `<`, `<=`, `>`, `>=`. `Binop` named `is_lt`, `is_lte`, `is_gt`, `is_gte`.
- [x] Prefix `-`. `Ir.Unary("neg", ...)`.
- [x] `and` and `or`, as the `If` the compiler turns each into: `a and b` is
      `If(a, b, Lit(Bool(False)))`. Both short-circuit, and an `If` is what
      short-circuiting is.
- [x] `x |> f(y)`, which is a plain call and describes as one.
- [x] Prefix `!`. `Ir.Unary("not", ...)`. `!x` arrives as a plain call to
      `Bool.not`, which the walk folds rather than follows
      (`src/check/code_reifier.zig:2964`), so `!b`, `Bool.not(b)` and `b.not()`
      all describe as the one node.
- [x] `a..<b` and `a..=b`, as `Ir.Range(Ir, Ir, [Exclusive, Inclusive], Meta)`.
      A range reaches the walk as the call the checker resolved it to,
      `Num.U16.range_exclusive_to`, so the fold is on the method name
      (`src/check/code_reifier.zig:3661`), the way `Bool.not` is.
- [x] `x ?? default`. It desugars to a `match` whose `Ok` branch binds a name
      the compiler made up, and the walk gives that binder one of its own
      (`src/check/code_reifier.zig:6904`).
- [x] `x?` and `x ? Tag`. The same desugaring, with the `Err` branch
      returning early, so it describes through the same rewrite an early
      `return` does: the `match` goes outside the binding, the `Ok` branch
      holds it, and the `Err` branch is the value the function hands back
      (`src/check/code_reifier.zig:4873`). One written inside an expression
      lifts the `match` out past that expression, which leaves no transfer in
      it at all (`src/check/code_reifier.zig:5212`).

## 4 Calls

- [x] Static dispatch, `x.f(y)`, reified as `Ir.Call(Str, List(Ir), Meta)` named
      by its fully qualified callee, such as `Num.F32.sin`. The translator decides
      what the call means in its target.
- [x] An operator method, carried as `Binop` or `Unary` instead of `Call`.
- [x] A plain call to a named function of the module being described, `f(x)`,
      as the same `Ir.Call(Str, List(Ir), Meta)` a static dispatch produces
      (`src/check/code_reifier.zig:2406`). The callee is named and the walk
      stops there, so the structure the author wrote survives into the target.
      A callee the walk cannot describe refuses the whole site, because a
      translator would otherwise meet a `Call` with no row. The report points
      at the call in the caller, not at the construct inside the callee that
      stopped the walk; a frame per hop would fix that.
      The name is module-qualified, `Shader.step`, because one table holds the
      definitions of every module a description reaches. Naming the callee
      rather than writing its body into the description is also what lets a
      recursive function describe at all.
- [x] The callee's own description, beside the root in `Code.definitions`, so
      a translator resolves each `Call` against a table the compiler wrote
      rather than one the user assembled by hand
      (`src/check/code_reifier.zig:3569`). A method call writes a row too: the
      instantiation edge names the target, whether the plan carries it or the
      caller's evidence does (`src/check/code_reifier.zig:3732`). A method
      whose body the walk cannot describe keeps its bare name instead, the way
      a builtin does, so a target primitive with a Roc body that stands in for
      it on the CPU is named rather than refused
      (`src/check/code_reifier.zig:3698`). A definition is described once
      however many calls reach it, and its row comes before its caller's, so a
      target that declares before it calls emits the table in order. The
      described function is a row of its own table only when it calls itself,
      which is the one description whose `Call` names it. A `Call` carries no
      tag saying what kind of callee it names: a name has a row in the table
      or it does not, and a tag beside that would make "resolved, with no
      row" representable.
- [x] A call to a function in another module, `Helper.f(x)`, described from
      that module's published view and named by it
      (`src/check/code_reifier.zig:2946`). The binding the checker resolved
      names the artifact rather than the import it came through, so the table
      also reaches a module the described one never imports: a callee's own
      callee, two modules away. A cached build still rebuilds the description
      when that module changes: an artifact key hashes its imports' keys, and
      the call graph is a subgraph of the import graph, because a call resolves
      only where the checker resolved a reference.
- [x] A call to a function the compiler provides. The builtin is named by its
      export name and no row is written for it, because its body is the
      compiler's and a translator resolves the name against what its own
      target provides (`src/check/code_reifier.zig:2900`). A method call on
      the same builtin reads that same name
      (`src/check/code_reifier.zig:3882`), so `Str.concat(a, b)` and
      `a.concat(b)` are one `Call` under one name. A builtin the `Ir` does
      carry a node for is folded into that node instead: `Bool.not` is
      `Unary("not", ...)` however it is spelled.
- [x] A call to a generic function. The callee's body reads differently at each
      instantiation, so the walk describes one row per instantiation: the
      template's own function type read against the type of this exact use
      gives what each quantified variable was fixed to
      (`src/check/code_reifier.zig:3080`), and the row is keyed by a digest of
      those types. `id` called at `F32` and at `U64` is two rows, `Test.id` and
      `Test.id#1`: the walk counts rows per name and every row after the first
      takes its count as a serial (`src/check/code_reifier.zig:2754`). A
      variable the call does not fix is refused as "a call to a generic
      function this call does not fix", except a row variable, which a call
      may leave unbound because no description names a row
      (`src/check/code_reifier.zig:3171`).
- [x] A call to a function written inside another function, lifted into a row
      of its own (`src/check/code_reifier.zig:2856`). The binding leaves no
      `Let` behind, because the `Ir` is first order. What the lambda captured
      arrives as a leading parameter and every call site passes it first
      (`src/check/code_reifier.zig:1195`); captures are lexical, so every call
      sits in the scope that holds them. Two functions can each write one
      called `step`, and the second of them takes the serial. A local the
      checker generalized describes at the type each call fixes, a row per
      type (`src/check/code_reifier.zig:2881`).
- [x] A type-qualified call, `Type.f(x)`, which resolves to the same dispatch
      plan a value dispatch leaves behind, so the two describe through one arm
      (`src/check/code_reifier.zig:1442`). The name is the plan's dispatcher
      read under the active substitution, so `Shape.f(x)` inside a
      `where`-constrained body is named by the type the call fixed `Shape` to.
- [x] Calling a parameter or a binding that holds a function. The `Ir` has no
      node for applying an expression, so the walk resolves the function at the
      site that fixes it, the way a call fixes a generic callee's type
      variables. A function argument binds the callee's parameter to the
      definition it names, and the row is keyed by that as well as by the types
      (`src/check/code_reifier.zig:2527`): `apply_to(double, x)` and
      `apply_to(triple, x)` are two rows. A definition that hands back a
      function and the use that runs it are one flattened row and one `Call`
      (`src/check/code_reifier.zig:2354`), which is how a hand-written
      `encoder_for` is run. A name bound to a function and then read rather
      than run is still refused as "a reference to a function value".
      Only a plain call specializes: a lambda handed to a dispatch stays a
      `Lambda` node in the call's arguments, which is what a derived `map` and
      a builtin `map` both want.
- [x] A call through an exact alias, `same_thing = add_one`. The checker
      records the lookup an alias forwards to (`forwarded_lookup`,
      `src/check/checked_artifact.zig:17173`), and the walk follows it to the
      procedure it names (`src/check/code_reifier.zig:4066`, `:4110`), so the
      call is a `Call` of that procedure's row and the alias and the name
      share one row. An alias another module exports is followed the same way
      through its export row (`src/check/code_reifier.zig:4086`). An alias of
      a computed function, `f = make(2)`, has no forwarded lookup and stays
      refused as "a top-level constant that computes a function". Pinned by
      `eval_staging_tests.zig` ("staging - a call through an alias ...") and
      `code_reifier_test.zig:531`.
- [x] A function chosen by an `if`, or read out of a record literal, and then
      called: `(if c double else triple)(x)`. The callee names no definition,
      so the call is an `Apply` of the value (`src/check/code_reifier.zig:393`,
      N8i), and simplifying turns each `Apply` whose function is a known
      closure into a `Call` of its row. Checked with a probe of each form.
- [ ] A function taken from a list and then called, `Ok(g) => g(x)` in a
      `match` on `[double].first()`. "a call to a function value that no
      simplification resolves" (`src/reify/driver.zig:116`): simplifying does
      not read a closure back out of a list, so the `Apply` stays.

## 5 Control flow

- [x] `if`, `else if` and `else`, at any depth. `Ir.If(Ir, Ir, Ir, Meta)`.
- [x] `match`, as `Ir.Match(Ir, List(Branch), Meta)` with its branches in the
      order they were written, each carrying its patterns, its `if` guard and
      its value (`src/check/code_reifier.zig:5801`).
- [x] A branch written `A | B =>`, as a branch with a pattern per alternative.
- [x] A branch guard, as `Branch.guard`.
- [x] `for` and `while`, each as the fold it is: `Ir.For` and `Ir.While` carry
      the state the loop takes from one turn to the next, which is whatever
      `var`s the body assigns (`src/check/code_reifier.zig:4606`). `carried`
      names one entry per such `var`, so a turn writes what the author wrote.
      A loop that assigns none carries none, and matters for what leaves it.
- [x] `while Bool.True { .. }`, which reaches the walk as a form of its own
      and carries what a `while` carries, so the three share one call
      (`src/check/code_reifier.zig:4289`).
- [x] `break`, and a `return` that crosses a loop, as `Ir.Break(Ir, Meta)` and
      `Ir.Return(Ir, Meta)` (`src/check/code_reifier.zig:4330`). These are the
      two whose continuation is the turns of the loop that have not run, which
      no branch says. Each carries what the author wrote, so a target with its
      own `break` emits one and a target that folds lowers them itself. A
      `[Continue, Break]` step result would instead pick the fold lowering for
      every target, and a `return` in a loop would put the statements after it
      under a `Match` an imperative target has to read as "already returned".
- [x] `return` as an early exit, rewritten into the shape the body already
      has: a branch that returns hands its value back, and a branch that does
      not runs the statements written after it
      (`src/check/code_reifier.zig:4873`). That rewrite is what lets a target
      with no loops at all, SQL or a query plan, take `return` and `x?` while
      never meeting a control-flow node.
- [x] A `return` written inside an expression, `Ok(t? * 2.0)`, by lifting the
      branching construct out past the expression that holds it
      (`src/check/code_reifier.zig:5212`). What is left has no transfer in it,
      so the walk does this once rather than every translator doing it.
- [x] `crash`, as `Ir.Crash(Ir, Meta)` (`src/check/code_reifier.zig:1536`). The
      message is an `Ir` rather than a `Str`, so an interpolated one arrives as
      the concatenation the checker made of it. A `crash` followed by more
      statements is a discarded statement and stays refused; one written as a
      branch value or as the last thing in a block is an expression and
      describes.
- [x] `expect` inside a body. It asserts and hands back nothing, so the
      description passes over it the way it passes over a type annotation
      (`src/check/code_reifier.zig:4269`). A translator emits a target, and an
      assertion written for Roc's own test run has no place in one.

## 6 Bindings and blocks

- [x] A block body with `let` bindings and a final expression, reified as
      nested `Let` nodes rather than inlined, so a binding written once stays
      written once. Losing it is a defect in the output, not only in the
      ergonomics: the same shader built by evaluation carries four texture
      fetches where the source writes one
      (`examples/reifying/shaders-without-reifying/main.roc:18`).
- [x] A binding whose value is any describable expression.
- [x] A destructuring binding, `{ a, b } = r`, expanded into the reads it
      stands for: one `Let` per name, reading a `Field` or an `Index`
      (`src/check/code_reifier.zig:5592`). A translator that has records and
      locals emits this without also having pattern matching. A pattern that
      names a variant is a test as well as a binding, so that one stays the
      one-branch `match` it is.
- [x] A parameter written as a pattern, `|(a, _), b|` or `|{ a, b }|`, as a
      parameter under a name of its own whose reads wrap the body, the same
      reads a destructuring binding takes (`src/check/code_reifier.zig:7054`).
      `_` binds nothing and reads nothing. A lambda passed to a definition is
      lifted into a row named after the first name its patterns bind, and
      `Module.lambda` when they bind none.
- [x] A `var`, and any reassignment to one, as versions rather than as
      mutation: `$x`, then `$x#1`, then `$x#2`
      (`src/check/code_reifier.zig:5356`). A `var` written in one branch and
      read after it is joined by hoisting the branch into the binding, and
      several `var`s travel through one join as a tuple.
- [x] A type annotation or a type declaration inside a body, which names a type
      for the checker and leaves no value behind, so the description passes
      over it (`src/check/code_reifier.zig:4259`).
- [ ] An `import` inside a body. The parser refuses one ("import must be top
      level") before the walk could meet it, so no body holds one to describe.
- [x] A statement whose value is discarded, as a binding nothing reads
      (`src/check/code_reifier.zig:4363`), which keeps both its order and
      whatever it diverges on. Two shapes of one are something else first,
      because both hand back what the statements after them need: a branch
      that transfers, and a branch that assigns a `var`.
- [x] A function bound inside a block, lifted into a row of its own rather
      than left as a `Let` holding a function
      (`src/check/code_reifier.zig:5284`). Naming one where a `Code` is
      expected describes by section 11.

## 7 Aggregates

- [x] Record literal with at least one field.
      `Ir.MakeRecord(List({ name : Str, value : Ir }), Meta)`.
- [x] Field access, at any depth. `Ir.Field(Ir, Str, Meta)`.
- [x] A record field with a default (`port : U16 ?? 8080`), read as an ordinary
      field.
- [x] Tuple literal. `Ir.MakeTuple(List(Ir), Meta)`.
- [x] A value used at a wider tag union than its own. There is no node for
      it. The checker writes a `row_coerce` (design.md, "Row Coercion
      Primitive") at each use of a top-level value, and around a call to a
      function whose body closed the union its annotation left open. The
      description identifies a tag by its name, so the value does not change
      when it moves to a wider union: a value of a narrower union conforms to
      a wider slot, with no node between. A tag switch has one arm per member
      of its scrutinee's own union. A call takes the type its site reads it
      at, and inlining builds the helper's ends at that type, so a helper
      gives the same description as the code written inline. A translator that
      matches tags by name needs nothing more. A translator that numbers tags
      per union, such as a C or GLSL struct, converts where the type of a
      child is narrower than the type of its slot
      (`src/build/roc/Builtin.roc:23930-23936`). See
      `roc-reify-tag-names.md`.
- [x] Tuple access, `t.0`. `Ir.Index(Ir, U64, Meta)`.
- [x] List literal with at least one item. `Ir.MakeList(List(Ir), Meta)`.
- [x] Indexing a list. `List.get` returns `Try(a, [OutOfBounds]*)`, and the
      checker closes that error union at the call, which the description
      follows (`src/check/code_reifier.zig:6571`).
- [x] An empty aggregate, `[]` or `{}`. `Ir.MakeList` and `Ir.MakeRecord` with
      nothing in them.
- [x] A nullary tag as the value a reified function hands back. Both this and
      the empty aggregate once panicked in LIR lowering, because a layout
      shared between two equal named types stopped at the name.
      `seedSharedLayouts` and `shareLayoutsAcrossEquivalence` now carry the
      shared layout to every type inside it
      (`src/postcheck/solved_lir_lower.zig:11156`, `:11238`), pinned by
      `src/eval/test/eval_staging_tests.zig:1777` and `:1783`.
- [x] Record update, `{ ..r, b: 1 }`, expanded into the `MakeRecord` it stands
      for: the fields the update wrote, and every other field of the type read
      out of the subject (`src/check/code_reifier.zig:6247`). The subject is
      bound first unless it already reads a name, because each field reads it
      again. One over a record with an optional field is refused: the result
      carries whatever the subject had there, and a `Field` read of a field
      that may be absent is not that.
- [x] An unset record field (`b: _`), left out of the entries. `MakeRecord`
      lists what the literal sets and the type beside it says the field may be
      absent, so `{ a: v, b: _ }` and `{ a: v }` describe alike because they
      build the same value.
- [x] An optional record field (`timeout ?: U64`), as the `presence` a
      `Ty.Record` entry carries (`src/check/code_reifier.zig:6844`) and
      `Ir.OptField(Ir, Str, Meta)` for the `.?timeout` that reads it
      (`src/check/code_reifier.zig:6253`). The read hands back the
      `Try(a, [MissingField])` the value sits in rather than the value, which
      is why it is a node of its own. A field read through a `.?` segment is
      refused: the checker gives such a path one flat `Try` however many
      optional segments it holds, and nested nodes cannot say that.

## 7b Patterns a `match` branch may test with

- [x] `x`, as `Pattern.Bind(Str, Meta)`, which is also what a branch value
      reads as a `Local`.
- [x] `_`, as `Pattern.Anything(Meta)`.
- [x] `Tag(p, q)` and a bare tag, as `Pattern.Variant(Str, List(Pattern), Meta)`
      (`src/check/code_reifier.zig:6031`).
- [x] `Bool.True` and `Bool.False`, as `Pattern.PatLit(Lit.Bool(..), Meta)`, the
      same split a Bool expression takes.
- [x] An integer, fractional, `Dec` or string literal, as `Pattern.PatLit`.
- [x] `(p, q)`, as `Pattern.PatTuple(List(Pattern), Meta)`.
- [x] `{ a, b: p }`, as `Pattern.PatRecord(List({ name, pattern }), Meta)`
      (`src/check/code_reifier.zig:5976`).
- [x] Reaching a tag union through a nominal, so `Ok(v)` on a `Try` is a
      `Variant` under the nominal's own `Ty`.
- [x] `p as name`. `Pattern.PatAs(Pattern, Str, Meta)`, so the name stays
      beside the pattern it renames rather than moving into the branch value.
- [x] A literal of a type of your own, as
      `Pattern.PatGuard(Pattern, Ir, Meta)`: the value bound, and that type's
      equality against its conversion of the literal. The condition sits on
      the alternative that owns it, which a branch's own guard cannot do
      (`src/check/code_reifier.zig:6064`).
- [x] `[p, q]` as `Pattern.PatList(List(Pattern), Meta)`, and `[p, .., q]` as
      `Pattern.PatListRest(List(Pattern), [Ignored, Named(Str)], List(Pattern), Meta)`
      (`src/check/code_reifier.zig:6019`). Two nodes rather than one carrying
      an optional rest, because a translator answers an exact length with a
      test and a rest with a slice.
- [x] `{ a, .. }`, as the entries beside the rest. A rest that binds nothing
      stands for the fields the pattern did not name, and naming none of them
      is what those entries already say. A rest that binds a name,
      `{ a, ..others }`, is refused: it binds a record the pattern builds out
      of what is left rather than one it takes apart, and `Pattern` names
      values a match takes apart.
- [x] A string interpolation pattern, as
      `Pattern.PatStr(Str, List({ capture : [Ignored, Named(Str)], delimiter : Str }), [Exact, Tail], Meta)`
      (`src/check/code_reifier.zig:6059`): the text the string starts with,
      one step per interpolation, and whether the last delimiter ends the
      string. A target that cannot split a string rejects the node by name.

## 8 Nominal and opaque types

- [x] A transparent nominal as a parameter or a result. `Ty.Named(Str, Ty)`,
      keeping the name over its backing shape.
- [x] Constructing one, `Vec2.({ x: x, y: 0.0 })`, which describes as the
      backing it wraps under the nominal's own name.
- [x] Reading a field through one.
- [x] An opaque nominal, and a builtin with no shape in the `Ir` (`Dict`, `Set`,
      `Box`, `Iter`, `Try`, the SIMD vectors), carried by name as
      `Ty.Opaque(Str, List(Ty))` so a translator that owns the type recognises it and
      every other translator refuses it by name.
- [x] A nominal whose backing is a tag union, as `Ty.Named` over
      `Ty.TagUnion`, including one whose union reaches the nominal again.
- [x] A recursive nominal, as `Ty.Named` whose backing carries `Ty.Recursive`
      naming it at each point it reaches back
      (`src/check/code_reifier.zig:6795`). Mutual recursion describes the same
      way, each nominal named by the `Named` that encloses it.
- [x] A recursive nominal with a type parameter, such as a tree or a linked
      list. A declaration's backing is one template every use shares, so what
      is open is the nominal at the arguments this use fixed rather than the
      checked id the use carries.
- [ ] Reading inside an opaque nominal, which Roc itself forbids from outside
      the defining module.
- [x] A transparent nominal with a type parameter, read at the type arguments
      the use fixed (`src/check/code_reifier.zig:6711`). The backing arrives as
      the template it was declared with, so the walk binds the nominal's
      declared variables to `args` for the span of that backing, the way a call
      binds a callee's quantified variables for the span of its body. `Box(F32)`
      and `Box(Str)` are two `Ty` values over one template. `Named(Str, Ty)`
      keeps the backing read at those arguments and drops the arguments
      themselves, where `Opaque` keeps the arguments and has no backing.

## 9 Types a reified signature may name

- [x] `I8` through `I128`, `U8` through `U128`, `F32`, `F64`, `Dec`, `Bool`,
      `Str` (`src/check/code_reifier.zig:7433`).
- [x] `List(a)`, as `Ty.ListOf(Ty)`.
- [x] A record type, as
      `Ty.Record(List({ name : Str, ty : Ty, presence : [Required, Optional] }))`.
      A field with a default is `Required`, because the default fills it in
      and every value of the type carries it. So is one whose presence the
      checker never pinned, which is what the checker itself commits such a
      field to. Entries arrive in the order the extension chain holds them,
      neither source nor alphabetical (`src/check/code_reifier.zig:6976`), so a
      translator that needs a fixed order sorts them.
- [x] A tuple type, as `Ty.Tuple(List(Ty))`.
- [x] A pure function type, as `Ty.Fn(List(Ty), Ty)`.
- [x] A type alias, resolved to the type it names.
- [x] A tag union, empty or otherwise, as
      `Ty.TagUnion(List({ name : Str, payloads : List(Ty) }))`
      (`src/check/code_reifier.zig:6571`). A union a nominal declares keeps its
      written order; one the solver built arrives in name order.
- [x] A tag union whose row the checker closed. Closing a row leaves the
      variable it solved in place, marked with the default it closed to, so
      the walk reads the mark rather than the extension's kind
      (`src/check/code_reifier.zig:6624`).
- [x] A reference back to an enclosing nominal, as `Ty.Recursive(Str)`. A
      translator resolves the name against the `Ty.Named` nodes it is inside,
      innermost first, which is the only reading: Roc refuses a recursive type
      alias, so every recursion is a nominal, and a nominal that reaches itself
      at other type arguments gets a `Named` of its own at those arguments, so
      one nominal never has two live instantiations nested inside each other.
- [x] A type variable the site fixes. The root is described at the types the
      site's `Code(f)` gives it, the way a callee is described at the types its
      call gives it: `rootSiteNode` matches the root's scheme against that `f`
      and hands `describeDefinition` the substitution
      (`src/check/code_reifier.zig:696`), so `twin : a -> (a, a)` named at
      `Code(Str -> (Str, Str))` describes with `a` at `Str`. A variable `f`
      does not reach is still refused (`src/check/code_reifier.zig:6640`), and
      so is a literal whose type only the method it feeds fixes: unannotated,
      `double = |x| x * 2` at a `U16` site leaves the literal open, because
      matching fixes the signature's variables and not the one `times` would.
      An annotation fixes both. The description takes the type the site holds
      when this module finishes checking, so narrowing that arrives from a
      later module does not reach it.
      Where a site widens a row the description carries the definition's own
      row, which is the row the function returns; `f`'s extra variants are what
      the consumer accepts.
- [x] A `where` constrained type variable. A constraint is no shape of its own:
      the site fixes the variable the way it fixes any other, and the
      description names what it was fixed to, in a parameter and in a result
      alike. `doubled : a -> U16 where [a.size : a -> U16]` at
      `Code(Meters -> U16)` describes `Meters -> U16`, and the method the body
      dispatches is named `Meters.size`. The reifier holds no refusal of its
      own for a constraint: a constrained variable no site fixes is refused as
      a type variable, above.
- [x] A row a sibling argument or a later clause fixes. A site's rows close
      when the binding holding it generalizes (`src/check/Check.zig:43017`),
      not when the site finishes, so `join(orders, |c, o| ..)` takes its row
      from `orders`, and a second clause reading the same parameter record
      adds the fields it reads. A row nothing else fixes closes on exactly
      the fields the lambda reads.
- [x] An open record, or a record extended by a variable. A row is a quantified
      variable, so a site fixes it the way it fixes any other. `matchRecord`
      binds the row to the record the site named
      (`src/check/code_reifier.zig:3297`) and the walk reads that binding where
      an extension chain ends in a variable
      (`src/check/code_reifier.zig:6974`), so
      `take_n : { n : U16, ..rest } -> U16` at `Code({ n : U16, m : U16 } -> U16)`
      describes its parameter as `{ n : U16, m : U16 }`, and the same
      definition at `Code({ n : U16 } -> U16)` describes it as `{ n : U16 }`,
      in a row of its own. A site's own `f` closes its rows before the walk
      reads them (`src/check/Check.zig:43044`), so the "open record" refusal
      below is a guard that no `Code` position reaches. What the row binds to
      is the site's whole record
      rather than the fields the definition did not name, because the residual
      is no type the artifact holds; the two sets are the same once a field a
      nearer link already collected is dropped
      (`src/check/code_reifier.zig:6998`). A row nothing fixes is still refused
      as "an open record": `Ty.Record` is a closed list of fields, so a record
      with no fixed set of them has no shape to write.
- [ ] A tag union whose row is still open, so its extension is a variable the
      checker did not close. "an open tag union": the union stands for many,
      and a description is monomorphic.

      What closed the open record above does not close this one, and the
      position is the difference. A record's row reaches the walk through a
      parameter, where the site's type is the precise one: the value handed to
      the described function has every field the site named, so binding the
      site's row describes what the body receives. A union's row reaches it
      through a result, where the definition's variants are the precise ones
      and the site's are wider, so binding there would write a description
      claiming a body hands back variants it cannot build. What this box wants
      is the other move: drop the open tail and describe the variants the
      definition has, which is already the reading where a site widens a row
      the checker closed.

## 10 Derived methods

The six derivable methods are `is_eq`, `to_hash`, `parser_for`, `encoder_for`,
`map` and `map!`. `map!` is effectful, so it is out of scope.

What decides the treatment is who the result has to agree with. A method whose
result must agree with Roc's own, `is_eq` and `to_hash`, is expanded, because
that knowledge is the compiler's. A method that answers to a format the
translator owns, a codec or `to_inspect`, stays a `Derived` node.

- [x] Derived `is_eq`, expanded structurally into the comparisons it performs,
      over records, tuples and transparent nominals.
- [x] Derived `is_eq` over a tag union, expanded into the `match` that
      comparison is: the two operands paired, a branch per variant, and a `_`
      for every pair that disagrees on the variant
      (`src/check/code_reifier.zig:1711`). A payload is bound, because no `Ir`
      node reaches inside a variant, and the compiler names those binders
      `eq_lhs_N` and `eq_rhs_N`: it wrote the match, so no source holds a name
      for them.
- [x] Derived `to_hash`, expanded the same way when the description reaches far
      enough, and emitted as `Derived` when it does not.
- [x] `parser_for` and `encoder_for`, as one `Derived(method, subject, args,
      meta)` per codec. A constrained body names its own evidence param rather
      than a target, so the body alone reads the same whether the compiler
      derived the codec or the author wrote it. The call that fixed the type
      says which, and the walk already enters the body once per instantiation,
      so the evidence rides in beside the substitution
      (`src/check/code_reifier.zig:3484`, `src/check/code_reifier.zig:3738`).
      A codec is also curried: `encoder_for` hands back an encoder the body
      then runs, and applying a function value has no node. The two halves fold
      into one (`src/check/code_reifier.zig:2023`), constructor arguments
      first, so the binding that held the encoder leaves nothing behind
      (`src/check/code_reifier.zig:5284`). Both spellings fold:
      `enc = Shape.encoder_for(f)` then `enc(v, s)`, and
      `Shape.encoder_for(f)(v, s)` written straight through.
      Staying unexpanded is the design, because the wire format is the
      translator's to decide, not Roc's.
      A hand-written `encoder_for` returns a real closure, and a body that runs
      one describes as the `Call` a translator resolves against a row
      (`src/check/code_reifier.zig:2354`): both origins carry the same
      arguments in the same order, which is what lets one translator read
      either. Written the ergonomic way, `Json.to_str(value)` is still refused
      as "a call to a function the compiler provides".
- [ ] Derived `is_eq` over an empty tag union. "derived equality on an empty
      tag union": nothing inhabits it, so there is no pair of values to
      compare.
- [x] Derived `is_eq` or `to_hash` through a nominal component. The compiler
      dispatches to a component's own method before it looks at the component's
      representation, and a derivation carries no dispatch plan, so the walk
      resolves the method itself against the checked method registries
      (`src/check/code_reifier.zig:1615`). The registry says which of the two a
      declaration is: a procedure target is a written method, which describes
      as the `Call` it is with its body in the table, and a structural target
      is the compiler's recipe, which is the signal to expand the backing. A
      written method the walk cannot reach keeps the bare name, the way a
      dispatch to one does. A generic nominal's is described at the
      instantiation its receiver fixes: the method's first parameter is the
      value the derivation is walking, and pairing the two binds what the
      scheme quantifies by shape (`src/check/code_reifier.zig:3965`), so
      `Deep(U16)` and `Deep(Str)` take a row each.
- [x] Derived `is_eq` through a `List`, `Dict`, `Set` or `Try` component, as
      the `Call` the builtin's own method is. A scalar builtin folds into the
      `Binop` a translator wants, `Str` among them, and every other builtin
      goes to the registry like any nominal
      (`src/check/code_reifier.zig:1682`). The registry keys a compiler builtin
      under its own owner rather than under a declaration, so `ForeignNominal`
      carries that key (`src/check/code_reifier.zig:7755`); it is a plain enum,
      and so already means the same thing in either store. The walk stops at a
      builtin's body by rule, so the description is the export name and nothing
      more, which a translator resolves against its own target or rejects by
      name. `Box` never arrives, because the checker refuses `==` on one, and a
      derived `to_hash` over a container stays the symbolic `Derived` node the
      stage expands.
- [ ] Derived `is_eq` or `to_hash` through an opaque nominal that derives it.
      An opaque type's `Ty` names it without its backing
      (`src/check/code_reifier.zig:6671`), and the derivation is that backing's
      comparison, so expanding here would describe a representation the
      description hides everywhere else. One that writes its own method
      describes as the call, which hides it.
- [x] Derived `map`, as a `Derived(method, subject, args, meta)` carrying the
      value and the mapping function in that order. The mapping function is a
      `Lambda` like any other, and the subject is the parametric nominal read
      at the type arguments the use fixed
      (`src/check/code_reifier.zig:3982`), which is what says where the
      payload being mapped sits. Both halves were needed: the nominal alone
      refused as "a type variable" whether the mapping function was a lambda
      or a name.
- [x] `to_inspect`, reached through `Str.inspect`. The call is recognised by
      the intrinsic the checker recorded on the use
      (`src/check/code_reifier.zig:2544`). A subject whose `to_inspect` is the
      inspect override describes as that call, and every other subject as
      `Derived("to_inspect", subject, [value], meta)`, including a container
      inside a record (`src/check/code_reifier.zig:1726`). Only the plain-call
      path checks the intrinsic, so the method call `s.inspect()` still
      describes as `Call("Builtin.Str.inspect", [s])`. Making the two one node
      needs one more `ForeignLookup` question: the intrinsic an exported
      template wraps.

## 11 Where a reified definition may live

- [x] A top-level definition of the module that reifies it.
- [x] A top-level definition of a module it imports, read through that module's
      published view and its export table.
- [x] A definition reached through a type module (`Maker := {}.{ ... }`).
- [x] An exact alias named where a `Code` is expected, `count_rows(same_thing)`
      with `same_thing = add_one`, of this module or of one it imports. A
      named site holds no lookup in its checked body, so the walk goes from
      the name's pattern to its procedure binding through the top-level value
      table, and from an alias binding to the lookup it forwards to
      (`src/check/code_reifier.zig:6946`). The site describes the procedure
      that lookup names, byte for byte the description of naming it directly.
- [x] A function bound inside a block, named where a `Code` is expected. The
      checker records a name a block binds to a lambda
      (`src/check/Check.zig:24051`), and the walk follows the binder's defining
      statement to that lambda (`src/check/code_reifier.zig:8236`). The lambda
      reads the block around it by section 2, and one the block generalized
      describes at the type each site fixes. A name bound to anything else,
      `f = if c a else b`, has no body behind it and is refused.
- [ ] A function reached through a value, such as an item of a list of
      functions.
- [x] A lambda written where the `Code` is expected, `describe(|s| ...)`. The
      walk reads the lambda where it stands and the description takes its place,
      so nothing has to name it. What it reads from the block around it
      describes by section 2, and it may stand inside a function body as well
      as a top-level constant.

## 12 Templates: arguments fixed while the compiler runs

A function that returns a `Code` is a template. The compiler calls it, writes
the call's arguments into the lambda it returns, and the call site takes the
description, so one template describes as many bodies as it is called with.

- [x] A template defined in this module, recognised by its callee before either
      body is checked.
- [x] A template defined in a module this one imports. Its arguments are
      described here and its body there, two walks into one const store.
- [x] An integer, fractional, `Dec` or string literal as an argument.
- [x] A list, tuple or record argument, and a nominal wrapping one, so long as
      every part of it is itself constant.
- [x] A field read of a record argument, which describes as a `Field` over the
      `MakeRecord` the call fixed.
- [x] Several calls of one template, each producing its own description.
- [ ] An interpolated string as an argument, `labelled("a${"b"}c")`. The
      checker binds every interpolated value to a name, so it is refused as
      "template needs a constant" however constant its pieces are
      (`src/check/code_reifier.zig:961`).
- [ ] An argument computed while the program runs. Refused at the argument
      (`src/check/code_reifier.zig:1043`), with a report that points there rather
      than at the template.
- [x] A template whose argument is a function. The parameter binds to the
      definition the argument names (`src/check/code_reifier.zig:798`), so a
      call on it names that row, and a lambda argument lifts into a row that
      reads the block around it. The argument is a function rather than a
      `Code`: `Code(f)` is opaque and not callable, so a template calling a
      `Code` parameter does not check, and making it callable is a change to
      the typing rules. A function argument that names no definition, a
      record field or an `if`, stays refused.
- [x] A name as an argument, bound to a literal at the top level or in an
      imported module. The walk follows the name to the value it holds and
      folds that value in (`src/check/code_reifier.zig:1023`), so `limit = 7`
      passed to a template describes as the `7`.

## 13 What every node carries

`Code` is opaque, so only the compiler builds one. The node unions are
transparent, because a translator `match`es them from outside `Builtin`, and
opacity blocks matching as firmly as construction. Only `Code` is
auto-imported, so a user module may still be named `Pattern` or `Branch`.

- [x] `Meta { ty : Ty, region : Region }` on every `Ir` node, so a translator can
      name a type and point at source. `Meta` and `Region` are aliases rather
      than nominals, because restoring a compile-time constant refuses a
      nominal record (`src/postcheck/boxy/lower.zig:37440`).
- [x] A region counted in the file its author wrote, resolved to 1-based lines
      and columns, with the module name beside them. One `Str` node per
      distinct string, so a description holds one node naming its module and
      not one per node (`src/check/code_reifier.zig:7316`). A description
      another module's walk writes carries that module's regions, so a refusal
      names the file the author must open.
- [x] `Node.children` (the normal form of `Ir.children`) and `Ty.children`,
      so a pass with nothing to say about any one kind walks a description
      without an arm per kind (`src/build/roc/Builtin.roc:24004`, `:23703`).
- [x] `Ty.numeric`, the question an operation site asks about a number, and
      `Ty.name`, the answer a refusal names a type with
      (`src/build/roc/Builtin.roc:23727`, `:23752`).
- [x] Comparing two `Ty` values. `Code.Ty` declares `is_eq : _` and
      `to_hash : _` (`src/build/roc/Builtin.roc:23689`), so `a == b` and
      `a != b` are the derived structural comparison. Checked with a probe
      that compares the parameter types of a `I64, I64, F32 -> I64` row.

---

## What the remaining unticked boxes cost

| Gap | What it costs |
| --- | --- |
| No function taken from a list | `[double].first()` and then a call: simplifying does not read a closure back out of a list, so the call stays an `Apply` and the site is refused; a function chosen by an `if` or read from a record literal does describe |
| No name whose value exists only at run time | a lambda cannot read a parameter, binder or `var` of the function it is written in; the value becomes a parameter of the lambda, or a template fixes it |
| No computed function at top level | `doubler = make(2.0)` names no definition, so a call on it is refused; the author writes it as a lambda, `doubler = \|x\| x * 2.0`, or as a template; an exact alias, `same = add_one`, does describe |
| No computed value of another package | `limit = xs.len()` in a package the app depends on is refused, because its body is that package's; a value written as data still folds |
| No open tag union | a result whose row nothing closed has no one set of variants to describe |

A shader or a codec is written as one function calling others, over as many
modules as its author split it into, and that describes whole: the compiler
walks the callees and ships their descriptions in the table, and every builtin
either folds into a node or arrives under the name the compiler knows it by. A
higher-order call describes too, because the walk resolves a function at the
site that fixes it rather than handing a translator a value it has nowhere to
put.

## How each box was checked

A ticked box is proven by one of three things: a case in
`src/eval/test/eval_staging_tests.zig`, a fixture under `test/cli/`, or a probe
compiled with `roc <file>` where a translator prints `ok` for a `Lambda` root.
An unticked box quotes the reason line the compiler printed for the same probe.
The walk's trees are also pinned by `src/compile/test/code_reifier_test.zig`,
and the position rule's reports by snapshots such as
`test/snapshots/staged_code_outside_staged_position.md`. The reifier is checked
against Roc's semantics too: `Interp.eval` runs a description, and
`examples/reifying/glsl/main.roc:113` compares its answer with what Roc
computes for the same function.

Working on the reifier:

| Task | What to know |
| --- | --- |
| run the GLSL example | `roc test --no-cache examples/reifying/glsl/main.roc`; the CLI suite runs the same command (`src/cli/test/parallel_cli_runner.zig:1875`) |
| a call into another module or a builtin | `code_reifier_test.zig` builds its walk with `ForeignLookup.none` (line 112), so those paths refuse there and are pinned only in `eval_staging_tests.zig` |
| a `Code` union gains a variant | the staging cases still pass with it unlisted; the GLSL example and `test/cli/StagedMatch.roc`, which match every variant, are what fail |
| a field added to `NodeStore` or `CommonEnv` | it moves the sizes pinned in `test/serialization_size_check.zig:41-42` and needs a `CACHE_VERSION` bump (`src/compile/cache_config.zig:237`) |
| lines added to `Check.zig` and the other files `run-check-type-checker-patterns` scans | its excluded ranges are line numbers (`build.zig:770`), so `minici` can fail at code the change never touched |
Line numbers were last checked against the `staging` branch over `main` at
`90d6e058ec`. The sections C24 and C25 rewrote carry current ones; the rest
have drifted.
