# Code reification: the pure-function surface a description covers

For a short introduction to the feature, read `docs/reifying-overview.md`.

A translator is a compiler written in ordinary Roc that runs during `roc build`.
It receives a `Code(f)`: a reified, typed, closed, monomorphic description of a
pure Roc function. The description is a `Code.Graph` of `Code.Row` values. Each
row holds `Code.Node` values, and each node holds a `Code.Op`, its arguments
(`Code.Val`), its type (`Code.Ty`) and the `speculatable` flag. The types are
declared in `src/build/roc/Builtin.roc:23625` to `src/build/roc/Builtin.roc:24212`.

This file is the checklist for that surface. Every box is a feature of pure Roc
that a description could carry. A ticked box is one the compiler carries today.
The rules the description follows are in `roc-reify-normal-form.md`. The
user-facing page is `docs/langref/reifying.md`.

Effects stay out of scope by design. An effectful function, `dbg`, a hosted
lambda and `x!` are refused, and nothing here proposes describing them.

A construct a target cannot run is still described, because a named node costs
one translator a rejection, and a refusal costs every author the construct.

Legend

- `[x]` the compiler describes it, proven by a probe or a test
- `[ ]` the compiler refuses it, and the quoted text is the reason line the
  diagnostic carries (`Rejection.detail`, `src/check/code_reifier.zig` (`Rejection`))

## 0 Vocabulary

| Term | Meaning | Where declared |
| --- | --- | --- |
| `Graph` | `{ root, rows }`. The rows a site reaches, root first. | `src/build/roc/Builtin.roc:24079` |
| `Row` | One function: `id`, `params`, `result`, `nodes`, `body`, `recursive`. | `src/build/roc/Builtin.roc:24056` |
| `Node` | `{ op, args, ty, speculatable }`. | `src/build/roc/Builtin.roc:24020` |
| `Op` | What a node computes. 24 ops. | `src/build/roc/Builtin.roc:23960` |
| `Val` | `Param(k)`, `Node(i)`, `Out({ node, k })`, `Arg({ owner, k })`, `Input(k)`. | `src/build/roc/Builtin.roc:23847` |
| `Graph.slots` | The types of the root's input slots, in slot order. Empty unless the translator returns a `Code.Bound`. | `src/build/roc/Builtin.roc` (`Graph.slots`) |
| `Bound`, `Value` | `Code.Bound(a)` is a translator's result with the site's run-time values, `{ value, inputs }`. `Code.Value` is one run-time value of a slot. | `src/build/roc/Builtin.roc` (`Code.Bound`, `Code.Value`) |
| `Region`, `End` | A body and how it ends: `Value`, `Jump`, `Return`, `Continue`, `Break`, `Branch`. | `src/build/roc/Builtin.roc:23880`, `:23897` |
| `Key` | The value one `Switch` arm takes: `Tag`, `Lit`, `Len`, `AtLeast`, `Default`. | `src/build/roc/Builtin.roc:23864` |
| `Tree` | One row as nested expressions, from `Graph.to_tree`. | `src/build/roc/Builtin.roc:24138` |

| View | Type | What stays a row |
| --- | --- | --- |
| `graph` | `Code(f)`, read with `Code.graph` | A recursive row, a row called from two or more places, a row a `Closure` names, and a row that holds a `Return` in a loop or in a switch arm. |
| `inline` | `Code.Inlined(f)`, read with `Code.Inlined.inline` | A recursive row, and a row that holds a `Return` in a loop or in a switch arm. Every other row is inlined, and a `Closure` of any non-recursive row is a `Lambda` region. |
| `outline` | `Code.Outlined(f)`, read with `Code.Outlined.outline` | The rows of `inline`, and one row for each computation of at least four nodes that occurs at two or more places (`roc-reify-normal-form.md` 5.3). The places are matched by anti-unification: where they differ in a value, the value is a parameter of the row, and only a speculatable value moves out of an arm or a loop body to be passed. A computation that holds a `Return`, or a `Continue`, `Break` or `Jump` to outside itself, is not made a row. |
| `lawful` | `Code.Lawful(f)`, read with `Code.Lawful.graph` | The rows of `graph`, normalized with the laws of layer L as well (`roc-reify-normal-form.md` 3.16). A row a raised loop or a fused `map` calls is a row a `Closure` names. |

The `graph` view inlines a helper called from one place, unless the helper
holds a `Return` in a loop or in a switch arm. The `inline` view keeps such a
row too. Inlining it would make the caller return the value of the callee and
skip the rest of its own body. A `Return` in a lambda body ends the lambda, so
it does not count, and a `Return` in tail position folds to a value (rule T6
of `roc-reify-normal-form.md`). The rules are in `src/reify/views.zig:1`. The normal-form version is 5
(`src/reify/mod.zig:33`). `Code.version` returns it.

---

## 1 Literals

- [x] Integer literal of every width, in decimal, `0x`, `0o` and `0b`, with or
      without a type suffix. Reified as `Lit.Int(I128, Ty)`. A literal that
      does not fit its type is refused as "this numeric literal"
      (`src/check/code_reifier.zig` (`numeralLit`)).
- [x] Fractional literal at `F32` and `F64`. `Lit.Frac(F64, Ty)`.
- [x] `Dec` literal. `Lit.Fixed(Dec)`.
- [x] String literal of one segment. `Lit.Str(Str)`.
- [x] `Bool.True` and `Bool.False`, as `Lit.Bool`. Bool is the one tag union
      with a literal, because a translator emitting a boolean wants the value
      rather than the two tags Roc represents it with
      (`src/check/code_reifier.zig` (`tagExpr`)).
- [x] String interpolation, and any string of more than one segment. The
      checker leaves the segments flat, text and value alternating, and every
      one is a `Str`. The literal describes as one `Prim` `concat` (owner
      `Str`) with every part in `args`. A segment the author left empty joins
      nothing and is dropped, so `"${v}"` describes as `v`
      (`src/check/code_reifier.zig` (`interpolatedExpr`)). A nested `concat` chain arrives as
      the same one node (rule N15 in `roc-reify-normal-form.md`).
- [x] Numerals follow the ordinary Roc defaulting rules. See
      `docs/langref/reifying.md`.
- [x] A literal of a type of your own, through `from_numeral` or `from_quote`,
      when the conversion is a method of a builtin or of a function of another
      package. It describes as a `Prim` for that conversion, with the number or
      the text the author wrote as its one argument. The `Num.Numeral` the
      checker declares is an opaque a translator has no reason to model. A
      numeral names no width, so it takes the widest form `Lit` holds, `I128`
      or `F64` (`src/check/code_reifier.zig` (`generatedNumeral`)): a fractional one rounds to
      `F64` where the author's `from_numeral` would have seen exact digits.
- [x] A literal of a type of your own whose conversion is a Roc function of the
      package being described. It describes as a `Call` of the row of that
      function (`src/check/code_reifier.zig` (`dispatchWithArgs`)). A quoted
      literal passes its text as a `Str`. A numeral passes the `Num.Numeral`
      the compiler builds from the digits the author wrote: a
      `Wrap("Builtin.Num.Numeral")` of a `Tag("Literal")` of a `Record` with
      `digits_after_pt`, `digits_after_pt_count`, `digits_before_pt` and
      `is_negative`, the fields Monotype fills (`numeralArgument`). The
      digits are exact, so this form has no `F64` rounding. The checker reads
      the row's `Try` as a conversion: the value is the `Ok` payload, and an
      `Err` is a literal the conversion rejected, which is a `Crash` with the
      message "this literal was rejected by its conversion"
      (`convertedLiteral`). A conversion that returns `Ok` of a known value
      folds to the value. Pinned by the staging cases at
      `src/eval/test/eval_staging_tests.zig:2054` and `:2060`, and by
      `src/compile/test/code_reifier_test.zig:1686`, `:1749` and `:1815`.
- [x] A literal of a type of your own through `from_interpolation`. "a custom
      string interpolation". The conversion runs in two stages (design.md,
      "An interpolated string literal converts in two stages"):
      `from_interpolation` reads the segments while the compiler runs and
      hands back an assembler, and the value is that assembler applied to the
      interpolated values. The walk runs the first stage by its definition
      where the literal stands, with the segments as a literal list
      (`src/check/code_reifier.zig` (`interpolationExpr`, `inlineCall`)),
      the way it reads a top-level value that computes a function. A builtin
      the stage calls that hands back a function, `Str.from_interpolation`
      and `Try.map_ok`, is walked by its Roc definition too, and a lambda the
      stage applies is walked where it is applied (`appliedInline`). The
      lambda that the `Ok` holds is a closure of a row, so the literal is the
      `Call` of that row over its captures, the segments among them, and the
      list of the interpolated values. Until M17 a translator sees the fold
      over that list that `Str.from_interpolation` writes. No node is new.
      The `Err` of the stage is the crash of the `from_numeral` case, "this
      literal was rejected by its conversion". The compiler wrote that crash,
      not the author, so it is a `Crash` of kind `rejected_literal`
      (`src/reify/ir.zig` (`CrashKind`)). Rule N13w of the normal form
      (`roc-reify-normal-form.md` 3.13) drops every test of the stage that
      only leads to it, so a rejection written as an `if`, a `match`, a chain
      of tests or a test in a helper describes as the conversion that never
      rejects. A rejection whose path stays behind a call that is not
      inlined stays a crash. A conversion in the translator's cut is one
      `Prim` named by its type and `from_interpolation`, over the segments and
      the values. Pinned by the
      staging cases at `src/eval/test/eval_staging_tests.zig:2452`, `:2458`
      and `:2464`, and by `src/compile/test/code_reifier_test.zig:4799`,
      `:4867`, `:4914`, `:4951` and `:5003`, and the spellings of a
      rejection by the L3 pairs at `:5108` to `:5146`. A `crash` that the
      author wrote in the stage stays, so the stage keeps its branch and the
      literal is refused (`:5160`). A conversion that can leave its
      body early, with a `?`, and one generic in the item type of its
      assembler are still refused (`:5034`).
- [x] A literal of a type of your own in a `match` pattern. The pattern binds
      the matched value, and the checker's own equality of that type against
      its conversion of the literal becomes a `Bool` `Switch`
      (`src/check/code_reifier.zig` (`guardedTest`)). Each alternative of
      `7 | 8` converts its own literal. Pinned by
      `src/eval/test/eval_staging_tests.zig:2066`.
- [x] An embedded file. One imported as `List(U8)` describes as
      `Code.Lit.Bytes(List(U8))`, a single literal holding the blob rather than
      one `Int` node per byte, because a file is as large as it is
      (`src/check/code_reifier.zig` (`exprAs`)). One imported as `Str` describes as a
      `Str` literal, through the same arm any text literal takes.

## 2 Names a body may read

A binding leaves no node of its own. The node that computes the value is the
binding, and a read of the name is `Val.Node(i)`. A value read more than once
stays shared, so a binding written once stays written once.

- [x] A parameter of the reified lambda. `Val.Param(k)`.
- [x] A binding the body introduced. The node that computes it, read as
      `Val.Node(i)` or, for a node with several outputs, `Val.Out`.
- [x] An argument the template call fixed, read as the literal it was called
      with rather than as a name (`Binding.Kind.constant`).
- [x] A top-level value of this module or of one it imports, written as a
      literal or as a record, tuple, list, tag or nominal built from literals,
      folded into the description as the value it holds
      (`src/check/code_reifier.zig` (`foldedConstant`)).
- [x] A top-level value that has to be computed, `limit = 7.0 * 2.0` or
      `limit = xs.len()`, of this module or of one in its package. It is not
      evaluated first: its definition names only things the compiler fixes,
      so the walk builds that definition where the name stands, by the same
      path that folds a literal (`src/check/code_reifier.zig` (`foldedConstant`)).
      `x > limit` describes as `x > 7.0 * 2.0`, and a constant the definition
      reads folds in turn, so `List.len([1, 2, 3])` stands where `limit` did.
      A computed value of another package folds the same way (N8l, M13). A
      top-level value that computes a function is the item after the alias
      item below.
- [x] A value the block around a lambda written at a `Code` position binds,
      read by that lambda. The statement that bound it is replayed at the head
      of the lambda's body, so the lambda holds the node that computes it
      (`src/check/code_reifier.zig` (`replayStatement`, `replayBinding`)), and a statement the lambda
      does not read stays out. A function the block binds is lifted into a row
      that takes what it captured first. Reading the value as a node in the
      lambda is the one reading that holds everywhere: the site's `f` leaves
      no room for an added parameter, and folding the value needs a constant
      the compiler evaluated, which a block is only inside a top-level
      constant.
- [x] A name the compiler does not fix, a function parameter or a branch or
      loop binder, read by a lambda whose translator returns a
      `Code.Bound`, whether the lambda reads it or a replayed statement does.
      It is an input slot `Input(k)`, with the longest chain of `Field`,
      `Index` and `Unwrap` reads of it (rule N18 of
      `roc-reify-normal-form.md`). The program receives its value at run
      time in `Code.Bound.inputs` (`src/check/code_reifier.zig`
      (`unboundRef`, `inputSlot`), `roc-reify-proposal.md` section 10.1).
- [ ] The same name, read where the translator does not return a
      `Code.Bound`. Refused as a capture, naming it, with the line "A
      translator whose result is a `Code.Bound` receives such a value as an
      input slot." (`src/check/code_reifier.zig` (`unboundRef`)).
- [ ] A `var` read from around the lambda. "a `var`, whose value at the call
      is not always the value the description reads".
- [ ] A slot whose type holds a function, an opaque type or an optional record
      field. "a captured function value", "a captured value of an opaque
      type", "a captured record with an optional field".
- [ ] A translator call with captured inputs whose other arguments are not
      fixed at build time: "a translator that receives captured inputs runs
      while the compiler runs, so the other arguments of its call must be
      fixed then". A call that holds two such sites: "a call that binds the
      inputs of two sites".

## 3 Operators

A builtin operator arrives as a `Prim` named by owner and method, such as owner
`Num.I64` and method `plus`. The owner is `Num.` and the type name for a number.

| Written | Arrives | Source |
| --- | --- | --- |
| `+`, `-`, `*`, `/`, `//`, `%` | `Prim` methods `plus`, `minus`, `times`, `div_by`, `div_trunc_by`, `rem_by` | `src/check/code_reifier.zig` (`binopMethod`) |
| `==` | `Prim` method `is_eq` | `src/check/code_reifier.zig` (`binopExpr`) |
| `!=` | `Prim` `Bool.not` over `is_eq`, whether the type derives its `is_eq` or writes it. Which of the two the author wrote rides on the dispatch plan. | `src/check/code_reifier.zig` (`exprAs`) |
| `<`, `<=` | `Prim` methods `is_lt`, `is_lte` | `src/check/code_reifier.zig` (`binopMethod`) |
| `>`, `>=` | `is_lt` and `is_lte` with the operands swapped. No node is `is_gt` or `is_gte`. | `src/build/roc/Builtin.roc:23936` |
| Prefix `-` | `Prim` method `negate` | `src/check/code_reifier.zig` (`exprAs`) |
| Prefix `!` | `Prim` `Bool.not`. `!b`, `Bool.not(b)` and `b.not()` all describe as the one node. | `src/check/code_reifier.zig` (`exprAs`) |
| `and`, `or` | An `And` or `Or` node. The first operand is in `args` and each other operand is a region, so both short-circuit. | `src/check/code_reifier.zig` (`connective`) |
| `x \|> f(y)` | A plain call, described as one. | |
| `a..<b`, `a..=b` in a `for` | `ForRange({ inclusive, body })`. A range outside a `for` is refused: "a range outside a `for`". | `src/check/code_reifier.zig` (`rangeOf`, `binopExpr`) |
| `x ?? default`, `x?`, `x ? Tag` | `Unwrap` of the `Try`, then a `Switch` with the arms `Err` and `Ok`. A payload is read with `Payload("Ok", 0)`. The `Err` arm of `?` is a `Return`. | `src/check/code_reifier.zig` (`matchExpr`) |

The normal form also reorders a literal to the last place of an integer `plus`,
`times` or `is_eq`, and it flattens chains of `plus_wrap`, `times_wrap`,
`bitwise_and`, `bitwise_or` and `bitwise_xor`. The table is in
`src/build/roc/Builtin.roc:23936`.

## 4 Calls

- [x] Static dispatch, `x.f(y)`, on a builtin. It arrives as a `Prim` named by
      its owner and method, such as owner `Num.F32` and method `sin`. The
      translator decides what the call means in its target.
- [x] An operator method, carried as a `Prim` of the operator.
- [x] A plain call to a named function of the module being described, `f(x)`,
      as `Call(row)` (`src/check/code_reifier.zig` (`callExpr`)). `Call` carries the
      `id` of a row of `Graph.rows`, and its `args` are the row's
      parameters. The structure the author wrote survives into the target
      when the row is kept. A callee the walk cannot describe refuses the
      whole site, because a translator would otherwise meet a `Call` with no
      row. The report points at the call in the caller, not at the construct
      inside the callee that stopped the walk; a frame per hop would fix that.
      A row has no name, because the graph holds the definitions of every
      module a description reaches under one numbering.
- [x] The callee's own description, as a row of `Graph.rows`, so a translator
      resolves each `Call` against a table the compiler wrote rather than one
      the user assembled by hand (`src/check/code_reifier.zig` (`calledRow`)). A method
      call writes a row too: the instantiation edge names the target, whether
      the plan carries it or the caller's evidence does
      (`src/check/code_reifier.zig` (`methodTargetCallee`)). A row is described once however
      many calls reach it. The root is `Graph.root`, always the first row. The
      other rows follow in the order a depth-first walk of the root first meets
      them (`src/reify/number.zig:225`). The `graph` view keeps a row only
      where the table above says. `Row.recursive` says the row reaches itself
      through its calls. A `Call` carries no tag saying what kind of callee it
      names: a row id names a row, and a tag beside that would make "resolved,
      with no row" representable.
- [ ] A method whose target the checker names nowhere. "a method this call names
      no target for", and "a method its nominal names no target for" for a
      derivation (`src/check/code_reifier.zig` (`dispatchWithArgs`, `writtenMethodCall`)). The walk does not
      guess a bare name for it.
- [x] A call to a function in another module, `Helper.f(x)`, described from
      that module's published view and named by it
      (`src/check/code_reifier.zig` (`resolvedTarget`)). The binding the checker resolved
      names the artifact rather than the import it came through, so the table
      also reaches a module the described one never imports: a callee's own
      callee, two modules away. A module the walk cannot read is refused: "a
      call to a function in a module this one does not read"
      (`src/check/code_reifier.zig` (`reachedAway`)). A cached build still rebuilds the
      description when that module changes: an artifact key hashes its
      imports' keys, and the call graph is a subgraph of the import graph,
      because a call resolves only where the checker resolved a reference.
- [x] A call to a function of another package. It describes by its body, as a
      function of the site's package does (N8l). A function in the
      translator's cut, which the item `code_primitives` of the translator's
      type lists, in any package, describes as a `Prim` named by its qualified
      name: the nominal it is an associated item of and the item. Its body is
      not read (N8h), and a translator maps it by name, as the GLSL example
      maps `Glsl.Vec3.scale` (`src/check/code_reifier.zig` (`resolvedTarget`,
      `inCut`)).
- [x] A call to a function the compiler provides. The builtin is a `Prim` named
      by its owner and method, and no row is written for it, because its body
      is the compiler's and a translator resolves the name against what its
      own target provides (`src/check/code_reifier.zig` (`providedPrim`)). A method call on
      the same builtin reads that same name, so `Str.concat(a, b)` and
      `a.concat(b)` are one `Prim` under one name. A builtin the `Op` does
      carry a node for is folded into that node instead: `Bool.not` is the
      same `Prim` however it is spelled, and `and` and `or` are `And` and `Or`.
- [x] A call to a generic function. The callee's body reads differently at each
      instantiation, so the walk describes one row per instantiation: the
      template's own function type read against the type of this exact use
      gives what each quantified variable was fixed to
      (`src/check/code_reifier.zig` (`instantiationOf`)), and the row is keyed by a digest of
      those types. `id` called at `F32` and at `U64` is two rows. A variable
      the call does not fix is refused as "a type variable this call does not
      fix", except a row variable, which a call may leave unbound because no
      description names a row (`src/check/code_reifier.zig` (`rowVars`)).
      A use can also lift a structural record or tag union of the scheme
      into a nominal (`src/check/unify.zig` (`mergeToNominal`)): `check =
      |m| if m < 10 Ok(m) else Err(m)` read by `check(input)?` is read at
      `Try`. The match records that structure as fixed to the nominal, and
      the key names it, so the row is built at `Try`, its tags are wrapped,
      and a use at the helper's own union is another row
      (`src/check/code_reifier.zig` (`matchType`, `instantiationKey`)).
      Pinned by "a `?` on the Try a block-generalized helper returns
      describes as the helper's body in place" and the tests after it in
      `src/compile/test/code_reifier_test.zig`.
      A lambda written in the generic callee is part of that callee, so its
      row is built under the instantiation of the callee's row: the same
      substitution, the same evidence, and a key that extends the callee's
      own (`enclosedLambda`, `src/check/code_reifier.zig` (`enclosedLambda`)). `firsts =
      |xs| xs.map(|p| p.0)` called at `(I64, Str)` describes, a nested lambda
      and one that captures a parameter of the callee too, and two
      instantiations give two rows for the lambda. A lambda the callee's
      block generalized adds its own lookup's substitution on top. A row that
      a `where` method's type stands on, such as the open error row of
      `from_numeral`, is a row of the scheme, so a call may leave it unbound.
      Pinned by the staging cases "a lambda in a generic callee describes at
      each instantiation" and "a lambda in a where-constrained generic callee
      dispatches at the fixed type".
- [x] A function parameter a call fixed, captured by a lambda. In
      `apply_all = |xs, f| xs.map(|x| f(x))` called with `|x| x * 3`, `f` is
      bound to that lambda's row, and the lambda `List.map` receives captures
      `f`. The lifted lambda carries the binding as a bound callee for the
      captured name, not as a captured value, so a call of `f` inside it names
      the row, and the closure takes nothing for `f` (`enclosedLambda`,
      `src/check/code_reifier.zig` (`enclosedLambda`)). A lambda that captures only such
      names can also be passed on to another definition. `xs.map(f)` passes
      the bound row as a closure. Pinned by the staging case "a lambda that
      captures a fixed function parameter names its definition".
- [x] A call to a function written inside another function, lifted into a row
      of its own (`src/check/code_reifier.zig` (`liftedTarget`)). The binding leaves no
      node behind, because the description is first order. What the lambda
      captured arrives as a leading parameter and every call site passes it
      first (`src/check/code_reifier.zig` (`enclosedLambda`)); captures are lexical, so every
      call sits in the scope that holds them. A local the checker generalized
      describes at the type each call fixes, a row per type.
- [x] A type-qualified call, `Type.f(x)`, which resolves to the same dispatch
      plan a value dispatch leaves behind, so the two describe through one arm
      (`src/check/code_reifier.zig` (`exprAs`)). The target is the plan's dispatcher
      read under the active substitution, so `Shape.f(x)` inside a
      `where`-constrained body is resolved at the type the call fixed `Shape` to.
- [x] Calling a parameter or a binding that holds a function. The `Op` list has
      no node for applying an expression, so the walk resolves the function at
      the site that fixes it, the way a call fixes a generic callee's type
      variables. A function argument binds the callee's parameter to the
      definition it names, and the row is keyed by that as well as by the types
      (`src/check/code_reifier.zig` (`passedCallee`)): `apply_to(double, x)` and
      `apply_to(triple, x)` are two rows. A definition that hands back a
      function and the use that runs it are one flattened row and one `Call`,
      which is how a hand-written `encoder_for` is run. A builtin or a
      function in the translator's cut used as a value is refused: "a builtin
      or a function in the translator's cut used as a value"
      (`src/check/code_reifier.zig` (`functionValue`)). A `var` that holds a function is
      refused: "a var that holds a function"
      (`src/check/code_reifier.zig` (`carriedValue`)).
      A lambda handed to a dispatch is a `Closure` of its row, or, in the
      `inline` view, a `Lambda` region where it is built. That is what a derived
      `map` and a builtin `map` both want.
- [x] A call through an exact alias, `same_thing = add_one`. The checker
      records the lookup an alias forwards to (`forwarded_lookup`,
      `src/check/checked_artifact.zig`), and the walk follows it to the
      procedure it names (`src/check/code_reifier.zig` (`forwardedProcedure`)), so the call is a
      `Call` of that procedure's row and the alias and the name share one row.
      An alias another module exports is followed the same way through its
      export row (`src/check/code_reifier.zig` (`reachedProcedure`)). An alias of a computed
      function, `f = make(2)`, has no forwarded lookup, so it is the next item. Pinned by
      `src/eval/test/eval_staging_tests.zig:1823` ("staging - a call through an
      alias calls the row of the function it names") and
      `src/compile/test/code_reifier_test.zig:532`.
- [x] A top-level value that computes a function, `doubler = make(2.0)` with
      `make = |k| |x| x * k`, used in a described body. The compiler
      evaluates such a value after the description is built, so the walk has
      no closure value to read. It reads the definition, as it reads a computed
      constant: the checker records the checked expression the binding was
      written as (`CallableEvalTemplate.body`,
      `src/check/checked_artifact.zig:16986`), and the walk builds that
      expression where the name stands (`src/check/code_reifier.zig`
      (`computedFunction`, `foldedBody`)). The definition names the lambda and
      its captures, so the capture `2.0` is the literal the definition wrote.
      A call on the name is the curried call of the definition and the use,
      one `Call` of the lambda's row over the capture and then the argument
      (`curriedCall`, `constructorCall`, `computedConstructor`). The name used
      as a value is a `Closure` of the row over the capture. A function the
      definition captures is a row of its own by the same rule, and a value
      written as another such value, `renamed = doubler`, is the one it names.
      A value of another module, in any package, is read in that module's
      reader (`ForeignLookup.resolve_exported_computed`,
      `src/check/checked_artifact.zig` (`exportedComputed`)). A capture the walk
      cannot describe stops the walk with its own reason, for example "dbg".
      Two cases stay refused: a value that reads itself, "a top-level constant
      that computes a function and reads itself"; and a site that names such a
      value as the function to describe, "a top-level constant that computes a
      function, named as the function to describe", because the site's root
      needs a lambda whose parameters it can list (`reachedHere`). Pinned by
      `src/eval/test/eval_staging_tests.zig:2066`, `:2072`, `:2078`, `:2084`,
      `:2090` and `:2107`, and by `src/compile/test/code_reifier_test.zig:1388`,
      `:1420`, `:1448`, `:1483`, `:1503` and "N8l M13: a top-level value of
      another package that computes a function is walked by its definition".
- [x] A function chosen by an `if` between known functions, and then called:
      `(if c double else triple)(x)`. The call is first an `Apply` of the value,
      and simplifying turns each `Apply` whose function is a known closure into
      a `Call` of its row, so the result is a `Switch` over the calls. `Apply`
      is no `Op` of the description: it either resolves or the site is refused.
      Checked with a probe of each form.
- [ ] A function taken from a list and then called, `Ok(g) => g(x)` in a
      `match` on `[double].first()`. "a call to a function value that no
      simplification resolves" (`src/check/code_reifier.zig` (`normalize`), pinned by
      `src/compile/test/code_reifier_test.zig:2305`): simplifying does not read a
      closure back out of a list, so the `Apply` stays.

## 5 Control flow

- [x] `if`, `else if` and `else`, at any depth. A `Switch` on a `Bool`, with the
      keys `Lit(Bool(False))` and `Lit(Bool(True))` in that order
      (`src/check/code_reifier.zig` (`ifExpr`)).
- [x] `match`, as a `Switch` whose arms are tried in the order they were
      written, first match wins (`src/check/code_reifier.zig` (`matchExpr`)). A match on
      a tag union has one arm per variant of the scrutinee's own union, each
      with a `Tag` key. A match on an integer has one `Lit` arm per value and a
      `Default` arm. A match on a list has `Len` and `AtLeast` arms. A payload
      is read with `Payload(tag, k)`.
- [x] A branch written `A | B =>`, as one path per alternative into the same
      value.
- [x] A branch guard, as a `Bool` `Switch` after the pattern matched, whose
      false arm goes on to the next branch
      (`src/check/code_reifier.zig` (`matched`)).
- [x] `for` and `while`, each as the loop it is: `ForRange` over an integer
      range, `ForList` over a list, and `Loop` for a `while` or for the
      iterator protocol (`src/check/code_reifier.zig` (`forLoop`, `conditionLoop`)). The
      state the loop takes from one turn to the next is whatever `var`s the
      body assigns. Each is a numbered slot, an `Arg` of the body region, and
      the body ends in `Continue` with the slots of the next turn. A loop that
      assigns none carries none. The `ForRange` body takes the index as
      parameter 0, and the `ForList` body takes the index and the item.
- [x] `while Bool.True { .. }`, which reaches the walk as a form of its own
      and carries what a `while` carries, so the three share one call
      (`src/check/code_reifier.zig` (`walkStatement`)).
- [x] `break`, and a `return` that crosses a loop, as the region ends `Break`
      and `Return` (`src/check/code_reifier.zig` (`breakTransfer`, `returnTransfer`)). These are the
      two whose continuation is the turns of the loop that have not run, which
      no branch says. A target with its own `break` emits one, and a target
      that folds lowers them itself.
- [x] `return` as an early exit. A branch that can leave the row makes its
      `Switch` an exiting switch, whose arms end in `Return` or in a `Jump` to
      the join that holds the statements written after it
      (`src/check/code_reifier.zig` (`terminate`)). That is what lets a target with no
      loops at all, SQL or a query plan, take `return` and `x?` while
      never meeting a control-flow node it cannot read.
- [x] A `return` written inside an expression, `Ok(t? * 2.0)`. The branching
      construct is a `Switch` in the region where the expression stands, so
      what follows is the join. The walk does this once rather than every
      translator doing it.
- [x] `crash`, as `Crash` with the message as its one argument
      (`src/check/code_reifier.zig` (`exprAs`)). A written `crash` carries a `Str`
      expression, so an interpolated message arrives as the concatenation the
      checker made of it (`src/check/code_reifier.zig` (`exprAs`)). A `crash` in
      statement position is a node too (`src/check/code_reifier.zig` (`walkStatement`)).
- [x] `expect` inside a body. It asserts and hands back nothing, so the
      description passes over it the way it passes over a type annotation
      (`src/check/code_reifier.zig` (`walkStatement`)). A translator emits a target, and an
      assertion written for Roc's own test run has no place in one. An
      `expect` used as an expression is the empty record.

## 6 Bindings and blocks

- [x] A block body with `let` bindings and a final expression. A binding keeps
      its node and every read names it, so a binding written once stays written
      once, and `Graph.to_tree` keeps a node read more than once as a `Def`.
      Losing it is a defect in the output, not only in the ergonomics: the same
      shader built by evaluation carries four texture fetches where the source
      writes one (`examples/reifying/shaders-without-reifying/main.roc:18`).
- [x] A binding whose value is any describable expression.
- [x] A destructuring binding, `{ a, b } = r`, expanded into the reads it
      stands for: a `Field` or an `Index` node per name
      (`src/check/code_reifier.zig` (`bindPattern`)). A translator that has records and
      locals emits this without also having pattern matching. A pattern that
      names one variant of a one-variant union reads its `Payload`. A pattern
      that can fail is refused: "a destructuring pattern that can fail". A list
      or literal pattern in a binding is refused by its form.
- [x] A parameter written as a pattern, `|(a, _), b|` or `|{ a, b }|`, as a
      parameter whose reads are the same reads a destructuring binding takes.
      `_` binds nothing and reads nothing.
- [x] A `var`, and any reassignment to one, as single assignment: each
      assignment binds the node of its value, and a read after it names that
      node (`src/check/code_reifier.zig` (`walkStatement`)). A `var` written in one branch
      and read after it is joined by the `Switch` that holds the branch, which
      delivers the value as an output, and several `var`s travel through one
      join as several outputs. An assignment that writes more than one name is
      refused.
- [x] A type annotation or a type declaration inside a body, which names a type
      for the checker and leaves no value behind, so the description passes
      over it (`src/check/code_reifier.zig` (`walkStatement`)).
- [ ] An `import` inside a body. The parser refuses one ("import must be top
      level") before the walk could meet it, so no body holds one to describe.
- [x] A statement whose value is discarded, as a binding nothing reads
      (`src/check/code_reifier.zig` (`discard`)), which keeps both its order and
      whatever it diverges on. Two shapes of one are something else first,
      because both hand back what the statements after them need: a branch
      that transfers, and a branch that assigns a `var`.
- [x] A function bound inside a block, lifted into a row of its own rather
      than left as a value (`src/check/code_reifier.zig` (`declStatement`)). Naming one
      where a `Code` is expected describes by section 11.

## 7 Aggregates

- [x] Record literal. `Record(List(Str))` holds the field names, and `args`
      holds the values in that order. The fields are in name order.
- [x] Field access, at any depth. `Field(Str)`.
- [x] A record field with a default (`port : U16 ?? 8080`), read as an ordinary
      field.
- [x] Tuple literal. `Tuple`.
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
      (`src/build/roc/Builtin.roc:23953`). See `roc-reify-tag-names.md`.
- [x] Tuple access, `t.0`. `Index(U64)`.
- [x] List literal. `List`.
- [x] Indexing a list. `List.get` returns `Try(a, [OutOfBounds, ..])` with an open error row, and the
      checker closes that error union at the call, which the description
      follows.
- [x] An empty aggregate, `[]` or `{}`. `List` and `Record([])` with nothing in
      them.
- [x] A nullary tag as the value a reified function hands back. Pinned by the
      staging case "a reified function hands back a nullary tag"
      (`src/eval/test/eval_staging_tests.zig:1739`). The empty aggregate is
      covered by the previous box.
- [x] Record update, `{ ..r, b: 1 }`, expanded into the `Record` it stands
      for: the fields the update wrote, and every other field of the type read
      out of the subject (`src/check/code_reifier.zig` (`recordExpr`)). An
      optional field the update did not write carries whatever the subject
      had, and only the subject's value says if it had the field. The update
      is then a `Switch` on `unwrap(OptField(r, b))`: the `Ok` arm is a
      `Record` that sets `b` to the payload, and the `Err` arm is a `Record`
      that leaves `b` unset. Two such fields make nested switches, one level
      for each field (`recordSetting`). Pinned by
      `src/eval/test/eval_staging_tests.zig:2162`.
- [x] An unset record field (`b: _`), and an optional field a literal leaves
      out. The `Record` node does not set the member. It lists the members it
      sets, so `Record(["a", "c"])` has two arguments for a type with three
      fields, and the type's `Record` entry for `b` says `Optional`
      (`ir.RecordForm`, `src/reify/ir.zig`). A record that sets every member
      lists nothing, so one value has one form. An update that unsets a field
      does not read the subject for it. Pinned by
      `src/eval/test/eval_staging_tests.zig:2120`, `:2156` and `:2168`, and by
      `src/compile/test/code_reifier_test.zig:1237`.
- [x] An optional record field (`timeout ?: U64`), as the `presence` a
      `Ty.Record` entry carries and `OptField(Str)` for the `.?timeout` that
      reads it (`src/check/code_reifier.zig` (`fieldAccessExpr`)). The read hands back the
      `Try(a, [MissingField])` the value sits in rather than the value, which
      is why it is a node of its own. The checker gives a path one flat `Try`
      of the last field's type however many optional segments it holds, and
      the first optional segment that is missing is the `Err` of all of it. A
      `.?` that is not the last segment is a `Switch` on its own `Try`: the
      `Err` arm is `Err(MissingField)` of the path's type, and the `Ok` arm
      reads the rest of the path. A required segment after the last optional
      one is read in the `Ok` arm and wrapped in `Ok` (`optionalPath`).
      Pinned by `src/eval/test/eval_staging_tests.zig:2174` and `:2180`.
      The read of a field a record literal did not set is not folded: the
      description keeps `OptField` of the `Record`, which names the field it
      does not list. Pinned by `src/eval/test/eval_staging_tests.zig:2126`.

## 7b Patterns a `match` branch may test with

A pattern is not a value of the description. It becomes the `Switch` keys, reads
and binds below.

| Pattern | Becomes | Source |
| --- | --- | --- |
| `x` | The name is bound to the matched node. | `src/check/code_reifier.zig` (`testQueue`) |
| `_` | Nothing. | `src/check/code_reifier.zig` (`testQueue`) |
| `Tag(p, q)` and a bare tag | A `Switch` with a `Tag` key per variant of the scrutinee's own union. The matching arm tests the payloads, read with `Payload`. | `src/check/code_reifier.zig` (`tagTest`) |
| `Bool.True`, `Bool.False` | A `Switch` on the `Bool` with the `Lit(Bool(..))` keys. | `src/check/code_reifier.zig` (`tagTest`) |
| An integer literal | A `Switch` with a `Lit` key, and a `Default` arm for every other value. | `src/check/code_reifier.zig` (`numeralTest`) |
| A fractional or `Dec` literal | A `Bool` `Switch` on the `is_eq` `Prim`. | `src/check/code_reifier.zig` (`numeralTest`) |
| A string literal | A `Bool` `Switch` on the `is_eq` `Prim`. | `src/check/code_reifier.zig` (`testQueue`) |
| `(p, q)` | `Index` reads, one per item. | `src/check/code_reifier.zig` (`testQueue`) |
| `{ a, b: p }` | `Field` reads. | `src/check/code_reifier.zig` (`testQueue`) |
| A pattern through a nominal, so `Ok(v)` on a `Try` | `Unwrap` of the nominal, then the tag test. | `src/check/code_reifier.zig` (`testQueue`) |
| `p as name` | The name is bound to the matched node, and `p` is tested on it. | `src/check/code_reifier.zig` (`testQueue`) |
| `[p, q]` and `[p, .., q]` | A `Switch` with a `Len` key for an exact length and an `AtLeast` key for a rest, then `Item` reads. | `src/check/code_reifier.zig` (`listTest`) |
| A literal of a type of your own | The equality the checker wrote, as a `Bool` `Switch`. | `src/check/code_reifier.zig` (`guardedTest`) |
| `{ a, .. }` | The entries beside the rest. A rest that binds nothing stands for the fields the pattern did not name. | `src/check/code_reifier.zig` (`testQueue`) |
| `{ a, ..others }` | The entries beside the rest, and `others` is bound to the `Record` of the fields the pattern did not name, each read from the matched record. A field the matched type marks optional is read by a `Switch` on its `OptField`, as in a record update. Pinned by `src/eval/test/eval_staging_tests.zig:2186` and `:2192`. | `src/check/code_reifier.zig` (`restRecord`) |
| `"a${x}b${y}c"` | `Str.starts_with` of the prefix, then `Str.drop_prefix`. Each delimiter is a `Str.split_first` of the text that is left, a `Switch` on its `Try`: `Err` goes to the next alternative, and `Ok` binds `before` to the capture and goes on with `after`. A last capture with no text after it takes the text that is left. An exact end tests `Str.is_empty` of the text that is left. Pinned by `src/eval/test/eval_staging_tests.zig:2144` and `:2198`. | `src/check/code_reifier.zig` (`strTest`) |

| Refused pattern | Reason |
| --- | --- |
| A tag pattern on a type that is not a tag union | "a tag pattern on this type" |

The string pattern follows `LIR.strMatchStep` (`src/lir/LIR.zig:821`): the
capture stops at the first place the delimiter appears, and there is no
search again after a later step fails. A target that cannot split a string
refuses the `Str.split_first` `Prim` by name.

## 8 Nominal and opaque types

- [x] A transparent nominal as a parameter or a result. `Ty.Named(Str, Ty)`,
      keeping the name over its backing shape.
- [x] Constructing one, `Vec2.({ x: x, y: 0.0 })`, which describes as `Wrap` of
      the backing under the nominal's own name.
- [x] Reading a field through one. An `Unwrap` of the nominal, then the
      `Field` (`src/check/code_reifier.zig` (`unwrapOnce`)).
- [x] An opaque nominal, and a builtin with no shape in `Ty` (`Dict`, `Set`,
      `Box`, `Iter`, `Try`, the SIMD vectors), carried by name as
      `Ty.Opaque(Str, List(Ty))` so a translator that owns the type recognises it and
      every other translator refuses it by name. A value of an opaque type
      built in the body is refused: "a value of an opaque type"
      (`src/check/code_reifier.zig` (`nominalExpr`)).
- [x] A nominal whose backing is a tag union, as `Ty.Named` over
      `Ty.TagUnion`, including one whose union reaches the nominal again.
- [x] A recursive nominal, as `Ty.Named` whose backing carries `Ty.Recursive`
      naming it at each point it reaches back. Mutual recursion describes the
      same way, each nominal named by the `Named` that encloses it.
- [x] A recursive nominal with a type parameter, such as a tree or a linked
      list. A declaration's backing is one template every use shares, so what
      is open is the nominal at the arguments this use fixed rather than the
      checked id the use carries.
- [ ] Reading inside an opaque nominal, which Roc itself forbids from outside
      the defining module.
- [x] A transparent nominal with a type parameter, read at the type arguments
      the use fixed (`src/check/code_reifier.zig` (`bindNominalArgs`)). The backing arrives as
      the template it was declared with, so the walk binds the nominal's
      declared variables to `args` for the span of that backing, the way a call
      binds a callee's quantified variables for the span of its body. `Box(F32)`
      and `Box(Str)` are two `Ty` values over one template. `Named(Str, Ty)`
      keeps the backing read at those arguments and drops the arguments
      themselves, where `Opaque` keeps the arguments and has no backing.

## 9 Types a reified signature may name

- [x] `I8` through `I128`, `U8` through `U128`, `F32`, `F64`, `Dec`, `Bool`,
      `Str` (`src/check/code_reifier.zig` (`tyOf`)).
- [x] `List(a)`, as `Ty.ListOf(Ty)`.
- [x] A record type, as
      `Ty.Record(List({ name : Str, ty : Ty, presence : [Required, Optional] }))`.
      A field with a default is `Required`, because the default fills it in
      and every value of the type carries it. So is one whose presence the
      checker never pinned, which is what the checker itself commits such a
      field to. Entries are in name order (`src/reify/types.zig:253`).
- [x] A tuple type, as `Ty.Tuple(List(Ty))`.
- [x] A pure function type, as `Ty.Fn(List(Ty), Ty)`.
- [x] A type alias, resolved to the type it names.
- [x] A tag union, empty or otherwise, as
      `Ty.TagUnion(List({ name : Str, payloads : List(Ty) }))`
      (`src/reify/types.zig:277`). The variants are in name order.
- [x] A tag union whose row the checker closed. Closing a row leaves the
      variable it solved in place, marked with the default it closed to, so
      the walk reads the mark rather than the extension's kind
      (`checkedRowVariableClosesTagRow`, used at
      `src/check/code_reifier.zig` (`collectVariants`)).
- [x] A reference back to an enclosing nominal, as `Ty.Recursive(Str)`. A
      translator resolves the name against the `Ty.Named` nodes it is inside,
      innermost first, which is the only reading: Roc refuses a recursive type
      alias, so every recursion is a nominal, and a nominal that reaches itself
      at other type arguments gets a `Named` of its own at those arguments, so
      one nominal never has two live instantiations nested inside each other.
- [x] A type variable the site fixes. The root is described at the types the
      site's `Code(f)` gives it, the way a callee is described at the types its
      call gives it: `rootSite` matches the root's scheme against that `f`
      and hands `describeDefinition` the substitution
      (`src/check/code_reifier.zig` (`rootSite`, `instantiationOf`)), so `twin : a -> (a, a)` named
      at `Code(Str -> (Str, Str))` describes with `a` at `Str`. A variable `f`
      does not reach is still refused as "a type variable at this Code
      position" (`src/check/code_reifier.zig` (`Unfixed`)). A variable only a `where`
      obligation names, such as the one in an unannotated helper
      `double = |x| x * 2`, is not in `f`, so matching cannot reach it. The
      checker recorded what the use copied every variable to, and the dispatch
      the obligation selected fixed the copy: the walk binds such a variable
      from that record (`siteSubstitution`, used at
      `src/check/code_reifier.zig` (`instantiationOf`)). A call's record is keyed by its
      callee expression. A named site is no expression any template lowers,
      so publication writes its record as an entry with a substitution and
      no evidence (`publishNamedCodeSiteSubstitutions`,
      `src/check/checked_artifact.zig`). So a generic helper that holds a
      lambda describes at the types its call fixes: the same helper called
      from a `U8 -> U8` function describes at `U8`, and a free site takes the
      type that site gives it. A use through an exact alias instantiates the
      alias's scheme, so it takes no such binding. Pinned by the staging case "a
      literal of an unannotated helper describes at the type each use fixed".
- [x] The numeric default at a site. Numerals follow the ordinary Roc
      defaulting rules, and the description takes the type the site holds when
      this module finishes checking. Narrowing that arrives from a later module
      does not reach it. The checker commits nothing: the reifier seals a
      variable published with a numeric default the way Monotype does
      (`defaultedVariable` in `src/check/code_reifier.zig`). A default that
      does not fit its use, as in `|x| x * 2.U8`, is refused with that
      reason, pinned by `test/cli/StagedUnfitDefault.roc`. A function
      with no type that any rule fixes stays refused as polymorphic, for
      example `same = |x| x`, pinned by `test/cli/StagedOpenTypeVariable.roc`.
      Where a site widens a row the description carries the definition's own
      row, which is the row the function returns; `f`'s extra variants are what
      the consumer accepts.
- [x] A `where` constrained type variable. A constraint is no shape of its own:
      the site fixes the variable the way it fixes any other, and the
      description names what it was fixed to, in a parameter and in a result
      alike. `doubled : a -> U16 where [a.size : a -> U16]` at
      `Code(Meters -> U16)` describes `Meters -> U16`, and the method the body
      dispatches is a `Call` of the row of `Meters.size`. The reifier holds no
      refusal of its own for a constraint: a constrained variable no site fixes
      is refused as a type variable, above.
- [x] The report of a type variable left open names the variable as the
      annotation wrote it (or "an unnamed type variable"), and the place it
      stands in: a parameter by its name, the result, an expression, or the
      call or `Code` position that does not fix it. A parameter's refusal
      points at the parameter. The fix the report gives follows the cause: an
      annotated variable the use leaves open, an annotated variable nothing
      fixes, an inferred variable the use leaves open, or an inferred one
      nothing fixes (`rejectOpen`,
      `src/check/code_reifier.zig` (`rejectOpen`), and `renderOpenTypeHint`,
      `src/check/report.zig`). So `.filter_by(|_band, p| ..)` reads
      "the type variable p, in the type of the parameter _band" and is told
      to fix the type of the value the parameter receives. Pinned by
      `test/cli/StagedOpenTypeVariable.roc` and
      `test/cli/StagedPolymorphicFunction.roc`.
- [x] A row a sibling argument or a later clause fixes. Checking closes no row
      at a `Code` site. An argument that comes before the lambda fixes the row
      through ordinary unification, so `join(orders, |c, o| ..)` takes its row
      from `orders`, and a second clause reading the same parameter record
      adds the fields it reads. A row that is still open when the walk reads it
      seals to the row default checking recorded on the variable, as Monotype
      seals it (`tyOf`, `collectRecordFields` and
      `CheckedTypePayload.variableSealsToRowDefault`). So a row nothing else
      fixes holds exactly the fields the lambda reads, and an open tag row
      seals to the empty union. Pinned by `test/cli/StagedSiblingRows.roc`.
- [x] An open record, or a record extended by a variable. A row is a quantified
      variable, so a site fixes it the way it fixes any other. `matchRecord`
      binds the row to the record the site named
      (`src/check/code_reifier.zig` (`matchRecord`)) and the walk reads that binding where
      an extension chain ends in a variable
      (`collectRecordFields`, `src/check/code_reifier.zig` (`collectRecordFields`)), so
      `take_n : { n : U16, ..rest } -> U16` at `Code({ n : U16, m : U16 } -> U16)`
      describes its parameter as `{ n : U16, m : U16 }`, and the same
      definition at `Code({ n : U16 } -> U16)` describes it as `{ n : U16 }`,
      in a row of its own. A row the substitution does not fix seals to its row
      default, so the "open record" refusal below is a guard for a row that
      carries no default. What the row binds to
      is the site's whole record
      rather than the fields the definition did not name, because the residual
      is no type the artifact holds; the two sets are the same once a field a
      nearer link already collected is dropped
      (`collectField`, `src/check/code_reifier.zig` (`collectField`)). A row nothing fixes
      is still refused as "an open record" (`src/check/code_reifier.zig` (`collectRecordFields`)):
      `Ty.Record` is a closed list of fields, so a record with no fixed set of
      them has no shape to write.
- [x] A tag union whose row is still open, so its extension is a variable that
      carries no closing mark: a rigid `..` or a variable that is constrained.
      The row seals to the empty union the way Monotype seals it
      (`lowerCheckedTypeVariable`), so the description has the variants the
      definition names and no others (`src/check/code_reifier.zig`
      (`collectVariants`)). A flexible row with a recorded row default seals
      the same way. A `match` arm for a variant the definition does not name,
      such as `_` over `[Red, Green, ..]`, is dead and has no arm. Pinned by
      `src/eval/test/eval_staging_tests.zig:2150` and by
      `src/compile/test/code_reifier_test.zig:1256`.

      The position is why this is sound. A record's row reaches the walk
      through a parameter, where the site's type is the precise one. A union's
      row reaches it through a result, where the definition's variants are the
      precise ones and the site's are wider, so binding the site's variants
      there would claim a body hands back variants it cannot build.

## 10 Derived methods

The six derivable methods are `is_eq`, `to_hash`, `parser_for`, `encoder_for`,
`map` and `map!`. `map!` is effectful, so it is out of scope.

What decides the treatment is who the result has to agree with. A method whose
result must agree with Roc's own, `is_eq` and `to_hash`, is expanded, because
that knowledge is the compiler's. A method that answers to a format the
translator owns, a codec or `to_inspect`, stays a `Derived(method, subject_type)`
node, whose `args` are the method's arguments
(`src/check/code_reifier.zig` (`structuralDispatch`, `derivedOf`)).

- [x] Derived `is_eq`, expanded structurally into the comparisons it performs,
      over records, tuples and transparent nominals. The comparisons join in an
      `And`, so the later ones run only where the earlier ones held
      (`src/check/code_reifier.zig` (`conjunction`)).
- [x] Derived `is_eq` over a tag union, expanded into the nested `Switch` that
      comparison is: one on the left operand, and in each arm one on the right
      operand whose matching arm compares the payloads and whose other arms are
      `False` (`src/check/code_reifier.zig` (`tagUnionEq`)). A payload is read with
      `Payload`, so no source holds a name for it.
- [x] Derived `to_hash`, expanded the same way when the description reaches far
      enough, and emitted as `Derived` when it does not
      (`src/check/code_reifier.zig` (`hashExpr`)).
- [x] `parser_for` and `encoder_for`, as one `Derived(method, subject_type)` per
      codec. A constrained body names its own evidence param rather
      than a target, so the body alone reads the same whether the compiler
      derived the codec or the author wrote it. The call that fixed the type
      says which, and the walk already enters the body once per instantiation,
      so the evidence rides in beside the substitution. A codec is also
      curried: `encoder_for` hands back an encoder the body then runs, and
      applying a function value has no node. The two halves fold into one
      (`src/check/code_reifier.zig` (`derivedCodecPlan`)), constructor arguments first, so the
      binding that held the encoder leaves nothing behind. Both spellings fold:
      `enc = Shape.encoder_for(f)` then `enc(v, s)`, and
      `Shape.encoder_for(f)(v, s)` written straight through.
      Staying unexpanded is the design, because the wire format is the
      translator's to decide, not Roc's.
      A hand-written `encoder_for` returns a real closure, and a body that runs
      one describes as the `Call` a translator resolves against a row: both
      origins carry the same arguments in the same order, which is what lets
      one translator read either. Written the ergonomic way,
      `Json.to_str(value)` is still refused as "a call to a function the
      compiler provides" when the compiler has no export name for the callee
      (`src/check/code_reifier.zig` (`resolvedTarget`)).
- [x] Derived `is_eq` over an empty tag union. Nothing inhabits it, so no
      pair of values reaches the comparison. It describes as
      `Derived("is_eq", subject)` over the two operands, as every derivation
      the walk does not expand does, and a stage that expands it meets no
      variants (`src/check/code_reifier.zig` (`derivedEq`)). Pinned by
      `src/compile/test/code_reifier_test.zig:1211`.
- [ ] Derived `is_eq` on a function type. "derived equality on a function"
      (`src/check/code_reifier.zig` (`eqOver`)).
- [x] Derived `is_eq` or `to_hash` through a nominal component. The compiler
      dispatches to a component's own method before it looks at the component's
      representation, and a derivation carries no dispatch plan, so the walk
      resolves the method itself against the checked method registries
      (`nominalMethod`, `src/check/code_reifier.zig` (`nominalMethod`)). The registry says
      which of the two a declaration is: a procedure target is a written
      method, which describes as the `Call` it is with its body in the table,
      and a structural target is the compiler's recipe, which is the signal to
      expand the backing. A generic nominal's is described at the instantiation
      its receiver fixes: the method's first parameter is the value the
      derivation is walking, and pairing the two binds what the scheme
      quantifies by shape, so `Deep(U16)` and `Deep(Str)` take a row each.
- [x] Derived `is_eq` through a `List`, `Dict`, `Set` or `Try` component, as
      the `Prim` the builtin's own method is. A scalar builtin folds into the
      `is_eq` `Prim` a translator wants, `Str` among them, and every other
      builtin goes to the registry like any nominal
      (`src/check/code_reifier.zig` (`nominalEq`)). The registry keys a compiler builtin
      under its own owner rather than under a declaration, so `ForeignNominal`
      carries that key. The walk stops at a builtin's body by rule, so the
      description is the export name and nothing more, which a translator
      resolves against its own target or rejects by name. `Box` never arrives,
      because the checker refuses `==` on one, and a derived `to_hash` over a
      container stays the symbolic `Derived` node the stage expands. A builtin
      whose equality the registry calls derived is refused: "derived equality
      on this builtin type".
- [x] Derived `is_eq` or `to_hash` through an opaque nominal that derives it.
      An opaque type's `Ty` names it without its backing, and the derivation is
      that backing's comparison, so expanding here would describe a
      representation the description hides everywhere else. It describes as
      `Derived("is_eq", subject)` over the two operands, and `to_hash` already
      did the same (`src/check/code_reifier.zig` (`nominalEq`, `derivedEq`)).
      One that writes its own method describes as the call, which hides it.
      Pinned by `src/compile/test/code_reifier_test.zig:1177`.
- [x] Derived `map`, as a `Derived(method, subject_type)` carrying the value and
      the mapping function in that order in `args`. The mapping function is a
      `Closure` like any other, and the subject is the parametric nominal read
      at the type arguments the use fixed, which is what says where the payload
      being mapped sits. Both halves were needed: the nominal alone refused as
      "a type variable" whether the mapping function was a lambda or a name.
- [x] `to_inspect`, reached through `Str.inspect`. The call is recognised by
      the intrinsic the checker recorded on the use
      (`src/check/code_reifier.zig` (`callExpr`, `inspectExpr`)). A subject whose
      `to_inspect` is the inspect override describes as that call, and every
      other subject as `Derived("to_inspect", subject_type)` with the value in
      `args`, including a container inside a record. Only the plain-call path
      checks the intrinsic, so the method call `s.inspect()` describes as the
      `Prim` of the builtin `inspect` rather than as `Derived`. Making the two
      one node needs one more `ForeignLookup` question: the intrinsic an
      exported template wraps.

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
      (`src/check/code_reifier.zig` (`forwardedProcedure`)). The site describes the procedure
      that lookup names, byte for byte the description of naming it directly.
      Pinned by the staging cases "a site that names an alias describes the
      function it names", "an alias of an alias forwards to the one function"
      and "a site that names an imported alias describes the function it names".
- [x] A function bound inside a block, named where a `Code` is expected. The
      walk follows the binder's defining statement to that lambda
      (`blockLambdaOf`, `src/check/code_reifier.zig` (`blockLambdaOf`)). The lambda reads the
      block around it by section 2, and one the block generalized describes at
      the type each site fixes. A name bound to anything else,
      `f = if c a else b`, has no body behind it and is refused: "a function
      value that names no definition".
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
      every part of it is itself constant (`isConstantForm`,
      `src/check/code_reifier.zig` (`isConstantForm`)).
- [x] A field read of a record argument, which describes as a `Field` over the
      `Record` the call fixed.
- [x] Several calls of one template, each producing its own description.
- [ ] An interpolated literal of a type of your own as an argument. The checker
      binds every interpolated value to a name, so it is refused as "template
      needs a constant" however constant its pieces are
      (`src/check/code_reifier.zig` (`isConstantForm`)).
- [ ] An argument computed while the program runs. Refused at the argument,
      with a report that points there rather than at the template ("Template
      Needs A Constant", `buildStagedCodeReport` in `src/check/report.zig`).
- [x] A template whose argument is a function. The parameter binds to the
      definition the argument names (`templateCallee`,
      `src/check/code_reifier.zig` (`templateCallee`)), so a call on it names that row, and a
      lambda argument lifts into a row that reads the block around it. The
      argument is a function rather than a `Code`: `Code(f)` is opaque and not
      callable, so a template calling a `Code` parameter does not check, and
      making it callable is a change to the typing rules. A function argument
      that names no definition, a record field or an `if`, stays refused: "a
      function value that names no definition".
- [x] A name as an argument, bound to a literal at the top level or in an
      imported module. The walk follows the name to the value it holds and
      folds that value in (`nameHoldsConstant`,
      `src/check/code_reifier.zig` (`nameHoldsConstant`)), so `limit = 7` passed to a template
      describes as the `7`.

## 13 What every node carries

`Code` is opaque, so only the compiler builds one. The node unions are
transparent, because a translator `match`es them from outside `Builtin`, and
opacity blocks matching as firmly as construction. Only `Code` is
auto-imported, so a user module may still be named `Ty` or `Node`.

- [x] `Node { op, args, ty, speculatable }` on every node, so a translator can
      name a type and know whether it may evaluate the node where the body
      would not. `speculatable` is exact: a builtin not on the normal form's
      list is not speculatable, and neither is a node over one
      (`src/build/roc/Builtin.roc:24015`). A translator for a target without
      short-circuit evaluation reads it on the nodes of an `And` or `Or`
      operand.
- [x] The description holds no source regions. The compiler keeps a table from
      each node to the source places it came from (`originAt`,
      `src/check/code_reifier.zig` (`originAt`); `src/reify/provenance.zig`).
      `Code.refuse_at` is the one reader: it names a row `id` and a node
      index, and the compiler reports the message at every source place the node
      came from, with the calls that reached it
      (`src/build/roc/Builtin.roc:24211`). `Code.Inlined.refuse_at` does the
      same for the `inline` view (`src/build/roc/Builtin.roc:24180`). A
      translator that runs when the program runs crashes with the message
      instead. Two sites with one normal form are equal by `Code.is_eq`, which
      ignores the site key.
- [x] The order of `nodes` comes from the graph alone, so a refactor that keeps
      the row's meaning keeps every index (`src/build/roc/Builtin.roc:24047`).
- [x] `Node.children` and `Ty.children`, so a pass with nothing to say about any
      one kind walks a description without an arm per kind
      (`src/build/roc/Builtin.roc:24027`, `:23703`). `Op.regions` and
      `Op.repeats` answer the same for regions (`src/build/roc/Builtin.roc:23991`).
- [x] `Ty.numeric`, the question an operation site asks about a number, and
      `Ty.name`, the answer a refusal names a type with
      (`src/build/roc/Builtin.roc:23727`, `:23757`).
- [x] `Row.node`, `Row.uses`, `Graph.row`, `Graph.root_row`, `Graph.inputs` and
      `Graph.to_tree` (`src/build/roc/Builtin.roc:24061`, `:24071`, `:24088`,
      `:24095`, `:24101`, `:24108`). `Graph.inputs` lists the fields of the
      root's one record parameter for a translator that binds each field to an
      input of its host.
- [x] Comparing two `Ty` values. `Code.Ty` declares `is_eq : _` and
      `to_hash : _` (`src/build/roc/Builtin.roc:23689`), so `a == b` and
      `a != b` are the derived structural comparison. Every other description
      type declares them too, and so do `Code` and `Code.Inlined`
      (`src/build/roc/Builtin.roc:24197`, `:24171`).

## 14 Code positions, unannotated helpers and reports

- [x] A `Code` is a parameter of the outermost function of an annotation, or
      what that function returns. A callback parameter, a record field and a
      tuple item are refused with "code is not allowed here" at the `Code`
      the user wrote (`rejectMisplacedStagedCode`, `src/check/Check.zig`).
      Pinned by `test/cli/StagedNestedCallback.roc`.
- [x] A `Code` behind a transparent alias, `MyCode : Code(I32 -> I32)`, is a
      `Code` position. A parameter of type `MyCode` stages, and a record field
      of type `MyCode` is refused (`stagedCode`, `src/check/Check.zig`). Pinned
      by `test/cli/StagedAliasParam.roc` and `test/cli/StagedAliasPosition.roc`.
- [x] A call is a template call only when the callee's own return type is a
      `Code`. A generic function that takes a `Code` and hands it back is an
      ordinary call (`claimOrRejectCodeCall`, `src/check/Check.zig`). Pinned by
      `test/cli/StagedGenericPassThrough.roc`.
- [x] A lambda written at a `Code` position calls an unannotated helper at the
      types its call fixes. No compiled body holds the lambda, so the
      checked module collects its value references and the evidence of every
      call inside it as it does for the body of a named function
      (`collectStagedLambda`, `src/check/checked_artifact.zig`). Pinned by the
      staging case "a lambda written at the site calls unannotated helpers at
      the types it fixes" and by `test/cli/StagedInlineUnannotatedCall.roc`.
- [x] An unannotated helper calls another unannotated generic helper. An
      evidence entry that forwards to the caller's own evidence is resolved
      against the evidence the walk holds, the way Monotype resolves it through
      its evidence chain (`supply`, `src/check/code_reifier.zig`). Pinned by the
      staging case "an unannotated helper calls another at the evidence its
      caller supplied".
- [x] A binder keeps the name the author wrote. The canonicalizer stores the
      identifier on the pattern, the checked module copies it to
      `CheckedPatternBinder.name`, and the walk reads that field. It never
      slices source text. A string pattern capture is the name inside `${ }`,
      an `as` pattern is the name after `as`, and an associated item takes its
      declared name. Pinned by `test/cli/StagedCaptureNames.roc`.
- [x] A site that cannot be described becomes a `runtime_error` in the checked
      body, whether or not the caller asked for compile-time problems. Only the
      `staged_code` report depends on that request (`reifyStagedCode`,
      `src/check/checked_artifact.zig`). So no later stage meets a site with no
      description. A site whose `f` holds an error is retired earlier by
      `poisonUndescribableStagedCode` (`src/check/Check.zig`), by the
      definition or the top-level `expect` that owns the site. Pinned by
      `test/cli/StagedPoisonedSite.roc` and
      `test/cli/StagedTopLevelExpectPoison.roc`.
- [x] A refusal by `Code.refuse_at` reports the calls that reached the node as
      structured frames (`RefusalCall`, `src/check/problem/types.zig`). A call
      in the reporting module keeps its region, so the report places it with
      the same line mapping as every other region of that module. A call in
      another module names the module, the line and the column
      (`addRefusalCalls`, `src/check/report.zig`).

---

## What the remaining unticked boxes cost

| Gap | What it costs |
| --- | --- |
| No function taken from a list | `[double].first()` and then a call: simplifying does not read a closure back out of a list, so the call stays an `Apply` and the site is refused; a function chosen by an `if` between known functions does describe |
| No name whose value exists only at run time | a lambda cannot read a parameter, binder or `var` of the function it is written in; the value becomes a parameter of the lambda, or a template fixes it |
| No computed function at a site | `main = Stage.describe(doubler)` where `doubler = make(2.0)` is refused, because the site's root needs a lambda; the author writes `\|x\| doubler(x)` at the site, or writes `doubler` as a lambda. A use of `doubler` inside a described body, and an exact alias, `same = add_one`, do describe |
| No custom string interpolation through a `?` | a `from_interpolation` of a type of your own whose body can leave early, with a `?`, or that is generic in the item type of its assembler, is refused at the literal; every other one describes (the box above) |

A shader or a codec is written as one function calling others, over as many
modules as its author split it into, and that describes whole: the compiler
walks the callees and ships their descriptions in the table, and every builtin
either folds into a node or arrives as a `Prim` under the name the compiler
knows it by. A higher-order call describes too, because the walk resolves a
function at the site that fixes it rather than handing a translator a value it
has nowhere to put.

## How each box was checked

A ticked box is proven by one of three things: a case in
`src/eval/test/eval_staging_tests.zig`, a fixture under `test/cli/`, or a probe
compiled with `roc <file>` where a translator prints `ok` for a root. An
unticked box quotes the reason line the compiler printed for the same probe.
The walk's graphs are also pinned by `src/compile/test/code_reifier_test.zig`,
and the position rule's reports by snapshots such as
`test/snapshots/staged_code_outside_staged_position.md`. The reifier is checked
against Roc's semantics too: `Interp.eval` runs a description
(`examples/reifying/glsl/Interp.roc:55`), and the `expect`s of
`examples/reifying/glsl/main.roc:94` and `:116` compare its answer with what
Roc computes for the same function.

Working on the reifier:

| Task | What to know |
| --- | --- |
| run the GLSL example | `roc test --no-cache examples/reifying/glsl/main.roc`; the CLI suite runs the same command (`src/cli/test/parallel_cli_runner.zig:3422`) |
| run the other examples | the CLI suite runs `hello`, `sql` and `dbsp` the same way (`src/cli/test/parallel_cli_runner.zig:3424` to `:3429`) |
| a call into another module or a builtin | `code_reifier_test.zig` builds its walk with a `StagedLookup` (`src/compile/test/code_reifier_test.zig:94`); the paths that need more are pinned in `eval_staging_tests.zig` |
| a `Code` union gains a variant | the staging cases still pass with it unlisted; the GLSL example and `test/cli/StagedMatch.roc`, which match every variant, are what fail |
| the rules of the normal form change | the version and the fingerprint table in `src/reify/mod.zig:33` to `:62` must move together, and an entry there is never edited |
| a field added to `NodeStore` or `CommonEnv` | it moves the sizes pinned in `test/serialization_size_check.zig:41-42` and needs a `CACHE_VERSION` bump (`src/compile/cache_config.zig:364`) |
| lines added to `Check.zig` and the other files `run-check-type-checker-patterns` scans | its excluded ranges are line numbers (`src/build/check_runner.zig:195`), so `minici` can fail at code the change never touched |

Line numbers into `src/build/roc/Builtin.roc`, the test files and the example
files were last checked against the `reify` branch at `f3269bdd24`. A line number into `src/check/code_reifier.zig`, `src/check/Check.zig`
or `src/check/report.zig` drifts with every edit, so find the function by its
name when a number misses.
