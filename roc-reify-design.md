# Code reification: the pure-function surface a description covers

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
| `Val` | `Param(k)`, `Node(i)`, `Out({ node, k })`, `Arg({ owner, k })`. | `src/build/roc/Builtin.roc:23847` |
| `Region`, `End` | A body and how it ends: `Value`, `Jump`, `Return`, `Continue`, `Break`, `Branch`. | `src/build/roc/Builtin.roc:23880`, `:23897` |
| `Key` | The value one `Switch` arm takes: `Tag`, `Lit`, `Len`, `AtLeast`, `Default`. | `src/build/roc/Builtin.roc:23864` |
| `Tree` | One row as nested expressions, from `Graph.to_tree`. | `src/build/roc/Builtin.roc:24138` |

| View | Type | What stays a row |
| --- | --- | --- |
| `graph` | `Code(f)`, read with `Code.graph` | A recursive row, a row called from two or more places, and a row a `Closure` names. |
| `inline` | `Code.Inlined(f)`, read with `Code.Inlined.inline` | A recursive row, and a row whose body still ends in `Return` after simplification (an early `return` that does not fold into a branch). Every other row is inlined, and a `Closure` of any non-recursive row is a `Lambda` region. |

The `graph` view inlines a helper called from one place. The rules are in
`src/reify/views.zig:1`. The normal-form version is 3
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
- [ ] A literal of a type of your own whose conversion is a Roc function of the
      package being described. "a conversion whose argument the compiler
      generates". The argument is a number the compiler writes, and a row
      parameter has the type the method declares, not `I128` or `F64`
      (`src/check/code_reifier.zig` (`dispatchWithArgs`)).
- [ ] A literal of a type of your own through `from_interpolation`. "a custom
      string interpolation". The conversion runs in two stages (design.md,
      "An interpolated string literal converts in two stages"):
      `from_interpolation` reads the segments while the compiler runs and
      hands back an assembler, and the value is that assembler applied to the
      interpolated values. The assembler is a function value the compiler
      computes, and no node can apply it
      (`src/check/code_reifier.zig` (`dispatchExpr`)). Pinned by the staging case "an
      interpolated literal of the author's own type is refused".
- [x] A literal of a type of your own in a `match` pattern. The pattern binds
      the matched value, and the checker's own equality of that type against
      its conversion of the literal becomes a `Bool` `Switch`
      (`src/check/code_reifier.zig` (`guardedTest`)).
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
      Two cases stay refused. A computed value of another package is a body of
      that package, which the walk does not read (N8h): "a computed constant
      of another package" (`src/check/code_reifier.zig` (`foldedConstant`)). A top-level
      value that computes a function names no definition, so a call on it has
      no row to name: "a top-level constant that computes a function"
      (`src/check/code_reifier.zig` (`reachedHere`)).
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
- [ ] A name the compiler does not fix: a function parameter, a branch or loop
      binder, or a `var`, whether the lambda reads it or a replayed statement
      does. Refused as a capture, naming it
      (`src/check/code_reifier.zig` (`unboundRef`)).

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
- [x] A call to a function of another package. It describes as a `Prim` whose
      `owner` is the module name and whose `method` is the function name. Its
      body is not read (N8h), and a translator maps it by name, as the GLSL
      example maps `Glsl.Vec3.scale` (`src/check/code_reifier.zig` (`resolvedTarget`)).
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
      which is how a hand-written `encoder_for` is run. A function of the
      compiler or of another package used as a value is refused: "a function of
      the compiler or of another package used as a value"
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
      function, `f = make(2)`, has no forwarded lookup and stays refused as "a
      top-level constant that computes a function". Pinned by
      `src/eval/test/eval_staging_tests.zig:1758` ("staging - a call through an
      alias calls the row of the function it names") and
      `src/compile/test/code_reifier_test.zig:531`.
- [x] A function chosen by an `if` between known functions, and then called:
      `(if c double else triple)(x)`. The call is first an `Apply` of the value,
      and simplifying turns each `Apply` whose function is a known closure into
      a `Call` of its row, so the result is a `Switch` over the calls. `Apply`
      is no `Op` of the description: it either resolves or the site is refused.
      Checked with a probe of each form.
- [ ] A function taken from a list and then called, `Ok(g) => g(x)` in a
      `match` on `[double].first()`. "a call to a function value that no
      simplification resolves" (`src/check/code_reifier.zig` (`normalize`), pinned by
      `src/compile/test/code_reifier_test.zig:2304`): simplifying does not read a
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
      (`src/eval/test/eval_staging_tests.zig:1674`). The empty aggregate is
      covered by the previous box.
- [x] Record update, `{ ..r, b: 1 }`, expanded into the `Record` it stands
      for: the fields the update wrote, and every other field of the type read
      out of the subject (`src/check/code_reifier.zig` (`recordExpr`)). One over a record
      with an optional field is refused: "a record update over a record with an
      optional field". The result carries whatever the subject had there, and a
      `Field` read of a field that may be absent is not that.
- [ ] An unset record field (`b: _`). "a record literal that unsets an optional
      field" (`src/check/code_reifier.zig` (`recordExpr`)). Pinned by the staging case
      `staged_unset_field` (`src/eval/test/eval_staging_tests.zig:1306`).
- [x] An optional record field (`timeout ?: U64`), as the `presence` a
      `Ty.Record` entry carries and `OptField(Str)` for the `.?timeout` that
      reads it (`src/check/code_reifier.zig` (`fieldAccessExpr`)). The read hands back the
      `Try(a, [MissingField])` the value sits in rather than the value, which
      is why it is a node of its own. A `.?` that is not the last segment of a
      path is refused: "a field read through an optional field". The checker
      gives such a path one flat `Try` however many optional segments it holds,
      and nested nodes cannot say that.

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

| Refused pattern | Reason |
| --- | --- |
| `{ a, ..others }` | "a record pattern whose `..` binds a name". It binds a record the pattern builds out of what is left rather than one it takes apart. |
| A string interpolation pattern | "a string interpolation pattern" (`src/check/code_reifier.zig` (`patternFormName`), pinned by `src/compile/test/code_reifier_test.zig:1824`). A target that cannot split a string has nothing to read. |
| A tag pattern on a type that is not a tag union | "a tag pattern on this type" |

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
- [x] A row a sibling argument or a later clause fixes. A site's rows close
      when the binding holding it generalizes (`groundPendingStagedRows`,
      `src/check/Check.zig`), not when the site finishes, so
      `join(orders, |c, o| ..)` takes its row from `orders`, and a second clause
      reading the same parameter record adds the fields it reads. A row nothing
      else fixes closes on exactly the fields the lambda reads.
- [x] An open record, or a record extended by a variable. A row is a quantified
      variable, so a site fixes it the way it fixes any other. `matchRecord`
      binds the row to the record the site named
      (`src/check/code_reifier.zig` (`matchRecord`)) and the walk reads that binding where
      an extension chain ends in a variable
      (`collectRecordFields`, `src/check/code_reifier.zig` (`collectRecordFields`)), so
      `take_n : { n : U16, ..rest } -> U16` at `Code({ n : U16, m : U16 } -> U16)`
      describes its parameter as `{ n : U16, m : U16 }`, and the same
      definition at `Code({ n : U16 } -> U16)` describes it as `{ n : U16 }`,
      in a row of its own. A site's own `f` closes its rows before the walk
      reads them (`groundPendingStagedRows`), so the "open record" refusal
      below is a guard that no `Code` position reaches. What the row binds to
      is the site's whole record
      rather than the fields the definition did not name, because the residual
      is no type the artifact holds; the two sets are the same once a field a
      nearer link already collected is dropped
      (`collectField`, `src/check/code_reifier.zig` (`collectField`)). A row nothing fixes
      is still refused as "an open record" (`src/check/code_reifier.zig` (`collectRecordFields`)):
      `Ty.Record` is a closed list of fields, so a record with no fixed set of
      them has no shape to write.
- [ ] A tag union whose row is still open, so its extension is a variable the
      checker did not close. "an open tag union"
      (`src/check/code_reifier.zig` (`collectVariants`)): the union stands for many, and a
      description is monomorphic.

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
- [ ] Derived `is_eq` over an empty tag union. "derived equality on an empty tag
      union": nothing inhabits it, so there is no pair of values to compare
      (`src/check/code_reifier.zig` (`eqOver`, `tagUnionEq`)).
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
- [ ] Derived `is_eq` or `to_hash` through an opaque nominal that derives it.
      An opaque type's `Ty` names it without its backing, and the derivation is
      that backing's comparison, so expanding here would describe a
      representation the description hides everywhere else. The refusal names
      the type (`src/check/code_reifier.zig` (`nominalEq`)). One that writes its own
      method describes as the call, which hides it.
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

---

## What the remaining unticked boxes cost

| Gap | What it costs |
| --- | --- |
| No function taken from a list | `[double].first()` and then a call: simplifying does not read a closure back out of a list, so the call stays an `Apply` and the site is refused; a function chosen by an `if` between known functions does describe |
| No name whose value exists only at run time | a lambda cannot read a parameter, binder or `var` of the function it is written in; the value becomes a parameter of the lambda, or a template fixes it |
| No computed function at top level | `doubler = make(2.0)` names no definition, so a call on it is refused; the author writes it as a lambda, `doubler = \|x\| x * 2.0`, or as a template; an exact alias, `same = add_one`, does describe |
| No computed value of another package | `limit = xs.len()` in a package the app depends on is refused, because its body is that package's; a value written as data still folds |
| No open tag union | a result whose row nothing closed has no one set of variants to describe |
| No unset optional field | `{ a: v, b: _ }` is refused |
| No string interpolation pattern | a `match` on `"a${x}"` is refused |
| No literal conversion written in the package | `from_numeral` or `from_interpolation` in the package being described is refused at the literal; a conversion of a builtin or of another package describes |

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
| run the GLSL example | `roc test --no-cache examples/reifying/glsl/main.roc`; the CLI suite runs the same command (`src/cli/test/parallel_cli_runner.zig:3033`) |
| run the other examples | the CLI suite runs `hello`, `sql` and `dbsp` the same way (`src/cli/test/parallel_cli_runner.zig:3035` to `:3040`) |
| a call into another module or a builtin | `code_reifier_test.zig` builds its walk with a `StagedLookup` (`src/compile/test/code_reifier_test.zig:142`); the paths that need more are pinned in `eval_staging_tests.zig` |
| a `Code` union gains a variant | the staging cases still pass with it unlisted; the GLSL example and `test/cli/StagedMatch.roc`, which match every variant, are what fail |
| the rules of the normal form change | the version and the fingerprint table in `src/reify/mod.zig:33` to `:62` must move together, and an entry there is never edited |
| a field added to `NodeStore` or `CommonEnv` | it moves the sizes pinned in `test/serialization_size_check.zig:41-42` and needs a `CACHE_VERSION` bump (`src/compile/cache_config.zig:316`) |
| lines added to `Check.zig` and the other files `run-check-type-checker-patterns` scans | its excluded ranges are line numbers (`src/build/check_runner.zig:126`), so `minici` can fail at code the change never touched |

Line numbers in this file were last checked against the `reify` branch at
`9d0514ae2a`. A line number into `src/check/code_reifier.zig`, `src/check/Check.zig`
or `src/check/report.zig` drifts with every edit, so find the function by its
name when a number misses.
