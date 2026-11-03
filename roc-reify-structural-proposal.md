# Structural Types in Code Reification

Status: proposal, revision 1. Baseline: branch `reify` at `66d2712e03`, plus the
uncommitted working-tree edits of the opaque-proposal session (`src/check/code_reifier.zig`,
`design.md` and others). All `path:line` references are to that working tree on
2026-10-29. Each reference also names its function, so a reader can find it again
after the lines move. Probes ran with `zig-out/bin/roc`, built 2026-10-29 20:56 from
the same tree.

Companion documents: `roc-reify-proposal.md`, `roc-reify-opaque-proposal.md`,
`roc-reify-normal-form.md`, and design.md "Code Reification" (`design.md:23589`).

Source of the limits: the structural-types analysis of the SurrealDB example
(`examples/reifying/surreal`), section 5.1, limits Y1 to Y7, its P5 read-view limit,
and the "Findings" table of `examples/reifying/surreal/README.md`. This proposal
checks each limit again with the current compiler, reduces it to a minimal program,
finds its cause in `src/`, and adds four limits that the checks found (Y8 to Y11).

## 0. Summary

### 0.1 Priority Table

| # | Limit | Priority | Kind | Why this priority | Difficulty |
|---|---|---|---|---|---|
| Y10 | The checker accepts `{ ..r }` at any `r` (`Str`, a tag union, an opaque type). Monotype then stops with an invariant panic. No reification is needed | P0 | bug, compiler crash | A crash on a program that type-checks. It also decides the rule that Y3 must follow | M: a declared typing rule in the checker, tests on both sides |
| Y9 | A `Code` site inside an unannotated generic function is described once, with the open row sealed to `{}`. The translator gets a parameter type that is not the type the program runs at | P0 | bug, silent wrong description | Silent. A translator that reads parameter types (`Graph.inputs`, typed columns) gets wrong data and gives no error | S for the interim refusal (Stage 0). D1 removes the limit |
| Y2 | An annotated open-row helper that calls another open-row helper is refused at the inner helper. A named site whose root is an unannotated helper that forwards a `where` requirement to another helper is refused | P0 | bug | Helper libraries over open rows are the normal way to share predicates in the DSL. The same chain written as an inline lambda works | M (D2) and S (D3) |
| Y1 | A `Code` site inside a function whose annotation has an open row variable is refused. Reusable query fragments `Query(p, { name : Str, ..r }) -> Query(..)` are impossible | P1 | missing feature | Largest API gain: fragments compose at the query level, not only at the predicate level. Needs Y2 first | L to XL: publication, walk, Monotype, Boxy |
| Y3 | A record extended by a nominal record (`Ref(r) := { ..r }` at `r = Owner`, `Owner := {..}`) runs as a program, but the reifier refuses it | P1 | gap: the walk does not follow a rule that Monotype has | Blocks `Ref` read views for nominal rows and for self-linked rows (analysis P5). Small after Y10 | S |
| Y7 | roc-lang/roc#12705: "top-level Monotype definition has free locals" in `lift` | P1 | bug, compiler crash, not in reify code | A crash. The library avoids it with a code rule. Not in this proposal's scope | External (`src/postcheck/monotype_lifted/lift.zig`) |
| Y5 | `Code.Ty` drops a field default (`??`). The field is `Required` | P2 | missing feature | Schema `DEFAULT` from the type. The library has `.default(..)` today | M: API change, walk, translators |
| Y6 | No type description without a lambda | P2 | missing feature | `Surreal.table("owner")` instead of `Surreal.table("owner", \|o\| o)`. Cosmetic until D1 exists | S for closed types; generic use needs D1 |
| Y8 | A captured record with an optional field, at any depth, is refused at a bound site. So a captured `Id(row)` is refused when `row` has an optional field | P2 | gap; the `Id` case done by option A (see "Y8 Option A") | `select_where(orders, \|o\| o.customer.id() == who)` fails for most real rows. A parameter record works today | M; the `Id` case: `Named` carries type arguments, and `Id` holds no phantom |
| Y4 | A constant whose value comes from a `Code` (a `Table` built with `Surreal.table(name, \|r\| r)`, a `Code.type_id(..)` constant) cannot be read in a clause | P2 | gap plus a misleading report | A library change avoids it. The report points at the table definition, not at the clause | S (diagnostic only); no new description form |
| Y11 | A walk refusal in the site's own module names only the refused region, never the site that reached it | P2 | diagnostics | Y2 and Y4 reports point at a helper or a table and do not name the failing clause | S |

P0: fix before new reification features. P1: next. P2: when the API needs it.

### 0.2 Decisions

| # | Decision | Limits | Ships in |
|---|---|---|---|
| D1 | Instance descriptions. A `Code` site whose function type mentions a quantified variable of the template that holds it is an instance site. It has no description of its own. Each closing use of the template (a use whose types fix those variables) describes it at the use's types, in the module of the use, and records the result on the use. Monotype reads the description from the use when it specializes the template; Boxy passes it as a hidden argument. This is how `where` evidence already flows | Y1, Y9 | Stage 2 |
| D2 | A type reference names the frame its variables belong to. `TypeRef` gains a frame. `fixedType` reads the reference's own frame, not the reader's current frame. The instance key hashes each binding through its frame | Y2 (annotated) | Stage 0 |
| D3 | A named site supplies the evidence of its root. `reifyNamedSite` reads the evidence the checker recorded on the site's lookup and supplies it to the root, as a call supplies evidence to its callee | Y2 (unannotated) | Stage 0 |
| D4 | Record extension well-formedness, a declared typing rule: a record extension is a record, a row variable, or a nominal whose backing is a record that the applying module can inspect. Anything else is a type error at the application. The walk follows an inspectable nominal extension into its backing, as Monotype's `flattenRecordRow` does | Y10, Y3 | Stage 0 |
| D5 | `Code.Ty` record presence gains `Default(Value)` and `DefaultComputed`. A default that is a constant form is its value; any other default is `DefaultComputed` | Y5 | Stage 3 |
| D6 | `Code.ty_of : Code.Proxy(t) -> Code.Ty`, an intrinsic like `Code.type_id`. Publication computes it where `t` is closed at the call. Inside a generic function it is an instance constant of D1 | Y6 | Stage 3 (closed), Stage 2 + 3 (generic) |
| D7 | No description form for a `Code` value or an identity value inside a description. A clause that reads a constant that holds one is refused at the clause, with a message that names the constant and the fix | Y4 | Stage 0 |
| D8 | The `Id` case is done by option A, not by opaque D5: `Code.Ty.Named(name, args, backing)` carries the nominal's type arguments, and `Id(row) := { table : Str, key : Str }` holds no phantom, so a captured `Id` holds only its table and key. A structural optional field in a slot binds as `Value.Absent` where the record does not hold it (Q9, done) | Y8 | Done: the `Id` case and `Value.Absent` |
| D9 | A walk refusal outside the site's own lambda names the site that reached it, in the site's module too, as `StagedCode.foreign` already does for another module | Y11 | Stage 0 |

Y7 is a referenced item (section 3.11). It has no decision here.

## 1. Problem and Evidence

The SurrealDB example builds queries from reified Roc lambdas. Structural types
carry most of the DSL: the reifier sees every field path, every link hop and every
record that a clause builds. The limits below are the places where the compiler, not
the library, stops the DSL.

### 1.1 Repro Setup

Every repro below is a headerless app next to the module `Db.roc`. Run each with
`roc <file>.roc`. The outputs in this proposal are the exact outputs of the baseline
compiler (blank lines and stack frames removed).

```roc
## Db.roc: a small translator. Each method writes what the reifier gave it.
Db :: {}.{
	Q(row) := { log : Str }.{
		## Writes the parameter types of the described predicate.
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, code| Q.({ log: "${q.log} | filter ${Str.inspect(code.graph().root_row().params)}" })

		show : Q(row) -> Str
		show = |q| q.log
	}

	from : Str -> Q(row)
	from = |name| Q.({ log: name })
}
```

### 1.2 Probe Results

| Repro | Written | Result today |
|---|---|---|
| `y1.roc` | `named_only : Db.Q({ name : Str, ..r }) -> ..`, body `q.filter(\|x\| x.name != "")` | refused: "cannot reify a polymorphic function", "an open record" |
| `y9.roc` | the same fragment unannotated, with the direct call `Db.Q.filter(q, ..)` | accepted. The parameter type is `{ name : Str }` at `Pet` and at `Owner`. The direct filter at `Pet` gives `{ age, id, name }` |
| `y2a.roc` | `named_in_oslo : { city : Str, name : Str, ..r } -> Bool` calls `in_oslo : { city : Str, ..r } -> Bool` | refused at `in_oslo`: "an open record" |
| control | the same chain, outer helper unannotated; or an inline lambda `\|p\| in_oslo(p.owner)`; or an annotated chain over a non-row variable `Bx(a)` | accepted |
| `y2u.roc` | named site `owners.filter(city_is_oslo)`, `city_is_oslo = \|x\| same(x.city, "Oslo")`, `same = \|a, b\| a == b`, both unannotated | refused at `a == b`: "cannot reach this definition", "a method this call names no target for" |
| control | the same helpers through `\|o\| city_is_oslo(o)`; one unannotated helper as a named site | accepted |
| `y3.roc` | `Ref(r) := { ..r }`, `Owner := {..}`, `p.owner.name` in a clause | refused: "a record extended by a type that is not a record" |
| `y3run.roc` | the same types, no reification | runs, prints `Bob Ada` |
| control | `Owner` as an alias | accepted |
| `y10.roc` | `show : Ref(Str) -> Str`, no reification | compiler panic in Monotype: "instantiation record row extended into a non-record type". The same for `Ref([A, B])`; `Ref(Dict(Str, Str))` panics with "... into a non-inspectable named type" |
| `y4.roc` | a clause reads `vets.key("ruth")`, `vets = T.table("vet", \|v\| v)` | refused at the table's lambda: "a reified value that is not a function". The clause is not named |
| control | the same with a handle that holds no `Code` value | accepted |
| `y4id.roc` | a clause reads `owner_tid = Code.type_id(owner_proxy)` | refused at the constant: "cannot reify this expression", "this expression" |
| `y5.roc` | `Med := { id : Str, stock : I32 ?? 0, tags : List(Str) ?? [], note ?: Str }`, `\|m\| m` | `stock` and `tags` are `Required`; the defaults are not in the description |
| `y8.roc` | bound site captures `who : Id(Customer)`, `Customer : { id : Str, zip ?: Str }`, `Id(row) := { key : Str, phantom : List(row) }` | refused: "a captured record with an optional field". The same capture at a row with no optional field binds |
| Y7 | `roc test --no-cache main.roc` of `scratchpad/repro-freelocals` | compiler panic in `lift`, roc-lang/roc#12705, open |

### 1.3 Other Limits Reviewed

| Limit (source) | In this proposal? | Reason |
|---|---|---|
| P5: `Ref` read views refused for self links and nominal rows (analysis 2.3) | yes, as Y3 | A self link needs a nominal row (an alias cannot be recursive: "The type alias Owner references itself, which is not allowed"), and a nominal row in `Ref` is Y3 |
| README finding 1: a captured `Id(row)` whose row has an optional field | yes, as Y8 | Verified. The cause is general: any captured record with an optional field, at any depth |
| README finding 2: a table-built constant in a clause | yes, as Y4 | Verified. Also covers `Code.type_id` constants |
| Unannotated query fragment in method form (`q.filter(..)` on an unresolved `q`, analysis `p6b.roc`) | no, Q10 | Type error: the method call is a `where` requirement, so its argument is checked as a plain function before any `Code` position exists. Making it a `Code` position changes a typing rule. With D1 an annotated fragment works |
| README: "Each nominal with a `Code` method repeats the cut" | no | A cut design question (opaque proposal D3), not a structural-type limit |
| README: "Parameters of a database function are `$a1`, `$a2`" (a row has no parameter names) | no | A small feature of `Code.Row`, not a structural-type limit. A separate item |
| README: "`Array.sort` is not available" | no | Opaque proposal D7 (done) gives `List.sort` its evidence. Library work now |
| README: "A database-only function stops the program outside a clause" | no | Compile-time evaluation, not the reifier |
| README: "`==` on a union is refused", "A `match` whose arms return whole records is refused" | no | Translator choices. The description has `Derived` and the arms |

## 2. Current Behavior

### 2.1 How the Walk Fixes a Generic Definition's Types

| Step | What it does | Where |
|---|---|---|
| Instance of a callee | `instantiationOf` matches the callee's scheme against the type the call fixed. Each quantified variable gets a `TypeRef` | `src/check/code_reifier.zig:7569` |
| Non-row variable | bound to `use.reader.resolvedType(fixed)`, which resolves it in the caller's frame at once | `matchType`, `:7734-7802` |
| Record row variable | bound to the whole use record (`use`), whose own tail can be a variable of the caller's frame. Not resolved at bind time | `matchRecord`, `:7809-7857`, binding at `:7855` |
| Tag row variable | never bound. A description names only the variants the definition names | `matchTagUnion`, `:7923` |
| A `TypeRef` | `{ reader, id }`. The reader is a module (`*Reifier`), not a frame | `:346-349` |
| Frame | `describeDefinition` puts the instance's substitution on the reader (`self.substitution = ..`) and restores it at the end | `:1151`, `:1169-1186` |
| Reading a variable | `fixedType` reads `self.substitution`: the current frame of that reader | `:8077-8081` |
| Instance key | `instantiationKey` hashes `rootKey(bound.id)` of each binding | `:8038` |
| Row tail with no binding | a flex tail with an empty row default seals to `{}`; any other open tail is refused with "an open record" | `collectRecordFields`, `:7348-7354` |
| Extension that is not a record | refused: "a record extended by a type that is not a record" | `:7363-7369` |

### 2.2 How Sites Are Described and Lowered

| Stage | Behavior | Where |
|---|---|---|
| Publication | each site is described once (`.named_function`, `.inline_lambda`, `.template_call`). A `.template` or `.template_callee` site is skipped | `reifyModuleSites`, `src/check/code_reifier.zig:9805`; `walkSite` |
| Named site | the root is described at the site's `f` (`fixed`); no evidence is supplied to the root | `reifyNamedSite`, `:9954` |
| Template call | a function that returns a `Code` is described at each call, with the call's arguments | `reifyTemplateCall` `:902`, `templateSite` `:918` |
| Stored result | one `CheckedCodeSite.node` per site | `src/check/checked_artifact.zig:2551-2557` |
| Lowering | restores that node where the site stands; walks no function | `restoreCodeSiteAtNode`, `src/postcheck/monotype/lower.zig:47593`; design.md stage table `:23603` |

So a site has one description. A site inside a generic function is described with
the function's own types. The design text says: "A description is a specialization
read without lowering, so the walk reads types by Monotype's rules" (`design.md:23612`).
Monotype specializes the function per instance. The walk does not.

### 2.3 How Types With Defaults and Extensions Are Converted

| Checked type | `Code.Ty` | Where |
|---|---|---|
| defaulted field | `Required` ("a defaulted field is filled in") | `recordTy`, `src/check/code_reifier.zig:7298-7316` (`.required, .defaulted, .undetermined => false` at `:7306`) |
| optional field | `Optional` | same |
| record extended by a nominal | refused | `:7366-7369` |
| default identity | the checker has it: `CheckedFieldKind.default` (`origin_module`, `expr_node`) | `src/check/checked_artifact.zig:2585-2616` |
| Monotype: record extended by a nominal | flattened into the nominal's backing when the backing is inspectable and not recursive; anything else is an invariant panic | `flattenRecordRow`, `src/postcheck/monotype/solve.zig:7938-8005` (invariants `:7982`, `:7984`, `:7988`, `:8005`); test "record row follows an inspectable nominal record extension" `:12671` |

### 2.4 How a Constant and a Capture Are Read

| Source | Description | Where |
|---|---|---|
| top-level constant | its definition is walked where the name stands | `foldedConstant`, `src/check/code_reifier.zig:2994` |
| a lambda at a `Code` position met inside a walked body | refused: its checked type is `Code(f)`, not a function | `lambdaRow` `:1223-1237` (also `:1301`, `:1586` with the same text) |
| `code_from_lambda` expression (a `Code.type_id` or `Code.prim` call) met inside a walked body | refused with the form name ("this expression") | `exprRef`, `:2112-2117` |
| captured value at a bound site | an input slot whose shape is computed by `slotShape`; a record field marked optional stops it | `slotShape` `:8690`, refusal `:8743` |
| `Code.Value` | has no form for an absent field | `src/build/roc/Builtin.roc:24480-24495` |

## 3. Design, Per Limit

### 3.1 Y10 and D4: Record Extension Well-Formedness (P0)

Repro `y10.roc`:

```roc
Ref(r) := { ..r }

## No reification: a type that extends a record by `Str`.
show : Ref(Str) -> Str
show = |_x| "ok"

main! = |args| {
	echo!("${if args.len() > 100 show(crash "never") else "skipped"}\n")
	Ok({})
}
```

Output:

```
Roc hit an internal compiler error. This is a bug in the compiler, not in your code.
Work in progress on thread .. (compile worker 5), outermost first:
  post-check    monotype
thread .. panic: postcheck invariant violated: instantiation record row extended into a non-record type
src/postcheck/monotype/solve.zig:8005:36: in flattenRecordRow
src/postcheck/monotype/solve.zig:9488:61: in planNodeContent
```

`Ref([A, B])` gives the same panic. `Ref(Dict(Str, Str))` gives "instantiation record
row extended into a non-inspectable named type" (`solve.zig:7984`).

Root cause: the checker substitutes a type argument into a record extension and
does not check that the result is a record row. Monotype's `flattenRecordRow` treats
a non-record extension as a compiler invariant (`solve.zig:8005`). So the checker
breaks an invariant that Monotype depends on.

Rule (to declare in design.md, near "Type Alias Invariant", `design.md:4244`):

> Record Extension Well-Formedness. A type parameter that stands as the extension of
> a record in a declaration's backing (`{ ..r }`, `{ f : T, ..r }`) is a record-row
> parameter. An application of the declaration must supply, for that parameter, one
> of: a record type, an alias whose backing is one of these, a row variable, or a
> nominal whose backing is a record (not recursive through the extension) that the
> applying module can inspect (`:=`, or `::` in its own module). Any other argument is
> a type error at the application: "`Str` cannot extend a record".

| Question | Answer |
|---|---|
| Is this a "Solver-Mutating Rewrite"? | No. It mutates no solved graph and restamps no plan. It is a typing rule: it changes which programs type-check, so it is declared with tests on both sides, as design.md requires for a typing rule |
| Where is it checked? | At the instantiation of a declaration's backing with its arguments, where the checker opens a nominal or alias. The record-row parameters of a declaration are a fact of the declaration's backing, computed once when the declaration is checked (the same place that appends hidden row variables, `finishAliasDeclarationParameters`, Rewrite Inventory `design.md:13020`) |
| Why allow a nominal? | Monotype already flattens an inspectable nominal extension (`solve.zig:7978-7989`, its own test `:12671`), and `y3run.roc` runs. The rule states what the compiler already does. Q1 asks rtfeldman to confirm that this is part of the language |
| A value of `Ref(Owner)` | Built from a record: `Ref.({ id: "a", name: "Ada" })`. `Ref.(Owner.({..}))` is a type error today ("The value I found has type: Owner. But the nominal type expects: { ..r }"), which the rule keeps: the backing is a record with `Owner`'s fields, not an `Owner` |

Walk change (Y3, section 3.6) depends on this rule: after it, the `.nominal` arm of
`collectRecordFields` meets only an inspectable record nominal.

Tests (each validated by reverting the change):

| Test | Pins |
|---|---|
| CLI: `Ref(Str)`, `Ref([A, B])`, `Ref(Dict(Str, Str))` in an annotation | type error at the application, with the new message; no panic. Rejected side |
| CLI: `Ref(Owner)` with `Owner := { id : Str, name : Str }`; `Ref({ id : Str })`; `Ref(Alias)`; a self link `Owner := { .., referred_by ?: Ref(Owner) }` | the program runs (output of `y3run.roc`). Accepted side |
| CLI: `Ref(Time)` where `Time ::` is opaque in another module | type error. In `Time`'s own module: accepted (Q2) |
| checker unit test in `src/check/test/` | the record-row parameter set of `Ref(r) := { ..r }` is `{r}`; of `P(a, r) := { x : a, ..r }` is `{r}` |

Risks: a package that writes `{ ..r }` at a non-record today compiles until Monotype
reaches the type. Such code is already broken; the new error only moves earlier.

### 3.2 Y9: A Site in an Unannotated Generic Function Is Sealed (P0)

Repro `y9.roc` (uses `Db.roc`):

```roc
import Db

Pet : { id : Str, name : Str, age : U8 }
Owner : { id : Str, name : Str, city : Str }

## Unannotated, with a direct call: the site is described once.
named_only = |q| Db.Q.filter(q, |x| x.name != "")

main! = |_args| {
	pets : Db.Q(Pet)
	pets = Db.from("pet")
	owners : Db.Q(Owner)
	owners = Db.from("owner")
	echo!("direct at Pet: ${pets.filter(|x| x.name != "").show()}\n")
	echo!("fragment at Pet: ${named_only(pets).show()}\n")
	echo!("fragment at Owner: ${named_only(owners).show()}\n")
	Ok({})
}
```

Output (no error):

```
direct at Pet: pet | filter [Record([{ name: "age", presence: Required, ty: U8 }, { name: "id", presence: Required, ty: Str }, { name: "name", presence: Required, ty: Str }])]
fragment at Pet: pet | filter [Record([{ name: "name", presence: Required, ty: Str }])]
fragment at Owner: owner | filter [Record([{ name: "name", presence: Required, ty: Str }])]
```

The `Code` value at the fragment has the type `Code(Pet -> Bool)` in the running
program, but its description says `{ name : Str } -> Bool`.

Root cause: the site in `named_only` is described once, at publication. The lambda's
row tail is a flex variable that `named_only`'s scheme quantifies. `collectRecordFields`
finds no binding for it and seals it to its row default `{}`
(`src/check/code_reifier.zig:7350-7353`). The seal rule (`design.md:23623-23630`) is
for a variable that nothing fixes. A variable that the enclosing template quantifies
is fixed: by each caller, and Monotype specializes it per caller.

Change in two steps:

| Step | Change |
|---|---|
| Stage 0 (interim) | The walk of a site refuses, instead of sealing, a variable that a template enclosing the site quantifies. Which template encloses a site is explicit data: the site records the definition that owns it (design.md, "Each site records the definition or top-level `expect` that owns it"), and the template's scheme variables are `schemeVars` (`src/check/code_reifier.zig`, used by `instantiationOf`). The refusal reads: "a `Code` site inside a generic function, whose types each caller fixes: describing it per caller needs instance descriptions (not yet)". A variable that no enclosing template quantifies (`r` in a top-level `\|r\| r.id > 0`) still seals |
| Stage 2 (D1) | The site is an instance site and is described per closing use (section 3.4). The interim refusal goes |

Tests: `y9.roc` refused at Stage 0 (revert the change: the wrong parameter type comes
back); a top-level inline site `|r| r.id > 0` with nothing fixing `r` still describes
as `{ id : Dec }`. At Stage 2, `y9.roc` prints the `Pet` and the `Owner` record.

Risks: a program that uses this today with field reads only gets a correct query
from a wrong description. It becomes an error at Stage 0 (Q3). No such site exists in
`examples/reifying/surreal` (checked: no lambda at a `Code` position inside a generic
library function).

### 3.3 Y2: Open-Row Helper Chains (P0)

#### 3.3.1 Annotated Chain: D2

Repro `y2a.roc`:

```roc
import Db

Owner : { id : Str, name : Str, city : Str }

in_oslo : { city : Str, ..r } -> Bool
in_oslo = |x| x.city == "Oslo"

## An annotated open-row helper that calls another one.
named_in_oslo : { city : Str, name : Str, ..r } -> Bool
named_in_oslo = |x| in_oslo(x) and x.name != ""

main! = |_args| {
	owners : Db.Q(Owner)
	owners = Db.from("owner")
	echo!("${owners.filter(named_in_oslo).show()}\n")
	Ok({})
}
```

Output:

```
── ✗ cannot reify a polymorphic function ────────────────────────── y2a.roc:6:11
This function is polymorphic here, and the place it is used does not narrow
every type variable to one type.
in_oslo = |x| x.city == "Oslo"
A description is built for one concrete type at a time. A type variable has no
shape to describe. Use this function where its types are already fixed, or
write a type annotation that fixes them.
What is left open (not fixed): an open record
```

Source: `rejectError(.unresolved_type, region, "an open record")` in
`collectRecordFields`, `src/check/code_reifier.zig:7354`; title and summary in
`src/check/report.zig:5907-5912`.

Matrix (all with `Db.roc`):

| Outer helper | Inner helper | Site | Result |
|---|---|---|---|
| annotated, open row | annotated, open row | named | refused at inner |
| annotated, open row | annotated, open row | `\|p\| outer(p)` | refused at inner |
| annotated, open row | unannotated | named | refused at inner |
| unannotated | annotated, open row | named | accepted |
| `\|p\| in_oslo(p.owner)` (no outer helper) | annotated | inline | accepted |
| annotated, `Bx(a) -> Bool` (non-row variable) | annotated, `Bx(a) -> Bool` | named | accepted |

Root cause, step by step:

| Step | What happens | Where |
|---|---|---|
| 1 | The site describes `named_in_oslo` at `Owner`. Its frame binds `r_outer` to the rest of `Owner` | `instantiationOf` `:7569`, `matchRecord` `:7855` |
| 2 | The call `in_oslo(x)` is matched: `in_oslo`'s row `r_in` is bound to the use record `{ city : Str, name : Str, ..r_outer }`, a `TypeRef` into the module reader, with the tail `r_outer` unresolved | `matchRecord` `:7852-7856` |
| 3 | `describeDefinition` enters `in_oslo`: the reader's `substitution` becomes `in_oslo`'s frame | `:1177` |
| 4 | Converting `x`'s type follows `r_in` to the use record, then its tail `r_outer`, through `reader.fixedType`, which reads the current frame (`in_oslo`'s). `r_outer` is not there | `collectRecordFields` `:7348-7354`, `fixedType` `:8077-8081` |
| 5 | `r_outer` is rigid (annotated), so it does not seal: "an open record" | `:7353-7354` |

A non-row variable does not fail because `matchType` resolves it at bind time
(`use.reader.resolvedType(fixed)`). A row variable is bound to a whole record whose
tail is read later, in another frame. An unannotated outer helper has a flex tail,
which step 5 seals to `{}`: the inner row is then described at a record narrower than
Monotype's instance, and `instantiationKey` (`:8038`) hashes the use record's root
key, which is the same for every outer instance. The same wrong-type defect as Y9.

D2. A type reference names its frame:

| Item | Change | Where |
|---|---|---|
| Frame store | The walk owns an arena of frames. A frame is an immutable substitution, made when `describeDefinition` or `enclosedLambda` enters an instance, and freed when the site's walk ends | `Walk`; `describeDefinition` `:1169-1186`; `enclosedLambda` (merge at `:1471-1486`) |
| `TypeRef` | `{ reader, id, frame }` | `:346-349` |
| `fixedType` | reads `ref.frame`, not `self.substitution` | `:8077-8081`; its callers `resolvedType` `:8071`, `collectRecordFields` `:7349` |
| `matchRecord` | binds the row to `use` with `use.frame` (the caller's frame), so the tail is read where it belongs | `:7855` |
| `instantiationKey` | hashes each binding through its frame: a structural digest that follows a bound variable to its binding, so two outer instances give two keys | `:8038` |
| `matchRecord` use switch | follow a use `.alias` to its backing instead of returning with no binding (`.alias => return` at `:7825-7836`); add a test that reaches it | `:7824-7836` |

No design.md rule changes: the walk already claims Monotype's types. design.md
"Code Reification" gets one sentence under the instance paragraph: "A type reference
carries the frame its variables belong to; a binding is read in that frame."

#### 3.3.2 Unannotated Chain at a Named Site: D3

Repro `y2u.roc`:

```roc
import Db

Owner : { id : Str, name : Str, city : Str }

## Two unannotated helpers: `same` has a `where` requirement (`a.is_eq`).
same = |a, b| a == b
city_is_oslo = |x| same(x.city, "Oslo")

main! = |_args| {
	owners : Db.Q(Owner)
	owners = Db.from("owner")
	echo!("inline: ${owners.filter(|o| city_is_oslo(o)).show()}\n")
	echo!("named: ${owners.filter(city_is_oslo).show()}\n")
	Ok({})
}
```

Output:

```
── ✗ cannot reach this definition ───────────────────────────────── y2u.roc:6:15
This name should lead to a function body the compiler can read, and it does not.
same = |a, b| a == b
Reifying reads the function's body. Name a function defined at the top level of
this module or of one it imports.
The compiler could not follow: a method this call names no target for
inline: owner | filter [Record([{ name: "city", ..}, { name: "id", ..}, { name: "name", ..}])]   (abbreviated)
```

Source: the `.none` arm of `dispatchWithArgs`, `src/check/code_reifier.zig:6052`
(the region is the `==`). `calleeEvidence` (`:5115`) has the same text; a debug trace
must confirm which arm fires. Title: `src/check/report.zig:5925-5930`. The detail is
not row-specific: a `where` requirement forwarded through two unannotated helpers.

Root cause: the inline site calls `city_is_oslo`, and that call recorded evidence for
its `where` requirements, which `supply` (`:6377`) reads. A named site has no call.
`reifyNamedSite` (`:9954`) fixes the root's types from the site's `f` (`fixed`) but
supplies no evidence. When the root forwards its requirement to `same` (a
`constraint` entry), nothing answers it. One helper alone works because its `==`
dispatches on a type that `fixed` made concrete.

D3. The site's lookup of the name is a use of a generic definition, and the checker
records evidence on it as on any use (`siteEvidence`). `reifyNamedSite` reads that
evidence and passes it to `reifyLambda` as the root's `SuppliedEvidence`, the same
way `calledRow` passes a call's evidence. If the checker does not record evidence on
a lookup that a `Code` position consumes, the publication records it there; that is
recorded data, not a new plan. The implementer checks this first.

#### 3.3.3 Tests for D2 and D3

In `src/compile/test/code_reifier_test.zig` unless stated. Validate each by reverting
the change.

| Test | Pins |
|---|---|
| "Y2: an annotated open-row helper that calls another describes at the site's row" | `y2a.roc`; the inner row's parameter type is the full `Owner` record |
| "Y2: two calls of one annotated open-row helper at two rows build two rows" | `\|v\| named(v.a) and named(v.b)`, `a` and `b` of different record types; two rows, two parameter types (needs a non-inlined view, or a recursive inner helper so the row stays) |
| "Y2: an unannotated outer helper over an annotated open-row helper keeps the full row" | the parameter type is the site's record, not `{ city : Str }` (the silent case) |
| "Y2: a nested record field of a row-bound use is read in the caller's frame" | outer `{ owner : { city : c, ..o }, ..r }` passes `x.owner` to an inner open-row helper; `c` resolves |
| "Y2: an open tag row in an annotated chain" | `[A, B, ..t]` helpers; accepted, variants as named |
| "Y2: a named site whose root forwards a where requirement to another helper" | `y2u.roc`; equals the inline form's dump |
| CLI `test/cli/StagedOpenRowHelpers.roc` (Monotype and `--specialize=no`) | the matrix of 3.3.1 and `y2u.roc`, every line accepted |
| reify fuzzer (`src/compile/reify_fuzz.zig`) | generate generic helpers over open records and compose them at random rows (AGENTS.md: small typed constructs, composed randomly) |

Risks: `instantiationKey` changes for every generic callee, so row sharing changes; a
key that is too fine only duplicates rows (normalization merges equal rows). Bump
`CACHE_VERSION` because inline digests can change. Opaque proposal 1.10 notes that a
non-row variable "only the rest of the callable fixes" is refused and that no source
reached it, because "an annotated generic helper that forwards such a requirement ...
is reported 'Cannot Reify A Polymorphic Function' ... first". After D2 that refusal
can become reachable: add the `a.mix` probe of that note as a test.

### 3.4 Y1 and D1: Instance Descriptions (P1)

Repro `y1.roc`:

```roc
import Db

Pet : { id : Str, name : Str, age : U8 }
Owner : { id : Str, name : Str, city : Str }

## A query fragment over any row with a `name`.
named_only : Db.Q({ name : Str, ..r }) -> Db.Q({ name : Str, ..r })
named_only = |q| q.filter(|x| x.name != "")

main! = |_args| {
	pets : Db.Q(Pet)
	pets = Db.from("pet")
	owners : Db.Q(Owner)
	owners = Db.from("owner")
	echo!("${named_only(pets).show()}\n${named_only(owners).show()}\n")
	Ok({})
}
```

Output:

```
── ✗ cannot reify a polymorphic function ─────────────────────────── y1.roc:8:27
This function is polymorphic here, and the place it is used does not narrow
every type variable to one type.
named_only = |q| q.filter(|x| x.name != "")
...
What is left open (not fixed): an open record
```

Source: `collectRecordFields`, `src/check/code_reifier.zig:7354`.

Root cause: the site is described once, at publication of the module that holds it
(section 2.2), with the template's own types. `r` is rigid and nothing in that
module's walk fixes it. Monotype specializes `named_only` at `Pet` and at `Owner`, and
at each specialization the `Code` value is a different type, but only one description
slot exists (`CheckedCodeSite.node`).

#### 3.4.1 D1: The Mechanism

The design follows `where` evidence, which already reaches a generic function from
its callers, through Monotype's evidence chain and Boxy's dictionaries.

| Term | Definition (all explicit data) |
|---|---|
| Instance site | A site (kind `.named_function`, `.inline_lambda` or `.template_call`) whose site function type `f` mentions a variable of `schemeVars(T)`, where `T` is the template that holds the site (the site's recorded owner, or the nearest enclosing generalized lambda) |
| Instance constant | An instance site, or a `Code.type_id` / `Code.ty_of` call (D6) whose proxy type mentions a variable of `schemeVars(T)` |
| Inventory of `T` | The ordered list of `T`'s instance constants, plus one forward entry per use in `T` of a template `U` with a non-empty inventory whose recorded substitution mentions a variable of `schemeVars(T)` |
| Closing use | A use (call or value lookup) of a template `U` with a non-empty inventory whose recorded substitution mentions no variable that an enclosing template quantifies |
| Instance table | For one closing use: one entry per inventory entry of `U`, in inventory order. A constant entry is a `ConstNodeId` in the module of the closing use. A forward entry is a nested table |

| Stage | Change | Where |
|---|---|---|
| Publication of `T`'s module | Compute each template's inventory. Give each instance site `CheckedCodeSite.instance = k` (its index in the inventory) and no `node`. Store the inventory on `CheckedProcedureTemplate`, next to its evidence params | `reifyModuleSites` `src/check/code_reifier.zig:9805` (skip instance sites, as it skips `.template`); `src/check/checked_artifact.zig` (`CheckedCodeSite` `:2551`, template table) |
| Publication of the closing use's module | For each closing use, walk each inventory entry of `U` at the use's substitution: a site's lambda through the existing `instantiationOf` and `describeDefinition` path, with the use's recorded evidence supplied (D7 machinery of the opaque proposal, `supply`); a forward entry recursively, composing the substitution through D2 frames. Store the table on the use (`CheckedCodeInstances`). Within one module, equal `(U, instantiationKey)` share nodes | new `reifyInstanceUses` beside `reifyModuleSites`; `Walk` cache |
| Monotype | A specialization of `U` from a closing use carries the use's table in its context. A forwarding use inside `U` passes the nested table on. `.code_from_lambda` of an instance site restores the node of entry `k` of the table in force, not `CheckedCodeSite.node` | `.code_from_lambda`, `restoreCodeSiteAtNode` `src/postcheck/monotype/lower.zig:47593`; the evidence-chain context of design.md "Static Dispatch In Monotype" (`design.md:16331`) |
| Boxy | `U`'s worker takes the table as a hidden argument, one group, as it takes a dictionary group. The closing use passes a static constant; a forwarding use passes the caller's nested table | `pushCodeConversion` `src/postcheck/boxy/plan.zig`; design.md "Boxy Dictionaries And Vtables" (`design.md:13924`) |
| Refusal | An instance refusal is a `staged_code` problem of the closing use's module. Its region is in `U`'s module, so it is reported with `StagedCode.foreign` (another module) or D9 (same module), naming the closing use | `rejectError`; `src/check/report.zig` |
| Debug invariant | Lowering asserts that an instance site has a table entry in force, and that two closing uses that Monotype gives one specialization key have equal description digests | `lower.zig`, Boxy plan |

What does not change:

| Item | Why |
|---|---|
| Type checking | The checker types the program as today. No constraint, no redirect, no restamped plan. "Solver-Mutating Rewrites" (`design.md:9622`) does not apply: publication records data, lowering reads it |
| A site whose `f` mentions no enclosing variable | Described once, as today |
| Normal form rules | Unchanged. A description is still built for one concrete type |
| A template (`Code`-returning function) and its call | Unchanged; a template call inside a generic function whose types mention the enclosing variables is an instance site (Q4) |

design.md changes ("Code Reification"):

| Text | Change |
|---|---|
| Stage table, Description (`:23602`) | "Walks each site's checked bodies ... once per site, or, for an instance site, once per closing use, in the module of the use" |
| Stage table, Lowering (`:23603`) | "Restores the stored node, or the node the instance table in force names" |
| Seal invariant (`:23612-23630`) | "A variable that an enclosing template quantifies is never sealed: the site is an instance site" |
| New invariant | the definitions of the table above, and the frame rule of D2 |
| "Static Dispatch In Monotype", "Boxy Dictionaries And Vtables" | one paragraph each: an instance table travels as evidence does |

Developer diagnostic: `ROC_REIFY_INSTANCES`, a member of `base.dev_diagnostics.Var`
(design.md "Developer Diagnostics", `:25689`), prints each closing use with its table.
Debug and `-Ddev-diagnostics` builds only.

#### 3.4.2 Rejected Alternatives

| Alternative | Reason |
|---|---|
| Describe once with an open row in `Code.Ty` (`Record(fields, Open)`) | Changes the normal form: a derived `==`, a record update, `select(\|x\| x)` and scalarization (N14) have no meaning over an unknown row. It breaks "a description is a specialization read without lowering" |
| Describe in Monotype, per specialization | Moves the walk into lowering, against the stage table ("Lowering ... walks no function"). The walk reads checked bodies and plans, which lowering does not keep |
| Seal the row as Y9 does | Wrong types, silently (section 3.2) |
| Require the user to write a template (`Code`-returning function) | A fragment takes a query, not constants, so it is no template |

#### 3.4.3 Tests

| Test | Pins |
|---|---|
| `y1.roc` as CLI test `test/cli/StagedFragment.roc`, Monotype and `--specialize=no` | two lines: the `Pet` record and the `Owner` record. Revert D1: the refusal comes back |
| a fragment that calls a fragment (`card(named_only(q))`) | forward entries and nested tables; needs D2 |
| a fragment in a package, called from the app | the description is in the app's module; refusal in the package's body names the app's closing use |
| two closing uses at one type | one node (cache); Monotype one specialization |
| a generic fragment never closed | no description, no report; program compiles |
| a site whose `f` mentions no enclosing variable, inside a generic function | described once (unchanged) |
| `y9.roc` | the `Pet` and `Owner` records (Y9 final) |
| `Code.Bound` site inside a generic function | refused by name (Q3) |
| reify fuzzer | random generic wrappers around random sites, closed at random types; the description equals the one of the same lambda written at the closed type |

Risks:

| Risk | Answer |
|---|---|
| Cost: one walk per closing use | Keyed and cached per module. A fragment is called at a few row types |
| Cross-module node references in tables | A table entry names `(module, ConstNodeId)`; a site's node is already restored from the module that holds it |
| Boxy ABI change for site-generic workers | Same discipline as dictionaries: inventory order is the slot order |
| `roc check` of a package reports nothing for an instance site that no use closes | As for a template. Package tests close their fragments (Q6) |
| Cache | New artifact data: bump `CACHE_VERSION` (`src/compile/cache_config.zig:452`) |

### 3.5 Y1b: Unannotated Fragment in Method Form (not proposed)

`named_only = |q| q.filter(|x| x.name != "")` with no annotation is a type error today:
"The method filter has the type: `Db.Q(Pet), Code(Pet -> Bool) -> Db.Q(Pet)`. But I need
it to have the type: `Db.Q(Pet), ({ name: a, .. } -> Bool) -> _ret`". The call on an
unresolved `q` is a `where` requirement, and a `Code` position is read off the
annotation of the method a dispatch plan names (`design.md:23669-23690`). Making a
requirement's argument a `Code` position is a typing-rule change (Q10). With D1, the
annotated fragment is the supported form, and the direct-call form (`Db.Q.filter(q, ..)`)
works unannotated.

A `Code` in a declared `where` requirement is refused today too
(`where [q.filter : q, Code(a -> Bool) -> q]`): a `Code` position is read off the
annotation of a function, never off a requirement. Q10 is answered "no" (Stage 0).
The type mismatch report adds a hint where one side is a function and the other a
`Code` of a function: annotate the receiver's type, or call the method by its type
(`Q.filter(q, ..)`). The hint is reporting only, and no typing rule changes.

### 3.6 Y3: A Record Extended by a Nominal Record (P1)

Repro `y3.roc`:

```roc
import Db

## A read view of a linked row: field access goes through the nominal.
Ref(r) := { ..r }

## A nominal row. A self link needs one: an alias cannot be recursive.
Owner := { id : Str, name : Str, referred_by ?: Ref(Owner) }
Pet : { id : Str, owner : Ref(Owner) }

main! = |_args| {
	pets : Db.Q(Pet)
	pets = Db.from("pet")
	echo!("${pets.filter(|p| p.owner.name != "").show()}\n")
	Ok({})
}
```

Output:

```
── ✗ cannot reify this type ─────────────────────────────────────── y3.roc:13:23
...
There is no description for: a record extended by a type that is not a record
```

`y3run.roc` (the same types, no reification) runs and prints `Bob Ada`.

Source: `collectRecordFields`, `src/check/code_reifier.zig:7363-7369` (the `.nominal`
arm with `.tuple`, `.function`, `.tag_union`, `.empty_tag_union`). Report:
`src/check/report.zig:5901-5906`.

Root cause: the walk's record conversion stops at a nominal in the extension chain.
Monotype follows it (`flattenRecordRow`, `src/postcheck/monotype/solve.zig:7978-7989`).
The walk must read types by Monotype's rules (`design.md:23612`), so this is a gap
in the walk.

Change (after D4):

| Case in the extension chain | Walk |
|---|---|
| nominal with an inspectable record backing | continue the chain in the backing, instantiated at the nominal's arguments (as `nominalTy`, `:7037`, reads a `Named` backing through `nominal_args`). The nominal's name is not kept, as in Monotype: `Ref(Owner)` is `Named("Ref", Record([id, name, referred_by]))` |
| the backing reaches the same nominal instance again (a self link) | the existing nominal recursion rule gives `Recursive("Ref")` at the inner `Ref(Owner)` |
| opaque nominal (`::`) | refused with a new reason: "a record extended by an opaque type, whose fields it hides". Reachable only if Q2 allows the type in the declaring module |
| tuple, function, tag union, empty tag union, a nominal with another backing | compiler invariant after D4: debug assertion, `unreachable` in release (AGENTS.md) |

Tests (each validated by reverting):

| Test | Pins |
|---|---|
| "Y3: a field read through a record extended by a nominal record" | `y3.roc`: `p.owner.name` is `Field(Unwrap(Field(p0, owner)), name)`, the parameter type has `owner : Named("Ref", Record([id, name, referred_by: Optional]))` |
| "Y3: a self link through a nominal extension is Recursive" | `referred_by`'s type is `Named("Ref", ..)` whose inner occurrence is `Recursive("Ref")` |
| "Y3: an alias extension is unchanged" | the control (`Owner` as an alias) gives the same dump as before |
| CLI `test/cli/StagedNominalExtension.roc` (Monotype and Boxy) | the three lines above end to end |

Risks: none beyond D4. Normal form rules do not change. The descriptions of programs
that were refused before are new; bump `normal_form_version` only if Q11 of the
version policy counts newly accepted types (today it does not).

### 3.7 Y5 and D5: Field Defaults in `Code.Ty` (P2)

Repro `y5.roc`:

```roc
## The type a translator sees for a nominal row with defaults.
Med := { id : Str, stock : I32 ?? 0, tags : List(Str) ?? [], note ?: Str }

ty : Code(Med -> Med) -> Str
ty = |code| Str.inspect(code.graph().root_row().result)

main! = |_args| {
	echo!("${ty(|m| m)}\n")
	Ok({})
}
```

Output:

```
Named("Med", Record([{ name: "id", presence: Required, ty: Str }, { name: "note", presence: Optional, ty: Str }, { name: "stock", presence: Required, ty: I32 }, { name: "tags", presence: Required, ty: ListOf(Str) }]))
```

Source: `recordTy`, `src/check/code_reifier.zig:7306` (`.defaulted` is not optional,
and the default is dropped). The API says so: "A field with a default is `Required`"
(`src/build/roc/Builtin.roc:23651-23656`).

Facts:

| Fact | Evidence |
|---|---|
| A default is a closed expression | `M := { a : I64, b : I64 ?? a + 1 }` is "Nothing is named a in this scope". It can read top-level names |
| The checker keeps its identity | `CheckedFieldKind.default`: origin module and expression node (`src/check/checked_artifact.zig:2609-2616`) |
| Only a nominal record has defaults | `docs/langref/records.md:340` |

D5:

```roc
Ty := [
	# ... unchanged
	Record(List({ name : Str, ty : Ty, presence : [Required, Optional, Default(Value), DefaultComputed] })),
	# ...
]
```

| Default | Presence | Rule |
|---|---|---|
| a constant form (literal, aggregate of constant forms, tag, nominal of a constant form, a name that holds one) | `Default(v)`, `v` the `Code.Value` of the literal | the walk's existing `isConstantForm` (`src/check/code_reifier.zig:965`), read over the default's checked expression in its module; the walk describes the literal and converts it to a `Code.Value` |
| anything else (`?? Surreal.Time.now()`, a call) | `DefaultComputed` | explicit: "this field has a default whose value the type does not carry". A translator refuses it or asks for `default_by` |

| Item | Change | Where |
|---|---|---|
| API | presence variants; doc text "A field with a default is `Required`" changes | `src/build/roc/Builtin.roc:23651-23656` |
| Interning | the presence and the default value are part of the `Ty` key | `src/reify/types.zig` (record interning), `src/reify/digest.zig` |
| Walk | `recordTy` reads `field.field.kind.default` and the default's checked body through the foreign lookup of its origin module | `recordTy` `:7298-7316` |
| Emit | presence record | `src/check/code_emit.zig` (the `Record` arm of the type emitter) |
| Versions | `normal_form_version` (API shape, as opaque 1.4 did), `CACHE_VERSION` | `src/reify/mod.zig:40`, `src/compile/cache_config.zig:452` |
| Translators | every `[Required, Optional]` match | `examples/reifying/surreal/Types.roc`, `examples/reifying/sql/Sql.roc`, `examples/reifying/dbsp/Dbsp.roc`, `examples/reifying/glsl/Glsl.roc` (grep `presence`) |

Tests: `y5.roc` prints `Default(Int(0))` for `stock` and `Default(List([]))` for `tags`;
a nominal default `?? Active` is `Default(Wrap(Tag("Active", [])))`; `?? make()` is
`DefaultComputed`; two nominals that differ only in a default are two `Ty` values; a
record value that omits a defaulted field still describes as before (the record
literal fills it).

Rejected: a default as a row of the graph (`Default(U32)`). A `Ty` is data that also
exists outside a graph (D6), so a row index has no graph to point into.

### 3.8 Y6 and D6: A Type Description Without a Lambda (P2)

Today the only way to get a `Code.Ty` is a lambda at a `Code` position:
`Surreal.table("owner", |o| o)`. `Code` has `graph`, `version`, `bound`, `refuse_at`,
`proxy`, `prim`, `type_id` (`src/build/roc/Builtin.roc:24314-24327`, `:24515-24546`),
and `type_id` gives an identity, not a description.

D6:

```roc
## The description of `t`. `t` must be fixed at the call.
ty_of : Proxy(t) -> Ty
```

| Item | Change |
|---|---|
| Intrinsic | `code_ty_of`, as `code_type_id` (`src/canonicalize/BuiltinLowLevel.zig`), recorded in `NodeStore.code_identity_uses` |
| Publication | `moduleIdentities` (`src/check/code_reifier.zig`) converts the fixed type with the walk's `tyOf` and stores the `Code.Ty` value as the call's `code_from_lambda` constant node |
| Error | a proxy type that is not closed (a variable, an open row that no default seals): `ty_of_not_closed`, as `type_id_not_nominal` |
| Generic use | inside a generic function whose scheme the proxy type mentions, the call is an instance constant (D1), so `Surreal.table : Str -> Table(row)` can compute `ty_of(proxy : Proxy(row))` per closing use |

Tests: `ty_of` of `Owner`, of a record, of `List(Owner)` equals the `result` of
`|x| x` at that type; `ty_of` of an open proxy is the error; after D1, `table("owner")`
inside a generic body gives the row's description at each closing use.

### 3.9 Y4 and D7: A `Code`-Derived Constant in a Clause (P2)

Repro `y4.roc` with this module `T.roc`:

```roc
## A table handle that keeps its row type, read from an identity lambda.
T :: {}.{
	Table(row) := { name : Str, row_ty : Code.Ty }.{
		key : Table(row), Str -> Str
		key = |Table.(t), k| "${t.name}:${k}"
	}

	table : Str, Code(row -> row) -> Table(row)
	table = |name, code| Table.({ name: name, row_ty: code.graph().root_row().result })

	## A handle with no `Code` in it, for the control.
	Plain(row) := { name : Str }.{
		key : Plain(row), Str -> Str
		key = |Plain.(t), k| "${t.name}:${k}"
	}

	plain : Str -> Plain(row)
	plain = |name| Plain.({ name: name })
}
```

```roc
import Db
import T

Visit : { id : Str, vet : Str }
Vet : { id : Str, name : Str }

vets : T.Table(Vet)
vets = T.table("vet", |v| v)

plain_vets : T.Plain(Vet)
plain_vets = T.plain("vet")

main! = |_args| {
	visits : Db.Q(Visit)
	visits = Db.from("visit")
	echo!("plain: ${visits.filter(|v| v.vet == plain_vets.key("ruth")).show()}\n")
	echo!("table: ${visits.filter(|v| v.vet == vets.key("ruth")).show()}\n")
	Ok({})
}
```

Output:

```
── ✗ cannot reify this type ──────────────────────────────────────── y4.roc:8:23
...
vets = T.table("vet", |v| v)
...
There is no description for: a reified value that is not a function
plain: visit | filter [Record([{ name: "id", .. }, { name: "vet", .. }])]
```

The report points at line 8, the table's own lambda, which is a correct site. It does
not name line 17, the clause that failed.

`y4id.roc` (a clause that reads `owner_tid = Code.type_id(owner_proxy)`) gives
"cannot reify this expression", "There is no description for: this expression", at
the constant.

Source: the walk folds `vets` (`foldedConstant`, `src/check/code_reifier.zig:2994`),
walks `T.table`'s body with its arguments, and asks for the row of the argument
`|v| v`, whose checked type is `Code(Vet -> Vet)`. `functionOf` is null, so `lambdaRow`
refuses it (`:1235-1237`; the same text is at `:1301` and `:1586`; a trace must
confirm the arm). For `y4id.roc`: `exprRef`'s `.code_from_lambda` arm, `:2112-2117`.

Decision D7: no description form for a `Code` value (a description of a description)
or an identity value inside a description. Reasons:

| Reason | Detail |
|---|---|
| The library change is better API | A handle that holds only its name (`Rows(row) :: { name : Str }`, analysis P6, verified on the server) folds to a literal in a clause. With D6 and D1 the row type comes from `ty_of` where the schema needs it, so `Table` holds no `Code`-derived value at all |
| A form would only exist to be dropped | `vets.key("ruth")` reads only `name`. A `Code` constant node would be eliminated by normalization in every working case and would make acceptance depend on normalization power |
| `TypeId` and `PrimId` are opaque | A literal of them has no node form; a translator compares ids at translation time, not inside a clause |

What does change (Stage 0, small):

| Item | Change | Where |
|---|---|---|
| Message | a lambda at a `Code` position or a `code_from_lambda` met inside a walked body is refused with one new reason: "a value computed from a `Code` description (`vets`), which a description cannot hold. Keep `Code` values and their results out of values a clause reads, or build the value without one" | `lambdaRow` `:1235-1237`, `curriedLambdaRow` `:1300-1301`, `inlineBody` `:1585-1586`, `exprRef` `:2112-2117` |
| Place | reported at the clause, with the constant's definition as the reached region (D9) | `rejectError`; `src/check/report.zig` |

Tests: `y4.roc` reports at the clause (line 17) and names `vets`; `y4id.roc` the same;
the `plain` control describes. Revert: the report points at line 8 again.

### 3.10 Y8: A Captured Record With an Optional Field (P2)

Status: the `Id` case is done by option A (see "Y8 Option A" in section 6). The
general case (`Value.Absent`) is done (D8 below).

Repro `y8.roc`:

```roc
## A typed key: a phantom `List(row)` ties the key to its row type. No value
## of `row` is stored in it.
Id(row) := { key : Str, phantom : List(row) }

Customer : { id : Str, zip ?: Str }
Plain : { id : Str, zip : Str }

Stage := {}.{
	render : Code(Str -> Id(r)) -> Code.Bound(Str)
	render = |code| Code.bound(code, "slots ${code.graph().slots().len().to_str()}")
}

of_plain : Id(Plain) -> Str
of_plain = |who| Stage.render(|_k| who).value()

of_customer : Id(Customer) -> Str
of_customer = |who| Stage.render(|_k| who).value()

main! = |args| {
	n = args.len().to_str()
	echo!("${of_plain(Id.({ key: n, phantom: [] }))}\n")
	echo!("${of_customer(Id.({ key: n, phantom: [] }))}\n")
	Ok({})
}
```

Output:

```
── ✗ cannot bind this captured value ────────────────────────────── y8.roc:17:34
This function reads a value that exists only when the program runs, and the
site cannot give it to the translator's result as an input slot.
of_customer = |who| Stage.render(|_k| who).value()
...
The site cannot bind: a captured record with an optional field
slots 1
```

A capture read as `who.key` (a `Str`) binds; only a slot whose type holds an optional
field fails. In the Surreal library `o.customer.id() == who` captures the whole `Id`.

Source: `slotShape`, `src/check/code_reifier.zig:8690`, refusal at `:8743`. Cause: a
slot value is a `Code.Value` (`src/build/roc/Builtin.roc:24480-24495`), whose
`Record(List(Value))` is positional, and `CodeValueShape`
(`src/check/checked_artifact.zig:2532`) has no form for a field that may be absent.

D8 (both paths done):

| Path | Effect | Cost |
|---|---|---|
| Opaque proposal D5 (`Code.Binds`, `Value.Encoded`): the library makes `Id(row) ::` opaque with an `encoder_for` that writes the table and the key | The capture binds as encoded bytes; the phantom row never reaches a slot shape. Fixes the README case | Library only, after opaque Stage 2 |
| `Value.Absent` for an optional field that is absent, shape `opt_field` in `CodeValueShape`, Monotype and Boxy slot builders switch on the field's `OptField` | Any structural optional capture binds | Done: `Absent` in `Builtin.roc` `Value`; `opt_field` in `CodeValueShape` (`src/check/checked_artifact.zig`), written by `slotShape` (`src/check/code_reifier.zig`); Monotype `optionalFieldCodeValue` from `codeValueBody` (`src/postcheck/monotype/lower.zig`), which reads the field's `value_ty`; Boxy `lowerOptionalFieldCodeValueInto` from `lowerCodeValueLayerInto` (`src/postcheck/boxy/lower.zig`), which reads the child's `record_field_kind`; both shape checks. `CACHE_VERSION` 212, `normal_form_version` unchanged (36: no rule, builtin table or op changes). Tests: `test/cli/StagedOptionalCapture.roc` (both lowerings), `sql/main.roc` `insert_customer`, `surreal/TranslateTest.roc` `at_places`, `surreal/main.roc` `owners_at` |

Decision: take the first path first, and the second when a translator needs a
structural optional capture (Q9). Both are done: the SQL example inserts a
captured customer whose `email` may be absent, and the Surreal example filters
by captured addresses whose `zip` may be absent. A field default does not use
`Absent`: a default record that leaves out an optional field stays
`DefaultComputed` (an open choice, Q18).

### 3.11 Y7: roc-lang/roc#12705, Free Locals in `lift` (P1, referenced)

Repro (`scratchpad/repro-freelocals/main.roc`, `roc test --no-cache main.roc`):

```roc
G := {}.{
	f : G, a -> (Str -> Str)
	f = |_g, x| {
		h = |p| {
			_ = x
			p
		}
		|p| h(p)
	}
}

expect G.({}).f(1.U8)("x") == "x"
expect G.({}).f("s")("x") == "x"
```

Output: "Roc hit an internal compiler error", phase `post-check lift`, panic
"postcheck invariant violated: top-level Monotype definition has free locals after
checked closure collection" at `src/postcheck/monotype_lifted/lift.zig:561`
(`lowerTopLevelDef`). Re-verified on the baseline. The issue is open.

| Item | Answer |
|---|---|
| In reify code? | No. The repro has no `Code`. A control with `--specialize=no` does not crash; `--opt=interpreter` does |
| Trigger | a generic method called at two types, a local closure that reads a method parameter, and an inline lambda that calls that closure |
| Effect on the DSL | `Surreal.aggregated` had this shape. The library uses a top-level `Surreal.group_columns` instead (README of the repro, note 1) |
| Priority | P1: a crash; the library rule avoids it |
| Owner | Monotype lifted IR (`lift.zig`). Not part of this proposal's stages |

After the fix, `Grouped.aggregate` can keep its column helper as a local closure again.

### 3.12 Y11 and D9: Name the Site That Reached a Refusal (P2)

Evidence: `y2a.roc` reports only `in_oslo` (line 6), `y4.roc` only the table's lambda
(line 8). Neither names the `filter` call. Opaque proposal 0.3 (F4) already reports a
refusal in another module's file and names the site (`StagedCode.foreign`).

D9: when the refused region is outside the site's own lambda (a walked helper, a
folded constant, an instance site's body), the report adds the site that reached it,
in the same module too: "reached from the `Code` site at y2a.roc:15:24". Data: the
walk records the site's region at `beginSite`; `Rejection` already carries its module
(`Rejection.module`). No offset is read to find it.

Tests: `y2a.roc`, `y4.roc` reports name the clause; a refusal inside the site's own
lambda is unchanged.

## 4. What the SurrealDB API Gains

File references are to `examples/reifying/surreal` in the working tree.

### 4.1 Reusable Query Fragments (Y1, with Y2)

Before: a filter, an order or a projection is repeated in each query, or written as a
predicate helper and passed one level deep.

```roc
q1 = Surreal.from(patients).filter_by(|params, p| p.owner.get().address.city == params.city).select(pet_line)
q2 = Surreal.from(visits).filter_by(|params, v| v.patient.get().owner.get().address.city == params.city).select(visit_line)
```

After: a fragment over any row that has the fields it reads, at the query level.

```roc
## Rows whose owner lives in the parameter's city.
owned_in : Surreal.Query({ city : Str, ..p }, { owner : Surreal.Link({ address : { city : Str, ..a }, ..o }), ..r })
	-> Surreal.Query({ city : Str, ..p }, { owner : Surreal.Link({ address : { city : Str, ..a }, ..o }), ..r })
owned_in = |q| q.filter_by(|params, x| x.owner.get().address.city == params.city)

## Newest first, by any row with an `at`.
newest : Surreal.Query(p, { at : Surreal.Datetime, ..r }) -> Surreal.Selected(p, { at : Surreal.Datetime, ..r })
newest = |q| q.select_row().order_by(|r| r.at, Desc)

q1 = owned_in(Surreal.from(patients)).select(pet_line)
```

### 4.2 Helper Libraries Over Open Rows (Y2)

Before: an annotated helper may not call another annotated helper (`y2a.roc`); the
README advice is to inline or drop annotations, which then hits Y9.

After:

```roc
in_city : { city : Str, ..r }, Str -> Bool
in_city = |x, city| x.city == city

lives_in_oslo : { owner : Surreal.Link({ address : { city : Str, ..a }, ..o }), ..r } -> Bool
lives_in_oslo = |p| in_city(p.owner.get().address, "Oslo")

oslo_patients = Surreal.from(patients).filter(lives_in_oslo)
```

### 4.3 `Ref` Read Views for Nominal and Self-Linked Rows (Y3, with Y10)

Before (`main.roc:23`): `Owner` is nominal (it has a self link), so it keeps `Link`
and `.get()`:

```roc
Owner := { id : Str, name : Str, email : Str, phone ?: Str, address : Address, tags : List(Str), referred_by ?: Surreal.Link(Owner) }

referral = |o| match o.?referred_by {
	Ok(r) => r.get().name
	Err(_) => "-"
}
pet_line = |p| { id: p.id, kind: species_label(p.species), owner: p.owner.get().name }
```

After (read view next to the stored row, analysis P5):

```roc
## Read view: links are `Ref`, so a field read is a traversal.
Owner := { id : Str, name : Str, email : Str, phone ?: Str, address : Address, tags : List(Str), referred_by ?: Surreal.Ref(Owner) }

referral = |o| match o.?referred_by {
	Ok(r) => r.name
	Err(_) => "-"
}
pet_line = |p| { id: p.id, kind: species_label(p.species), owner: p.owner.name }
```

Library note: in the description, `Ref(Owner)` is `Named("Surreal.Ref", Record(..))`
with `Owner`'s fields and no `Owner` name. `Types.roc` finds the target table by
comparing that record with each table's row backing, not with its `Named` wrapper.

### 4.4 Schema Defaults From `??` (Y5)

Before (`main.roc:354`, `:373`, `:383`): each default is a schema call apart from
the type.

```roc
Medication : { id : Str, name : Str, form : Str, label : Str, unit_price : Dec, stock : I32 }
medications.define().default(|m| m.stock, 0).done()
```

After: the default is in the type, so the Roc value and the database agree by
construction.

```roc
Medication := { id : Str, name : Str, form : Str, label : Str, unit_price : Dec, stock : I32 ?? 0 }
medications.define().done()   # expected form: DEFINE FIELD stock ON medication TYPE int DEFAULT 0
```

`DefaultComputed` (`?? Surreal.Time.now()`) is refused by `Types.roc` with
"use `default_by`".

### 4.5 Type Descriptions Without Lambdas (Y6, with D1)

Before (`main.roc:82-101`):

```roc
owners : Surreal.Table(Owner)
owners = Surreal.table("owner", |o| o)
```

After:

```roc
owners : Surreal.Table(Owner)
owners = Surreal.table("owner")
```

`Surreal.table : Str -> Table(row)` calls `Code.ty_of(proxy)` where the schema needs
the row type; D1 makes that an instance constant per table.

### 4.6 Table Handles in Clauses (Y4, library change with D6)

Before (`main.roc:107`; README finding 2): the table name is repeated as text, and a
correlated subquery cannot name a table.

```roc
ruth_id = Surreal.id_of("vet", "ruth")
```

After: `Table` holds only its name and kind, so a clause folds it.

```roc
ruth_id = vets.id("ruth")
counts = Surreal.from(patients).select(|p| { n: p.name, visits: visits.rows().keep_if(|v| v.patient.get().id == p.id).len().to_i64_wrap() })
# expected form (analysis p5.roc, verified on the server for `pet`):
# SELECT name AS n, (SELECT * FROM visit).filter(|$v1| record::id($v1.patient) = record::id(id)).len() AS visits FROM patient
```

If a handle still holds a `Code` value, D7 reports it at the clause with the fix.

### 4.7 Captured Ids of Rows With Optional Fields (Y8, done by option A)

Done by option A instead of the path below: `Id` is `:=` with no phantom, and the
translator reads the row from the `Named` arguments. See "Y8 Option A".

Before (README finding 1): `select_where` examples use a captured `Dec`, because a
captured `Id(Customer)` with `zip ?: Str` is refused.

After (`Id` opaque with `encoder_for`, a `Code.Binds` site):

```roc
of_customer = |who| Surreal.bind_captured(Surreal.select_where(orders, |o| o.customer.id() == who))
# expected form, not verified: LET $_1 = customer:⟨c1⟩; SELECT .. FROM order WHERE customer = $_1
```

### 4.8 Correct Descriptions in Unannotated Fragments (Y9)

Before: an unannotated fragment that uses the direct-call form describes its rows as
`{ name : Str }`. A typed projection (`select_row`) inside it would list one column.
After Stage 0 it is an error; after D1 it lists the caller's columns.

## 5. Interaction With the Opaque Proposal

| This proposal | Opaque proposal | Interaction |
|---|---|---|
| D1 instance descriptions | D7 evidence, `supply`, `sharedTarget` | An instance site in `U` is walked with the closing use's evidence; nested forward entries compose like `constraint` evidence. Land D1 after opaque Stage 1 (done) so the walk's evidence path is stable |
| D1 and `Code.Bound` sites | D5 `Code.Binds` (Stage 2) | Both change bound sites. D1 refuses a bound instance site in its first version (Q3); revisit after Stage 2 |
| D2 frames | 1.10 note: "a generic method this receiver does not fix" | That refusal may become reachable after D2; add its probe as a test |
| D4, Y3 | D4 identities: `Named` carries an origin | `Ref(Owner)` flattens `Owner`; only `Ref`'s origin is in the `Ty` |
| D5 presence | `Code.Ty` shape changes (1.4: `Opaque` gained `TypeId`) | Same file region of `Builtin.roc`, same translators to migrate. Coordinate the `normal_form_version` and `CACHE_VERSION` bumps: each change takes the next number when it lands |
| D6 `Code.ty_of` | D6 `Code.type_id`, `Code.proxy`, `moduleIdentities` | Same intrinsic path and error style. After D1, `type_id` inside a generic function can also be an instance constant instead of `type_id_not_nominal` (Q8) |
| D7 | `Code.type_id`/`Code.prim` constants | A clause that reads an identity constant is refused by D7's message |
| D8 | D5 `Value.Encoded` | The `Id` case of Y8 is solved by D5 plus a library change. `Value.Absent` is done |
| D9 | 0.3 (F4) `StagedCode.foreign` | D9 extends the same report to the site's own module |
| Files | `src/check/code_reifier.zig`, `src/reify/mod.zig`, `src/compile/cache_config.zig`, `design.md` | The opaque session edits these files now. Start each stage of this proposal from a tree where that session's work is committed |

## 6. Staged Implementation Plan

```
Stage 0  bugs and diagnostics, no API change
         0.1 D4 rule (Y10)  ->  0.2 Y3 walk
         0.3 D2 frames (Y2)  ->  0.4 D3 named-site evidence (Y2)
         0.5 Y9 interim refusal
         0.6 D7 message, 0.7 D9 site in reports
   |
Stage 1  Surreal adoption of Stage 0: helper libraries, Ref read views (library only)
   |
Stage 2  D1 instance descriptions (Y1, Y9 final)
   |
Stage 3  D6 Code.ty_of (closed, then generic through D1); D5 defaults
   |
Stage 4  Surreal adoption: fragments, table("name"), defaults, Table without Code;
         langref; README limits table
```

Y7 is outside these stages. Y8 waits for opaque Stage 2.

### Stage 0

Status: done on branch `reify` (uncommitted), except 0.5 (skipped, Q3). The
`docs/langref/` part of 0.8 was done in the combined langref pass (see 4.4).

| Item | Status |
|---|---|
| 0.1 | done. design.md "Record Extension Well-Formedness" declares the rule as a new typing rule. `DescriptorFlags.record_row` and a refusal in `unifyVars`; no solver-mutating rewrite. Tests: `src/check/test/record_extension_test.zig`, CLI |
| 0.2 | done. `collectRecordFields` `.nominal` arm, `BoundNominal`. t7 (Monotype `rowExtensionChainResolved` stopped at a nominal) fixed too |
| 0.3 | done. `FrameId`, `Walk.frames`, canonical record digest in `instantiationKey`. `collectVariants` follows a fixed tag row tail too (see Q12) |
| 0.4 | done. `publishNamedCodeSiteEvidence`, `siteEvidence` at the root |
| 0.5 | skipped (Q3: Y9 waits for D1) |
| 0.6 | done. Rejection kind `code_value`, "Cannot Reify A Code Value", names the constant |
| 0.7 | done. A refusal outside the site's region names the site |
| 0.8 | done: `CACHE_VERSION`. `normal_form_version` unchanged (Q11). `docs/langref/`: done in the combined langref pass (4.4): `docs/langref/records.md` "What Can Extend a Record" (D4) |

Found during Stage 0, not fixed:

| Finding | Repro |
|---|---|
| The Boxy pipeline (`--specialize=no`) crashes on a record extended by a `:=` nominal ("record field access receiver did not have known boxy record fields"). It crashed before Stage 0 too | `Ref(r) := { ..r }`, `Owner := { id : Str, name : Str }`, `name_of : Ref(Owner) -> Str`, run with `--specialize=no` |
| Normalization breaks a loop invariant (`loops.noneRewritable`) for a tail-recursive helper whose body matches on a tag union, closed or open | `cat_after : [Cat, Dog], U8 -> Bool`, `cat_after = \|pet, k\| if k == 0 (match pet { Cat => True, _ => False }) else cat_after(pet, k - 1)`, passed by name to a `Code([Cat, Dog] -> Bool)` |
| A tag-union row `[A, ..r]` with a non-tag argument is not covered by D4 | not probed |

| Item | Files | Tests (validate each by reverting the change) |
|---|---|---|
| 0.1 Record Extension Well-Formedness (D4, Y10). Declare the rule in design.md near "Type Alias Invariant" (`design.md:4244`) | checker: declaration backing parameters and the application of a nominal or alias (`src/check/Check.zig`); `src/check/report.zig` | 3.1 table: both sides, CLI and checker unit tests |
| 0.2 Walk follows an inspectable nominal extension (Y3) | `collectRecordFields` `src/check/code_reifier.zig:7325-7369` | 3.6 table |
| 0.3 Frames (D2) | `TypeRef` `:346`, `fixedType` `:8077`, `resolvedType` `:8071`, `describeDefinition` `:1169-1186`, `enclosedLambda` `:1471-1486`, `matchRecord` `:7809-7857`, `instantiationKey` `:8038` | 3.3.3 table, rows 1 to 5 |
| 0.4 Named-site evidence (D3) | `reifyNamedSite` `:9954`; `Site` of `reifyLambda` `:658`; if needed, publication of a lookup's evidence | 3.3.3 table, row 6 |
| 0.5 Y9 interim refusal | `collectRecordFields` `:7348-7354`, site owner and `schemeVars` | 3.2 |
| 0.6 D7 message and place | `lambdaRow` `:1235-1237`, `curriedLambdaRow` `:1300`, `inlineBody` `:1585`, `exprRef` `:2112-2117` | 3.9 |
| 0.7 D9 | `Walk.beginSite`, `Rejection`, `src/check/report.zig`, `src/check/problem/types.zig` (`StagedCode`) | 3.12 |
| 0.8 Versions and docs | `CACHE_VERSION` (`src/compile/cache_config.zig:452`); `normal_form_version` only if a rule changes (`src/reify/mod.zig:40`); design.md "Code Reification" (D2 frame sentence, Y9 seal rule); `docs/langref/reifying.md` limits table (follow `docs/langref-style-guide.md`) | fingerprint test |

### Stage 1

Status: done on branch `reify` (uncommitted). Library and example only: no
compiler change was necessary. The read view is the existing `Surreal.Linked(r)
:= { ..r }`, not a new `Surreal.Ref`: the example had it for alias rows before
this stage, with `Translate.at` binding it as a link hop.

| Item | Files |
|---|---|
| 1.1 `Surreal.Ref(r) := { ..r }` read views for alias and nominal rows, stored rows with `Link`; `Translate.at` binds `Named("Surreal.Ref", _)` as a link hop (analysis `lib.diff`). Done, as `Surreal.Linked` | `examples/reifying/surreal/Surreal.roc`, `Translate.roc`, `Types.roc` |
| 1.2 An annotated helper module of open-row predicates, used by `main.roc`. Done | `examples/reifying/surreal/` |
| 1.3 README: remove the limits that Stage 0 lifts. Done | `examples/reifying/surreal/README.md` |

Done (1.1, 1.2, 1.3):

| Item | What was done | Where |
|---|---|---|
| 1.1 | Stage 0 (Y3) made the queries work with no library change: `p.owner.name` through `Linked(Owner)` is `owner.name`. Three library gaps stayed. (a) A `Linked` holds the fields of its row and not its name, so a live query did not find the table of a nominal row. `Types.lookup_read` finds it by the record behind each table's row. (b) A link to a nominal row that links to itself holds `Recursive("Surreal.Link")` and `Recursive("Owner")`, so `define_read` saw a `Recursive` where the read row had the type. `Types.unfold` puts the `Named` that a `Recursive` refers to in its place, as `Code.Ty` defines it (the nearest enclosing `Named` of that name). `site_of` and the new `Types.open` use it. (c) A read row that holds a `Linked` of itself (`Recursive("Surreal.Linked")`) is refused by `define_read` (`BadSchema`) and as a whole row (`Unsupported`): its fetch plan has no end. A field read through it works | `Types.roc:183-191` (`open`), `:200-208` (`site_of`), `:225-243` (`unfold`), `:296-310` (`lookup_read`), `:152` (`agree`); `Translate.roc:816-826`, `:841`; `Surreal.roc:96-106`, `:2835`, `:2858` |
| 1.2 | `Clinic.roc`: `bill`, `dose_cost`, `positive_doses`, `fee_covers_items`, `seen_from`, `seen_before`, `seen_since`, `too_old`, `low_stock`, each annotated with open rows. `bill` calls `dose_cost`, `seen_since` calls `seen_from` and `too_old` calls `seen_before` (the Y2 chain, D2). `main.roc` passes them by name to `filter_by`, `check`, `assert_each`, `update_by` and `delete_by`. The script is `expected_output.surql` byte for byte, as before | `examples/reifying/surreal/Clinic.roc`; `main.roc:110-114`, `:387-389`, `:766`, `:915`, `:969` |
| 1.3 | The rows "A read row links to an alias row only" and the Y3 note of "`Link` and `.get()`" are gone. New rows: "A nominal row in a `Linked`", "A `Linked` holds the fields of its row, not its name", "A read row that holds a `Linked` of itself is refused". New feature row for a helper over an open row; `Clinic.roc` in the file and cost tables. The Y9 row stays (Q3) | `examples/reifying/surreal/README.md` |

Tests:

| Test | Pins |
|---|---|
| `QueriesTest.roc:486-537` | `Linked(Patron)` with a nominal, self-linked `Patron`: field reads, the whole read row (`holder.{ address, id: record::id(id), name, sponsor }`), `match` and `map_ok` on `?sponsor`, the live query finds `patron` and watches `holder` and `holder.sponsor`; a read row that holds a `Linked` of itself: field reads two hops deep work, the whole row is `Unsupported` |
| `SchemaTest.roc:529-614` | `OrderRead` with `Linked(Customer)` (nominal), `CustomerRead` with `referrer ?: Linked(Customer)` agree with their stored rows; `CustomerLoop` is a `BadSchema` at `referrer.referrer` |
| `TypesTest.roc:352-375` | `read_sites` marks a `Linked` site; `lookup_read` finds `customer` for the `Linked` and its inner `Link`; `lookup` does not find the record; an alias row with the fields of `Customer` makes it ambiguous |
| `Types.roc` expects | `unfold` replaces only a `Recursive` that refers to the given `Named`; `open` |

Found during Stage 1, not fixed (library or language, no compiler change asked):

| Finding | Detail |
|---|---|
| Corrected in Stage 4: this finding was wrong. An open-row helper takes a record-backed `:=` row, by D4 (design.md "Record Extension Well-Formedness"); a `::` row is refused by design | Stage 1 said that `Owner :=` does not unify with `{ address : { city : Str, ..a }, ..o }`. It does: `Clinic.low_stock` takes `Medication := { .., stock : I32 ?? 0 }` in `main.roc` (Stage 4), and the probes `defaults/p5_openrow.roc` and `defaults/sur/s2_clinic_nominal.roc` of the Stage 4 session show it |
| A self-linked read view | The proposal's 4.3 form, `Owner := { .., referred_by ?: Ref(Owner) }`, is a read row that holds a `Linked` of itself. Its whole row has no finite SurrealQL form, and a live query over it watches one hop. Stage 1 refuses it (see 1.1 (c)); Q13. Done in the Q13 follow-up: accepted, the whole row stays refused |

### Stage 2

Status: done on branch `reify` (Stage 2 committed as `c57b0dd5a8`, Q16 as
`decea89214`, Q17 and generic constants uncommitted), except 2.9. Planning found two
questions that change what the compiler accepts (Q14, Q15), now decided. No checker change: the reifier finds each
site's owner and each use from published data.

Done:

| Item | What was done | Where |
|---|---|---|
| 2.1 | `planInstances` reads every checked body once and records each site and each use with whether its type mentions the owner's quantified variables. A fixpoint finds the templates that hold an inventory. An instance site gets no node (`markInstanceSite`); a lambda written at it keeps its checked form under a new id, which a walk from another module reads. The table is `CodeInstanceTable` in the checked module data, not `CheckedCodeSite` or the template table | `src/check/code_reifier.zig:10808`; `src/check/checked_artifact.zig:34814`, `:13706` |
| 2.2 | `closeUses` builds one table per closing use; `TableBuilder` re-runs the chain of uses (D2 frames), keys tables by module, template and `instantiationKey` (so a recursive template is a graph), and describes each site by its recipe (inline lambda, named function, template call). A use is a call, a value lookup, a direct static dispatch (Q14 a), or a call through a procedure alias | `src/check/code_reifier.zig:11297`, `:11447`, `:5771` |
| Q15 | A template call reads the call's type: `templateSite` instantiates the template's scheme at the callee's type, as `rootSite` does for a named site (`TemplateFixing`) | `src/check/code_reifier.zig:993`, `:1011` |
| 2.3 | The table rides on the root frame of the evidence chain (`EdgeEvidence.instances`), the draft and sealed template requests and the queued job. A forward use reads its nested table from the table in force; an alias call passes the use's table on (`InstancesFrom`). Debug assertion: a template with an inventory is never requested without a table | `src/postcheck/monotype/lower.zig:2214`, `:2263`, `:10504`, `:47758`, `:47768` |
| 2.4 | Not a hidden argument: a description is a constant, so Boxy plans one worker per table (`WorkerIdentity.instances`). A nested callable shares its holder's table | `src/postcheck/boxy/plan.zig:1005`, `:2307`, `:6934`, `:6953`; `src/postcheck/boxy/lower.zig:21115` |
| 2.5 | Three named refusals at the use or site: `bound_instance` ("Cannot Bind Inputs In A Generic Function"), `instance_through_evidence` (Q14 b, "Cannot Reify Through A Where Requirement"), `instance_in_local_generic`. A refusal inside the template is reported in the use's module at the template's source, naming the use (D9, F4). A refused use is a `runtime_error` | `src/check/problem/types.zig`, `src/check/report.zig`, `src/check/checked_artifact.zig:39259` |
| 2.6 | Nothing to remove: 0.5 was skipped (Q3) | |
| 2.7 | `ROC_REIFY_INSTANCES` prints each closing use and its table, nested tables indented | `src/base/dev_diagnostics.zig`, `src/check/code_reifier.zig:11467` |
| 2.8 | design.md: stage table, seal rule, instance invariant, "Static Dispatch In Monotype", "Boxy Dictionaries And Vtables", "Developer Diagnostics". docs/langref/reifying.md: query fragments and the two refusals | design.md, `docs/langref/reifying.md` |
| 2.10 | `CACHE_VERSION` 203. No `normal_form_version` bump: no rule changes, a description is built for one concrete type as before | `src/compile/cache_config.zig` |

Tests:

| Test | Pins |
|---|---|
| `test/cli/StagedFragment.roc`, Monotype and `--specialize=no` | an annotated fragment at `Pet` and at `Owner` (Y1), an unannotated fragment with a direct call (Y9 final), a fragment used as a value, a fragment that calls a fragment (forward entries), a method `q.only_named()` (Q14 a), a `where` dispatch in the site's lambda at `U8` and at `Str`, a fragment that no use closes, a site that names no variable of its generic function (described once) |
| `test/cli/StagedFragmentRefused.roc` | `Code.Bound` site in a generic function; a method selected by a `where` requirement (Q14 b) |
| `test/cli/StagedFragmentPackage/`, both lowerings | a package's fragment and a fragment that calls it, described at the app's use |
| `test/cli/StagedFragmentPackageRefused/` | a refusal inside a package fragment's site is in the package file and names the app's use |
| Template call at `Pet` (Q15) | scratchpad `d1/tc.roc`: the description has every field of `Pet` |
| `test/cli/StagedFragmentStored.roc`, both lowerings (Q16) | a constant that holds a fragment (`ops = { f: named_only }`), an alias call, an alias used as a value (`xs.map(for_pets)`), an alias at the fragment's own type used as a value, a `for` loop over a type whose `iter` holds a site |
| `test/cli/StagedFragmentConstant/`, both lowerings (Q16) | package constants with no annotation that hold fragments: a tuple, a record, and a constant that holds both. The app uses one field at `Pet` and at `Person` |
| `test/cli/StagedFragmentImplicitMethod.roc`, check and both lowerings (Q17) | a site in `to_inspect`, and a use in `is_eq` of a fragment, are refused at the method; the program is a runtime error, with no panic |
| `test/cli/StagedFragmentLoopRefused.roc` | a refusal that a `for` loop's `iter` use reaches is reported at the iterable; the loop is a runtime error on both lowerings |

Q16 (decided A, accept), done:

| Item | What was done | Where |
|---|---|---|
| Scan of bindings | Publication also reads each compile-time constant body and each top-level binding that evaluation computes. A use at a variable of the binding's own type is not closing: a use of the binding fixes it | `src/check/code_reifier.zig:11170` (`scanBinding`) |
| Stored table | `ConstFn.instances` (module, table): a stored function keeps the table it was built with, through `Mono.FnTemplate.const_instances`, `LIR.FnTemplate.instances` and the `ConstStore` writer. A restore puts it on the root frame of the restored evidence | `src/check/const_store.zig:486`; `src/postcheck/monotype/lower.zig:2234`, `:52385`; `src/postcheck/solved_lir_lower.zig`; `src/eval/const_store_writer.zig`; `src/lir/program.zig` |
| Binding use | A binding stored at its own type variables keeps no table; its use gives one, and an exact alias's lookup takes it (`BindingInstances`) | `src/postcheck/monotype/lower.zig:2214`, `:22468`; `src/postcheck/boxy/plan.zig:6949`, `:6957` |
| `for` loops and `==` | Found while testing Q16: a `for` loop's `iter` call, `a == b` on a written `is_eq` and `T.method(..)` are direct static dispatches, so they are uses (Q14 a). The `iter` use is keyed by the loop's body; a refused one makes the loop a runtime error (`refuseInstanceLoop`) | `src/check/code_reifier.zig:678`, `:701`, `:11391`; `src/check/checked_artifact.zig:13723`; Monotype `IteratorDispatchTask.use`; Boxy `IteratorCallSite.use` |
| Version | `CACHE_VERSION` 204 | `src/compile/cache_config.zig` |
| Generic constants | A constant whose type a use fixes (an unannotated `pair = (named_only, adults)` in a package, used in the app) is computed by its entry template at each use. Publication reads the constant's body at the entry template's variables, so the entry template gets an inventory of forward entries. A use of the constant is a closing use: `usedConstant` and `constantTarget` fix the entry template's variables from the type the use requests. Monotype puts the use's table on the root frame of the constant's evaluation; Boxy plans the entry worker with it | `src/check/code_reifier.zig:5825`, `:5855`, `:11018`, `:11310`, `:12001`; `src/postcheck/monotype/lower.zig:17880`, `:47450`; `src/postcheck/boxy/plan.zig:2311`, `:7107`; `src/postcheck/boxy/lower.zig:22624` |

Q17 (decided A, refuse by name at the method), done:

| Item | What was done | Where |
|---|---|---|
| Methods | `to_inspect`, `is_eq`, `to_hash`, `encoder_for` and `parser_for`, read from the module's method registry. The compiler calls them with no written use, so no use fixes their types | `src/check/code_reifier.zig:11162`, `:11172` |
| Methods across modules | A registry procedure target is always a template of the method's own module (debug assertion, `src/check/code_reifier.zig:11189`). The registry follows a method bound by value only through the module's own bindings (`src/check/static_dispatch_registry.zig:1150`), so `to_inspect = Other.render`, directly or through a binding of the module, gets no entry: the compiler never calls it, and a site in `Other.render` is described only at written uses. A use of `Other.render` in a method's lambda is refused as below. Also on upstream: inspection renders the default form for such a method, and an explicit call `x.to_inspect()` stops publication at an invariant ("could not resolve a checked dispatch target for an owned method"). If the registry starts to follow these bindings, the refusal must cover them | `test/cli/StagedFragmentImplicitAcross/`, check and both lowerings |
| Refusal | A site at such a method's own variables, and a use there of a template that holds one, is refused with `implicit_method_instance` ("Cannot Reify In A Method The Compiler Calls", detail: the method's name). The method gets no inventory, so the site and the use are runtime errors and both lowerings compile the method as usual | `src/check/code_reifier.zig:11047`, `:11634`; `src/check/report.zig`; `src/check/checked_artifact.zig:39457` |

Not done:

| Item | Reason |
|---|---|
| 2.9 Fuzzer | The fuzz driver walks each print as a site of its own, with no publication. A generic wrapper needs the published table of a closing use read back from the `ConstStore`. Follow-up |
| 3.4.1 digest invariant (two closing uses with one specialization key have equal digests) | Not added. Equal keys give equal tables by construction (the table key is the instance key) |

The repros are in the session scratchpad `d1/` (`y1.roc`, `y9.roc`, `ev.roc`,
`tc.roc`, with `Db.roc` of 1.1).

Found during Stage 2 planning:

| Finding | Detail | Effect on the plan |
|---|---|---|
| A template is reached by static dispatch too | `q.only_named()` (a method with a site, `direct_closed` plan) and `tidy_twice(box)` with `tidy_twice : b -> b where [b.tidy : b -> b]` (`ev.roc`): Monotype specializes `tidy` through the evidence that the use of `tidy_twice` supplies. 3.4.1 names only a call or a value lookup as a use, so no table reaches `tidy`, and lowering stops at the D1 invariant | Q14 |
| A template walk never reads the call's type | `named_as : Str -> Code({ name : Str, ..r } -> Bool)`, called as `pets.filter(named_as("rex"))` at `Pet` (`tc.roc`), is refused with "an open record". `reifyTemplateCall` (`src/check/code_reifier.zig:930`) walks the template body in its own frame, with no instance of the template's variables | Q15 |
| A table can refer to itself | A recursive generic function with a site has a forward entry for its own recursive use, at its own variables. A nested table as 3.4.1 defines it is then infinite | Internal: a table is a graph. An entry names a table by `(U, instantiationKey)`, so a recursive use names the table being built |
| A site records no owner that publication can read | The checker keeps the owner of each site in `code_site_owners` (`src/check/Check.zig:13058`), which it does not publish | Internal, no checker change: the reifier finds the owner by a walk of each template's checked body (and of each generalized local lambda's dispatch scope, Q5) down to the site's expression |
| Evidence of a site lambda | A lambda at a `Code` position is collected with no enclosing template parameters (`collectStagedLambda`, `src/check/checked_artifact.zig:22693`). A `where` dispatch inside it on a variable of the template (`\|x\| x.a == x.b`, `k.is_eq`) must read the closing use's evidence | Internal: to verify with a test before 2.2 |
| Data the plan can use | Each use records its substitution (`siteSubstitution`, `src/check/static_dispatch_registry.zig:2823`) and evidence (`siteEvidence`, `:2790`); each evidence edge records its target's substitution (`targetSubstitution`, `:2766`) | Explicit data for the closing use, for forward entries and (if Q14 says so) for evidence targets |
| Monotype cost | A specialization's identity includes its evidence (`StoredConstFnEvidence`, `src/postcheck/monotype/lower.zig:4179`), and about 15 places start a body's evidence chain (`rootEvidenceWithSubstitution`, `enterEvidenceScope`, restored compile-time functions). The table goes into the root frame of the chain and into the identity, or a debug assertion checks that two requests with one identity have equal digests (3.4.1) | Internal |

| Item | Files |
|---|---|
| 2.1 Inventory and instance sites at publication | `src/check/code_reifier.zig` (`reifyModuleSites` `:9805`), `src/check/checked_artifact.zig` (`CheckedCodeSite` `:2551`, template table) |
| 2.2 Closing uses: walk, tables, cache | new `reifyInstanceUses`; `Walk` |
| 2.3 Monotype: table in the specialization context; restore by entry | `src/postcheck/monotype/lower.zig` (`restoreCodeSiteAtNode` `:47593`, `.code_from_lambda`) |
| 2.4 Boxy: hidden table group | `src/postcheck/boxy/plan.zig` (`pushCodeConversion`) |
| 2.5 Refusals at the closing use (with D9) | `src/check/report.zig` |
| 2.6 Remove the Y9 interim refusal | `collectRecordFields` |
| 2.7 `ROC_REIFY_INSTANCES` | `base.dev_diagnostics.Var`, read only through `base.dev_diagnostics` |
| 2.8 design.md: stage table, seal invariant, instance invariant, Monotype and Boxy paragraphs | design.md |
| 2.9 Fuzzer: generic wrappers around sites | `src/compile/reify_fuzz.zig` |
| 2.10 `CACHE_VERSION`; `normal_form_version` if Y9 descriptions count as a rule change | as above |

Tests: 3.4.3.

### Stage 3

Status: done on branch `reify` (uncommitted). One small checker change: the
checker records a `Code.ty_of` call in `NodeStore.code_identity_uses` with a
new kind `ty_of`, through the path that `Code.type_id` already takes
(`src/check/Check.zig:31809`). There is no new checker record and no new
typing rule.

Done:

| Item | What was done | Where |
|---|---|---|
| 3.1 | `Code.ty_of : Proxy(_t) -> Ty`, intrinsic `code_ty_of`. Publication converts the proxy's type with the walk's `tyOf` and writes the `Code.Ty` with the emitter, as the call's constant node. An open variable is `ty_of_not_closed` ("Type Not Fixed"); a type the walk has no description for is the walk's own refusal. `moduleIdentities` now runs after the sites' plan | `src/build/roc/Builtin.roc:24342`; `src/canonicalize/BuiltinLowLevel.zig:49`; `Reifier.tyOfProxy` `src/check/code_reifier.zig:7857`, `moduleIdentities` `:11124`, `Walk.emitTy` `:10771`; `Emitter.tyValue` `src/check/code_emit.zig:396`; `src/check/checked_artifact.zig:39203`; `src/check/report.zig:6218` |
| 3.2 and Q8 | A `Code.type_id` or `Code.ty_of` call whose proxy type mentions a quantified variable of its template is an inventory entry (recipe kinds `type_id`, `ty_of`), found by the occurrence scan as a site is. Each closing use computes it at the use's instance; a refusal is reported at the use and names the call (D9). A call in a method the compiler calls is `implicit_method_instance` (Q17). Monotype and Boxy needed no change: the call is a `code_from_lambda` with no node, which they restore from the table in force | `IdentityMap` `src/check/code_reifier.zig:11388`, the `.identity` entry `:11589`, `TableBuilder.describe` `:12479`; `CodeInstanceTable.RecipeKind` `src/check/checked_artifact.zig:34848` |
| 3.3 | `presence : [Required, Optional, Default(Value), DefaultComputed]`. `recordTy` reads a defaulted field's default in its declaring module (`default_exprs`, found by content identity through the new `ForeignLookup.resolve_identity_module`). The value is what the walk describes as a literal: numerals at builtin types, `Str`, bytes, lists, tuples, a record that sets every field, tags, `Bool`, a nominal (`Wrap`), and a name of a constant that holds one. A name the walk names as a primitive (a constant of an opaque type), a literal of the author's own type, a value of an opaque type, a call, and a record that leaves out an optional field or a field with a computed default are `DefaultComputed` (a record that leaves out a field with a carried default sets it to that default, Q18). The default is part of the type key and digest (`Member.default`, `Types.values`) | `Reifier.fieldDefault` `src/check/code_reifier.zig:7934`, `defaultValue` `:8014`, `namedDefaultValue` `:8150`; `Default`, `Value` `src/reify/types.zig:111`, `:141`; `Content.default` `src/reify/digest.zig:330`; `Emitter.presence` `src/check/code_emit.zig:456`; `resolveIdentityModule` `src/check/checked_artifact.zig:38758` |
| 3.4 | Translators accept the new variants with no change of behavior: a field with a default is present, as `Required` was | `examples/reifying/dbsp/Dbsp.roc`, `examples/reifying/glsl/Glsl.roc`, `examples/reifying/sql/Sql.roc`, `examples/reifying/surreal/Types.roc` and `Schema.roc` (annotations only) |
| Versions | `normal_form_version` 34 (API shape, Q11), `CACHE_VERSION` 206 (Q18 then took 35 and 207) | `src/reify/mod.zig`, `src/compile/cache_config.zig`, `src/compile/cache_versioning.zig` |
| Docs | design.md "Code Reification": `Code.ty_of`, the identity inventory entries, the presence rule | design.md |

Q18 (decided B, fill), done:

| Item | What was done | Where |
|---|---|---|
| Walk | `recordExpr` sets a member left out with presence `Default(v)` to the literal of `v` at the member's type (`valueRef`: literals, `List`, tuple, record, tag, `Wrap`). A member left out with `DefaultComputed` is refused: "a record literal that leaves out a field whose default is computed. The type does not carry the value of a computed default, so a description cannot fill the field: write the field in the literal" | `recordExpr` `src/check/code_reifier.zig:2564`, `valueRef` `:2629` |
| Defaults | A record in a default that leaves out a field with a carried default is that default's value, as the walk now describes it; one that leaves out an optional field or a computed default is `DefaultComputed` | `defaultValue` `src/check/code_reifier.zig:8014`, `recordTypeFields` `:8170` |
| Versions | `normal_form_version` 35 (a refused form is now described), `CACHE_VERSION` 207 | `src/reify/mod.zig:40`, `:311`; `src/compile/cache_config.zig:492`; `src/compile/cache_versioning.zig:155` |
| Tests | `test/cli/StagedDefaultFill.roc`, both lowerings: the description of `\|s\| { id: s }` holds the filled literals (`Lit(Int(0, I32))`, `Lit(Frac(0.5, F32))`, `Tag("Tablet")`, a list, and a nested nominal's own default `Lit(Str("b"))`); a literal that leaves fields out describes as the one that writes them; the run result has the same values. `test/cli/StagedDefaultFillRefused.roc`: a computed default left out is refused at check, and is a runtime error on both lowerings | `test/cli/StagedDefaultFill.roc`, `test/cli/StagedDefaultFillRefused.roc`; cases in `src/cli/test/parallel_cli_runner.zig:3470-3474` |

Tests:

| Test | Pins |
|---|---|
| `test/cli/StagedTyOf/`, both lowerings | `ty_of` of a nominal, a record and `List(Owner)` equals the `result` of `\|x\| x` at that type; a generic `ty_at(proxy)`; `Tbl.table("owner")` in a package, whose generic body computes `ty_of` and `type_id` at each closing use; defaults declared in a package (`Default(Int(0))`, `Default(List([]))`, a nominal tag `Default(Wrap(Tag("Tablet", [])))`, a constant `Default(Int(7))`, a call `DefaultComputed`); two nominals that differ only in a default differ |
| `test/cli/StagedTyOfRefused.roc` | `ty_of` of an open proxy; a generic `ty_of` at a use that leaves it open (reported at the use, naming the call); a generic `type_id` at a record; `ty_of` in `to_inspect` (Q17); `Code.ty_of` read as a value |
| `test/cli/StagedIdentityRefused.roc` | changed: `open_id` (a generic `type_id`) is accepted now (Q8); its use at a record is the refusal |
| `src/reify/types.zig:1225` | a default is part of the record type key, and values intern |

Found during Stage 3:

| Finding | Effect |
|---|---|
| A record literal in a walked body that leaves out a defaulted field was refused ("a record literal that leaves out a field"). 3.7 says such a value "describes as before (the record literal fills it)" | Q18, decided B and done (the Q18 table above) |
| `Code.ty_of` of an effectful function type gives the walk's refusal "Reified Function Performs An Effect", whose text speaks of a function | Wording only |
| A translator's cut does not change a `Ty`: a default that names a cut member is its value | By design: a type is the same at every site |

| Item | Files |
|---|---|
| 3.1 `Code.ty_of` (D6), closed proxies | `src/build/roc/Builtin.roc`, `src/canonicalize/BuiltinLowLevel.zig`, `moduleIdentities`, Monotype and Boxy constant lowering (as for `code_type_id`) |
| 3.2 `ty_of` as an instance constant | D1 inventory |
| 3.3 Defaults in `Code.Ty` (D5) | 3.7 table |
| 3.4 Migrate translators to the new presence | `examples/reifying/*` |

### Stage 4

Status: done on branch `reify` (uncommitted). 4.4 was done in one combined
langref pass with opaque 3.3. Library, example and README only. Two
compiler bugs found here were fixed apart, before the library change
(`fd91b83dca`: instance tables for a use of a `::` method, and no hoisted
compile-time root over a rigid variable).

Done:

| Item | What was done | Where |
|---|---|---|
| 4.1 | `Clinic.recent` (a fragment over `Query({ since : Datetime, ..p }, { seen : Datetime, ..r })` that passes `Clinic.seen_since` by name) and `Clinic.by_id` (over `Selected(p, { id : Str, ..r })`). `main.roc` uses them in `pet_roster`, `recent_visits` and `add_medication`; the script is the same byte for byte | `examples/reifying/surreal/Clinic.roc:44-54`; `main.roc:746`, `:770`, `:912` |
| 4.2 | `Table.define : Table(row) -> Def(row)` and `define_read : Table(row) -> Defined` describe `row` with `Code.ty_of` of a `Code.Proxy(row)`, an instance constant at each use (D6, D1). Every `define(\|r\| r)` and `define_read(\|r\| r)` is now `define()` and `define_read()`. `Table` held no `Code` value before this stage | `Surreal.roc:1066-1077`, `:1087-1092` |
| 4.3 | `Types.Field` names the long presence type. A `Default(v)` field gets `DEFAULT <literal>` (`Translate.captured` of `v` at the field type) on its `DEFINE FIELD`, at any depth (`size.w`, `crates[*].w`) and on `id`. A literal default in a record of a union arm has no field definition, so it is not in the schema. `DefaultComputed` is a `BadSchema` that names the field, at any depth and on `id`, with or without a `default_by`: "give it a literal default, or remove the `??` and use `.default_by(..)`". A type default and a `.default(..)` on one field are "two defaults". `main.roc`: `Owner` has `tags : List(Str) ?? []` and `Medication` is `:=` with `stock : I32 ?? 0`, in place of two `.default(..)` clauses; the other rows stay aliases | `Types.roc:23-33`, `scan_field` `:356`, `key_type` `:463`, `field_defs` `:642`, `defs_of` `:664`; `Schema.roc:627-640`; `main.roc:26`, `:42` |
| 4.4 | `docs/langref/reifying.md`: "Query Fragments" (what a use is: a call, a method call by dispatch or by the type's name, a value at a fixed type, an alias, a constant, a fragment that calls one, a `for` loop's `iter`, a top-level `expect`; a refusal in a fragment shows at the fragment's source and names the use; the three refusals and why), "Record Fields" (`Required`, `Optional`, `Default(value)`, `DefaultComputed`, which defaults carry their value, the Q18 fill and its refusal, a record extended by a nominal record), "Type Descriptions" (`Code.ty_of`) and "Proxies in Generic Functions" (`ty_of` and `type_id` at each use, `type not fixed`, `not a nominal type`), "Every Report". `docs/langref/records.md`: "What Can Extend a Record" (D4: what `..r` accepts, the opaque refusal, the hint at a call) | `docs/langref/reifying.md`, `docs/langref/records.md` |
| README | New section "Row types and defaults" (aliases and nominals both work with open-row helpers; `??` needs `:=` or `::`). Feature rows: default from the type, a helper over an open row at a nominal row, a query fragment. Limits: the `define(\|r\| r)` row (Y6) and the Y9 row are gone; new rows for a fragment that needs an annotation (Y1b), a default in a union arm, and a default that is not a literal. Line references and the cost table updated | `examples/reifying/surreal/README.md` |

Tests:

| Test | Pins |
|---|---|
| `QueriesTest.roc` "query fragments" | `started_by` and `by_id` at `Purchased` and `Reviewed`; `edge_ids`, a fragment that calls both; `whole_by_id` gives the whole row of `Product` and of `Customer` (the columns of each use's row) |
| `SchemaTest.roc` "defaults from the type" | `Pack`: `DEFAULT` for `id`, an integer, `Dec`, `F64`, `Str`, a list, a nominal tag, nested and list-element fields; no `DEFAULT` in a union arm; two defaults; `DefaultComputed` at the root, with a `default_by`, nested (`inner.stamp.label`) and on `id` |
| Server (SurrealDB 3.3.4) | the `Pack` schema runs; a create and an `INSERT` that leave fields out get the defaults, a create with no key gets `pack:main`; an arm record without its defaulted field is refused by `TYPE` |
| `expected_output.surql` | unchanged: `main.roc` prints the same script |

Found during the langref pass (4.4), not fixed:

| Finding | Repro |
|---|---|
| Monotype crashes ("instantiation record row extended into a non-record type", `flattenRecordRow`) when a generic function over a record-row nominal is called at a structural record or at an alias of one. A direct field read works | `Ref(r) := { ..r }`, `name_of : Ref(r) -> Str`, `name_of = \|_o\| "x"`, `tag : Ref({ id : U64 })`, `tag = Ref.{ id: 7 }`, then `name_of(tag)`. The same with `Ref(Size)`, `Size : { w : F64, h : F64 }` |
| Boxy (`--specialize=no`) crashes ("checked nominal declared field order had an open backing row") when the same generic function is called at a record-row nominal extended by a `:=` nominal | `Labeled(r) := { label : Str, ..r }`, `Point := { x : F64, y : F64 }`, `label_of : Labeled(r) -> Str`, `label_of(Labeled.{ label: "home", x: 1, y: 2 })`. Monotype runs it |
| `instance_in_local_generic` ("Cannot Reify In A Local Generic Function") has no test, and a probe did not reach it: a block lambda `twice = \|q\| named_only(named_only(q))` used at two row types describes at each | `reifying.md` "Every Report" lists the report by its own text |

| Item | Files |
|---|---|
| 4.1 Fragments in `QueriesTest.roc` and `main.roc` (section 4.1) | `examples/reifying/surreal/` |
| 4.2 `Surreal.table(name)`, `Table` without `Code`-derived data, `rows()` for correlated subqueries | `Surreal.roc`, `Types.roc`, `Schema.roc` |
| 4.3 Defaults from types; `DefaultComputed` refused with advice | `Types.roc`, `Schema.roc` |
| 4.4 Langref: instance descriptions, `Code.ty_of`, presence variants | `docs/langref/reifying.md` |

### Q13 Follow-Up: Self-Linked Read Rows

Status: done on branch `reify` (uncommitted). Library, tests and README only.
No compiler change. `expected_output.surql` does not change.

| Item | What was done | Where |
|---|---|---|
| Q13 a | `define_read` accepts a read row that holds a `Linked` of itself. `Types.agree` takes `seen`, the pairs of a `Linked` and a stored type on the way. A `Linked` opens its row with each `Recursive("Surreal.Linked")` that refers to it in its place (`Types.unfold`), so the walk meets the same `Linked` one hop down, and that pair agrees. `Types.key` of a `Linked` is `Linked<fields>`, so two `Linked` of other rows have other pairs | `examples/reifying/surreal/Types.roc:82-106` (`check_read`), `:151-192` (`agree`), `:278-298` (`key`) |
| Q13 b | `Types.lookup_read` finds the table of a `Linked` by agreement with each row (`Types.agree`), not by an equal `key`. A `Linked` of a self-linked read row has `Recursive("Surreal.Linked")` where the stored row has a `Link`, so the keys differ. Without this, a live query over it was a `BadSchema` | `Types.roc:324-345` |
| Q13 c | `select(\|o\| o)` stays `Unsupported`. The message says why and what to write: "a whole read row that holds a `Linked` of itself has no finite fetch plan: each `Linked` of it fetches the row again, with no last hop; select its fields, or make the link a `Linked` of the stored row (`Linked(Owner)` for a stored `Owner`), whose own links are `Link`" | `Translate.roc:817` |
| Q13 d | A live query watches the first hop: `Types.read_sites` stops at the `Linked` that refers back. `sponsor = $parent.id` is watched, `sponsor.sponsor` is not | `Types.roc:752` (no change) |
| Q13 e | README: a rule row for the self-linked read row; the limit "is refused" is now "A whole read row that holds a `Linked` of itself is refused" (By design); a new limit "A live query over a read row that holds a `Linked` of itself watches the first hop" (Fix later) | `examples/reifying/surreal/README.md` |

Tests:

| Test | Pins |
|---|---|
| `SchemaTest.roc` (`CustomerLoop`, `CustomerLoopExtra`, `OrderLoop`) | The self-linked read row agrees and writes no statement; one with an extra field is a `BadSchema` at the top; a `Linked` of itself where the stored link points at another table is a `BadSchema` at `customer` |
| `TypesTest.roc` (`CustomerLoop`) | `read_sites` has one site, `referrer`; its key holds `N:Surreal.Linked`; `lookup_read` finds `customer`; `check_read` is `Ok`; `key` of a `Linked` |
| `QueriesTest.roc` (`PatronLoop`, `CardLoop`) | Field reads one and two hops deep; the whole row is `Unsupported` with the new message, also in a `Linked(PatronLoop)` of another table; a live query watches `sponsor` and not `sponsor.sponsor`, and `holder` and not `holder.sponsor` |
| `LiveTest.roc` (`ChainRead`) | The request of a live query that reads two hops: one `read` statement, `next = $parent.id` |

### Y8 Option A: Type Arguments in `Named`

Status: done on branch `reify` (uncommitted), by user decision (option A).
A reifier change and a library change. No checker change, no new typing rule.

The cause: `Id(row) := { table, key, phantom : List(row) }` put the row type
into the type of the captured value, so `slotShape` refused a row with an
optional field, a `Set` or a `::` type. Roc accepts a type parameter that the
backing does not hold, and still keeps `Id(Customer)` from `Id(Product)`. The
reifier did not carry the type arguments of a `Named`, so the library had no
other way to see the row.

| Item | What was done | Where |
|---|---|---|
| `Code.Ty` | `Named(Str, List(Ty), Ty)`: name, type arguments in declaration order, backing. `children` gives the arguments, then the backing. `name()` spells the arguments, as for `Opaque` (`Builtin.Try(I64, Str)`) | `src/build/roc/Builtin.roc:23664-23675`, `:23737`, `:23810` |
| Types | `Ty.nominal` has `args`. The arguments are part of the key, `has_recursive` and the digest. They are inside the nominal, as its backing is: `Spelling.partsOf` gives the arguments then the backing, `freeNames` drops the nominal's own name from both, `label` counts the arguments. `unfold` spells the last part. `widens` reaches the arguments as it reaches the backing | `src/reify/types.zig:173`, `:420-431`, `:599`, `:623`, `:914`; `src/reify/digest.zig:310` |
| Walk | `Reifier.nominalTy` reads the use's arguments inside the open nominal and before the nominal binds its own variables, as `nominalInstanceKey` reads them. `tryOver` gives `Try` its two arguments | `src/check/code_reifier.zig:7677`, `:2798` |
| Emitter | `Named(name, args, backing)` | `src/check/code_emit.zig:446` |
| Library | `Id(row) := { table : Str, key : Str }`. `Types.row_of` reads the row of a `Link` or an `Id` from the type arguments; `id_target`, `link_target` and `site_target` are gone. `Types.unfold` maps the arguments too | `examples/reifying/surreal/Surreal.roc:34-39`, `Types.roc:229-245`, `:256` |
| Translators | Every `Named(` match has three parts | `src/build/roc/Builtin.roc`, `examples/reifying/{surreal,sql,glsl,dbsp}` |
| Versions | `normal_form_version` 36, `CACHE_VERSION` 209 | `src/reify/mod.zig:40`, `src/compile/cache_config.zig` |
| Docs | design.md "Code Reification"; `docs/langref/reifying.md` (the `Ty` row and the `Named` arguments); the Surreal README finding 1 | |

Not changed: `slotShape` reads the backing only, so a captured `Link(row)`
still holds its fetched row and is still refused when that row has a field
of an opaque type. Since D8 (`Value.Absent`, Q9), a row with an optional
field binds.

## 7. AGENTS.md Constraints

| Constraint | How the design meets it |
|---|---|
| No workarounds, fallbacks, heuristics | D1 reads scheme variables and recorded substitutions; D2 reads frames; D3 reads recorded evidence; D4 is a declared rule; D5 uses the existing `isConstantForm` test, which is syntax |
| Consume explicit data | The enclosing template of a site, its scheme variables, a use's substitution and evidence, a field's default identity: all recorded by the checker |
| Invariants: debug assertion, `unreachable` in release | After D4, a non-record extension in the walk is an invariant. An instance site with no table entry in lowering is an invariant. User failures (an open proxy for `ty_of`, a refused instance) are reported |
| Solver-Mutating Rewrites | None. D4 is a typing rule by a well-formedness check, declared in design.md, tested on both sides; it uses no `dangerousSetVarRedirect` and restamps no plan |
| Backends follow LIR `incref`/`decref` | No backend change. A table entry is a constant; Boxy passes it as any hidden argument |
| Developer diagnostics | `ROC_REIFY_INSTANCES` through `base.dev_diagnostics` only; no release-build variable |
| No JSON | No new format |
| Fuzzers compose small typed constructs | 0.3 and 2.9 extend the reify fuzzer by composition, not by scenario catalogs |

## 8. Open Questions

| # | Question | Proposed answer |
|---|---|---|
| Q1 | Is a record extension by a `:=` nominal with a record backing part of the language (D4)? Ask rtfeldman | Decided (Stage 0): yes, as a new typing rule declared in design.md "Record Extension Well-Formedness". A `::` opaque type is refused in every module, its own module too. A literal-constrained variable is refused in a row slot |
| Q2 | May an opaque nominal extend a record in its own module (`Ref(Time)` inside `Time`'s module)? | Decided (Stage 0): no. The walk's opaque arm is an invariant |
| Q3 | Y9 interim: refuse now (programs that describe almost right become errors) or wait for D1? | Decided: wait for D1. No interim refusal (0.5 skipped) |
| Q4 | D1: are template calls and named sites inside generic functions instance sites? | Decided: accepted as proposed. Yes, every walked site kind. `Code.Bound` sites: refused by name in the first version |
| Q5 | D1: a block-level generalized lambda inside a function holds a site. Whose scheme counts? | Every enclosing generalized scheme: the inventory belongs to the nearest one, and it forwards to the outer one |
| Q6 | D1: should `roc check` of a package describe instance sites that only its `expect`s close? | Yes: an `expect` is a closing use like any other |
| Q7 | D5: carry a computed default as a description (a row) later? | Not now. `DefaultComputed` is explicit; a library has `default_by` |
| Q8 | After D1, should `Code.type_id` inside a generic function be an instance constant instead of `type_id_not_nominal`? | Decided: accepted as proposed. Yes, with D6 in Stage 3 |
| Q9 | D8: implement `Value.Absent`? | Done: the SQL and Surreal examples needed a structural optional capture. The `Id` case goes through opaque D5 |
| Q10 | Y1b: should the argument of a `where` method requirement become a `Code` position once dispatch resolves? Ask rtfeldman | Decided: no. The mismatch report adds a hint (3.5) |
| Q11 | Does a newly accepted type (Y3) or a newly refused site (Y9) need a `normal_form_version` bump? | No for Y3 (no rule changes); yes for D5 (API shape); bump `CACHE_VERSION` for every artifact or digest change |
| Q12 | D2: bind tag-union rows too (`matchTagUnion` binds none today)? | Decided (Stage 0): yes. The walk follows a tag row tail that the call fixed (`collectVariants`). With "no", a helper `\|p\| match p { Cat => True, _ => False }` read at `[Cat, Dog]` described as `True`, which is not what the program runs |
| Q13 | Stage 1: should a read row that holds a `Linked` of itself (`OwnerRead := { .., referred_by ?: Linked(OwnerRead) }`, the 4.3 form) be accepted? | Decided: accept, as a follow-up after Stage 4. Done (see "Q13 Follow-Up"): `define_read` compares the two recursive types coinductively, `select(\|o\| o)` (the whole row) stays refused (no finite fetch plan), and a live query watches only the first hop. `Linked(Owner)`, a `Linked` of the stored row, whose own links are `Link`, stays the form that has a whole row |
| Q14 | D1: a template with instance sites reached by static dispatch, not by a call or a value lookup. (a) A `direct_closed` or `direct_parametric` plan names the method (`q.only_named()`). (b) An `evidence_dependent` plan reaches it through the evidence a use supplies (`ev.roc`). What does the compiler do? | Decided: (a) is a use like a call: the plan names the target and the use records its substitution, so the method gets an instance description. (b) is refused at the closing use, with a named report, in this version: no evidence edge carries a table in Monotype or Boxy (the recommended mix). Options were: A. Both are uses. (a) is a use like a call (the plan names the target and the use records its substitution). For (b), the module that records the evidence edge gives the edge a table, at the edge's `targetSubstitution`; Monotype carries it in the evidence target, Boxy in the dictionary slot. Accepts `ev.roc`. B. (a) is a use; (b) is refused at the closing use, by name ("a method with `Code` sites reached through `where` evidence"). C. Both refused by name. A is the most work (all three stages get an evidence path). B and C refuse programs that type-check. Recommended: A for (a), because a fragment is often a method; B for (b) in the first version |
| Q15 | D1 (Q4): a template call inside a generic function is an instance site. But a template walk never reads the call's type, so a generic template is refused even at a closed call (`tc.roc`). In Stage 2, or apart? | Decided: A. Stage 2 first instantiates a template's variables from the call's type, as `rootSite` does for a named site (this also accepts `tc.roc`), and then makes a template call an instance site. Option B was: Stage 2 refuses, by name, a template call whose type mentions a variable of the enclosing template; the template fix is a separate item. A changes what is accepted at a closed call too |
| Q16 | A fragment held as a function value that compile-time evaluation stores: a constant `ops = { f: named_only }`, or a top-level alias used as a value (`xs.map(for_pets)` with `for_pets = named_only`). A call through the alias works. The stored function (`ConstFn`) carries no instance table, so restoring it reaches the template without one. Accept or refuse? | Decided: A (accept). Done in Stage 2 (see the Q16 table there). A `for` loop's `iter`, `==` on a written `is_eq` and `T.method(..)` are uses too (Q14 a) |
| Q17 | A method the compiler calls with no written use, when it holds an instance site: `to_inspect` from `Str.inspect` or an `inspect` of a record that holds the type, and `is_eq`, `to_hash`, `encoder_for` and the parsers from a derivation over a structure that holds the type. No use expression exists, so publication builds no table. Accept or refuse? | Decided: A (refuse by name at the method). Done in Stage 2 (see the Q17 table there). B was: accept, with a table per derivation node and per descriptor slot, built where the derivation or the inspect is planned |
| Q18 | D5: a record literal in a walked body that leaves out a defaulted field was refused ("a record literal that leaves out a field"). Should the walk fill the field from `Default(v)`, where the type carries the value? | Decided: B. The walk fills the field from `Default(v)`; a `DefaultComputed` field left out stays refused, and the report says the default is computed. Done in Stage 3 (see the Q18 table there). Option A was: keep the refusal |
