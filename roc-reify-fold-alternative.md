# Reification as a fold: the translator owns the description

An alternative to the fixed `Code.Ir` of `roc-reify-proposal.md`. The user side
stays as it is: a function written at, or named at, a `Code(...)` position is
reified. What changes is the package side. Instead of the compiler building one
public tag union that every translator walks, the compiler folds the checked
body into a type the translator supplies, by calling one well-known method per
construct. The translator's type is its IR, its DSL and its coverage
declaration at once.

Status: design sketch. Nothing here is implemented, and the Roc below is
written against the proposed API, so `roc check` does not accept it today.

---

## 1. The open dimension

`Code(f)` today fixes three things on behalf of every translator
(`src/build/roc/Builtin.roc:21296`):

| Decision | Who makes it today | Consequence for a translator |
|---|---|---|
| The shape of the description | the compiler: `Ir`, `Pattern`, `Lit` (`src/build/roc/Builtin.roc:21639`, `:21526`, `:21511`) | converts `Ir` into its own AST, then emits from that |
| The abstraction level | the compiler: `and` is an `If`, `x?` is a `Match`, interpolation is `Str.concat` | a target that has `AND` recovers it from `If(a, b, Lit(Bool(False)))` |
| Where coverage is checked | the translator, at build time, by walking the tree | twelve refusal arms in `examples/reifying/glsl/Glsl.roc:369-380`, each formatting its own location |

This is the initial encoding of a language: one data type, many consumers. The
alternative is the final encoding (tagless final, in the Haskell literature):
one vocabulary of operations, each consumer supplying their meaning. Both
encodings describe the same body. They differ in who owns the shape, and that
ownership is the dimension the current proposal leaves closed.

| | Initial (today) | Final (this document) |
|---|---|---|
| The description is | a value of `Code.Ir` | a value of the translator's own type `e` |
| A construct reaches the translator as | a tag it matches on | a method `on_<construct>` the compiler calls |
| Unsupported construct | the translator returns `Err` from its walk | `e` lacks the method, or declares it refused: a compile error at the construct |
| When the refusal appears | when the translator runs during `roc build` | during `roc check`, in the editor |
| A new language construct | a new `Ir` tag; every exhaustive translator breaks | a new method name; translators that lack it refuse only programs that use it |
| Lowering `and`, `?`, loops | chosen once by the compiler | each construct has its own method; the translator chooses how to lower it |

---

## 2. Mechanism

### 2.1 The type

`Code` gains a second parameter: the algebra the body folds into.

```roc
Code(fn, e) :: { root : e, defs : List({ name : Str, body : e }) }.{
	root : Code(fn, e) -> e
	defs : Code(fn, e) -> List({ name : Str, body : e })
}

Code.Site : { ty : Code.Ty, region : Code.Region }
```

`Code.Ty` and `Code.Region` stay as they are. Types are data because they are
the stable half of the description: `Ty` is a closed set of shapes the type
system fixes, while `Ir` is where language growth lands.

The user-facing type is unchanged in every signature a user reads, because the
second parameter appears only in the translator's own signatures:

```roc
fragment_330 : Code(Varyings, Uniforms -> Vec4, Glsl.Frag) -> Str
```

### 2.2 The vocabulary

One method per construct, named `on_` followed by the construct. Operators
reuse the well-known method name the surface already dispatches to, so the
method a Roc type writes for `+` (`plus`) pairs with the method an algebra
writes for a reified `+` (`on_plus`). The prefix keeps the two apart, so one
type can be both a DSL a user calls `plus` on and an algebra the compiler calls
`on_plus` on.

| Group | Methods |
|---|---|
| Names | `on_param`, `on_local`, `on_let`, `on_lambda`, `on_call`, `on_constant` |
| Literals | `on_int`, `on_frac`, `on_dec`, `on_bool`, `on_str`, `on_bytes` |
| Arithmetic | `on_plus`, `on_minus`, `on_times`, `on_div_by`, `on_div_trunc_by`, `on_rem_by`, `on_negate` |
| Comparison | `on_is_eq`, `on_is_ne`, `on_is_lt`, `on_is_lte`, `on_is_gt`, `on_is_gte`, `on_not` |
| Logic | `on_and`, `on_or`, `on_if` |
| Data | `on_record`, `on_update`, `on_field`, `on_opt_field`, `on_tuple`, `on_index`, `on_list`, `on_tag` |
| Control | `on_match`, `on_try`, `on_default`, `on_for`, `on_while`, `on_break`, `on_return`, `on_crash` |
| Strings | `on_interpolate` |
| Compiler-derived | `on_derived` |

Every method takes its children, already folded, then a `Code.Site`, and
returns `Try(e, Str)`:

```roc
on_plus : e, e, Code.Site -> Try(e, Str)
on_field : e, Str, Code.Site -> Try(e, Str)
on_let : Str, e, e, Code.Site -> Try(e, Str)
```

An `Err(message)` becomes a compile error at `site.region`. The compiler
attaches the location, so a translator no longer threads it through every
error the way `examples/reifying/glsl/Glsl.roc:390-401` does today.

Patterns are a second sort `p`, fixed by the signature of `on_match`:

```roc
on_match : e, List({ patterns : List(p), guard : [NoGuard, Guard(e)], value : e }), Code.Site -> Try(e, Str)
```

and `p` supplies `on_bind`, `on_anything`, `on_variant`, `on_pat_lit` and the
rest of today's `Pattern` tags as methods of its own.

### 2.3 Refusing a construct

A translator declares a construct it cannot express with an explicit value:

```roc
on_match = Code.refuse("GLSL 330 has no tag union to match on; use `if`")
```

`Code.refuse : Str -> Code.Refused`. When the compiler needs `on_match` and
finds a method of type `Code.Refused`, it reports the message at the `match`.
When it finds no method at all, it reports that the algebra does not describe
the construct, naming both. Either way the report lands on the user's source
line during `roc check`.

### 2.4 The footprint

The compiler does not require an algebra to implement the whole vocabulary. At
each `Code(fn, e)` site it computes the footprint: the set of constructs the
root body and every callee it reaches actually contain. The footprint becomes a
`where` clause on `e`, and only those methods are required.

```
      user body (checked, solved)           translator type e
                 |                                  |
                 v                                  |
   footprint: {param, field, let, times,            |
               plus, call, record}                  |
                 |                                  |
                 v                                  v
   where [e.on_param, e.on_field, ...]  --check-->  methods of e
                 |                                  |
                 v                                  |
   residual program: nested on_* calls,             |
   one per node, each carrying its Site             |
                 |                                  |
                 v                                  |
   compile-time evaluator  ---------------------->  Code(fn, e) constant
```

The residual program is ordinary monomorphic Roc: for `|x| x * 2.0` it is
`Frag.on_lambda(["x"], Frag.on_times(Frag.on_param("x", s1)?, Frag.on_frac(2.0, s2)?, s3)?, s0)`.
The existing checker resolves its dispatch and the existing compile-time
evaluator runs it. The reifier's job shrinks from building a public value to
emitting that program.

### 2.5 Callees

The closed set of definitions stays: every function the root reaches is folded
with the same algebra into `defs`, and a call reaches the translator as
`on_call(callee, args, site)` naming its row. Recursion works because calls are
by name, exactly as today.

---

## 3. Worked sketches

### 3.1 GLSL: the refusals become declarations

Today `examples/reifying/glsl/Glsl.roc:369-380` refuses twelve constructs at
build time, one match arm each. In the fold they are twelve declarations the
checker reads:

```roc
Frag := [
	Input(Str),
	Value({ statements : List(Str), value : Str, kind : Kind }),
].{
	on_param : Str, Code.Site -> Try(Frag, Str)
	on_param = |name, _| Ok(Frag.Input(name))

	on_field : Frag, Str, Code.Site -> Try(Frag, Str)
	on_field = |receiver, name, site| match receiver {
		Input(_) => Frag.input_field(name, site.ty)
		Value(v) => Frag.swizzle(v, name, site.ty)
	}

	on_times : Frag, Frag, Code.Site -> Try(Frag, Str)
	on_times = |a, b, site| Frag.infix("*", a, b, site.ty)

	on_and : Frag, Frag, Code.Site -> Try(Frag, Str)
	on_and = |a, b, site| Frag.infix("&&", a, b, site.ty)

	on_match = Code.refuse("GLSL 330 has no tag union to match on; use `if`")
	on_list = Code.refuse("GLSL 330 has no list; a fixed-lane vector is built from a tuple")
	on_crash = Code.refuse("`crash` cannot run on a GPU")
}
```

The string-keyed operator table of `examples/reifying/glsl/Glsl.roc:483-506`
disappears: each operator is a method the checker resolves, so a misspelled
operator is a compile error in the translator rather than an unreachable
`Unsupported` arm.

### 3.2 SQL: the target keeps the abstraction level it has

```roc
Pred := [Row, Col(Str), Lit(Str), Op(Str, Pred, Pred)].{
	on_param = |_, _| Ok(Pred.Row)
	on_field = |receiver, name, _| match receiver {
		Row => Ok(Pred.Col(name))
		_ => Err("a WHERE clause reads a column of the row, not a field of a value")
	}
	on_and = |a, b, _| Ok(Pred.Op("AND", a, b))
	on_or = |a, b, _| Ok(Pred.Op("OR", a, b))
	on_is_gte = |a, b, _| Ok(Pred.Op(">=", a, b))
	on_if = Code.refuse("a WHERE clause has no `if`; write the condition with `and` and `or`")
}

where : Table(row), Code(row -> Bool, Pred) -> Query(row)
```

Under today's `Ir` this translator receives `If(a, b, Lit(Bool(False)))` for
`a and b` (`roc-reify-design.md:84`) and must pattern-match it back into `AND`.
That recovery is exactly the reconstruction the rest of this code base
forbids its own stages.

### 3.3 The DSL and the reified function become one type

Section 7.1 of `roc-reify-proposal.md` sets a static-dispatch DSL `Sym` against
reification. With the fold they stop competing. A package's `Sym` keeps its
surface methods, gains `on_*` methods, and accepts both spellings:

```roc
Sym := [Col(Str), Lit(I64), Plus(Sym, Sym), Gte(Sym, Sym), And(Sym, Sym)].{
	plus = |a, b| Sym.Plus(a, b)                  # for hand-built terms
	on_plus = |a, b, _| Ok(Sym.Plus(a, b))        # for reified bodies
	on_is_gte = |a, b, _| Ok(Sym.Gte(a, b))       # `>=` returning Sym, which the surface cannot do
	on_and = |a, b, _| Ok(Sym.And(a, b))
}

filter : Rel(row), Code(row -> Bool, Sym) -> Rel(row)
filter_sym : Rel(row), Sym -> Rel(row)
```

The five gaps of section 7.1 (field access, comparisons returning `Bool`, `and`
and `or`, `if` and `match`, reuse) close because the residual program is
generated, not desugared from surface syntax: nothing forces `on_is_gte` to
return `Bool`. Reuse closes because the user's predicate is still an ordinary
function that `expect` calls.

---

## 4. Choosing the abstraction level without a fallback

The compiler makes these lowering choices once today:

| Surface | Today's description | Target that wants the surface form | Cited at |
|---|---|---|---|
| `a and b`, `a or b` | `If` | SQL, Datalog, SMT | `roc-reify-design.md:84` |
| `a != b` | `Unary("not", Binop("is_eq"))` | SQL `<>`, GLSL `!=` | `roc-reify-design.md:79` |
| `x?`, `x ? Tag` | `Match` | a target with exceptions or `Option` | `roc-reify-design.md:99` |
| `x ?? d` | `Match` | SQL `COALESCE` | `roc-reify-design.md:96` |
| `"a${b}c"` | `Str.concat` chain | SQL `format`, JavaScript template | `roc-reify-design.md:34` |
| `for`, `while` | fold with carried `var`s | GLSL, CUDA, C: structured loops | `roc-reify-design.md:200` |
| derived `is_eq` | expanded structural comparisons | SQL row equality | `roc-reify-design.md:457` |

In the fold each row is its own method: `on_and`, `on_is_ne`, `on_try`,
`on_default`, `on_interpolate`, `on_for`. The compiler never chooses a lowering
by checking which methods an algebra has, because that choice would be a
fallback. One construct maps to one method, always.

A translator that wants the lower form writes it, explicitly, with a helper the
builtins ship as ordinary generic Roc:

```roc
Code.Lower.and_as_if : e, e, Code.Site -> Try(e, Str)
	where [e.on_if : e, e, e, Code.Site -> Try(e, Str), e.on_bool : Bool, Code.Site -> Try(e, Str)]

on_and = Code.Lower.and_as_if
```

The lowering stays visible in the translator's source, and the compiler holds
no default.

---

## 5. What the fold answers in the current proposal

| Proposal section | Open problem | The fold's answer |
|---|---|---|
| 7.1, counterweight | a DSL puts its boundary in the type system; reification finds it at build time | the footprint `where` clause puts the boundary back in the type system, per translator |
| 7.5 | refusal diagnostics are the feature | `Code.refuse` messages appear at the construct, in `roc check`, with the location the compiler supplies |
| 7.6 | `Code.Ir` becomes public API forever | the vocabulary grows additively; a new `on_` name breaks no existing translator |
| 13, naming a constant | lists, opaque values and functions have no chosen representation | `on_constant : a, Code.Site -> Try(e, Str)` hands the value itself at its monomorphic type; the translator states what it needs of `a` in its own `where` clause |
| 13, a refusal as a compiler diagnostic | a translator's `Err` reaches the user as whatever the program does with it | a method's `Err` is a compile error at `site.region`, in `roc check`, with no well-known method needed |
| 9.3, 94 prong lists | `code_from_lambda` is listed across the pipeline | unchanged: the site still needs its checked-expression variant |

---

## 6. Costs

| Cost | Why | Mitigation |
|---|---|---|
| Information flows only upward | a fold hands a method its children, not its context; GLSL needs to know it is inside a parameter record | `e` carries what the parent needs (`Frag.Input` above), or `e` is a function of the context, which loses automatic locations for errors raised inside it |
| Whole-body analysis needs data | CSE, dead-binding removal and DBSP circuit optimization read the tree more than once | pick an algebra whose values are data: the stock `Code.Ir` of section 7, or a translator's own closed union |
| A large vocabulary | about 55 methods across two sorts | the footprint requires only the constructs a program uses; a SQL predicate translator needs about ten |
| A second check per site | the footprint `where` clause and the residual program are checked after the user module solves | one check over monomorphic, straight-line code; today the translator walks the same tree at evaluation time |
| Signatures remain API | changing `on_match`'s arguments breaks every translator that implements it | the same obligation as a tag payload today, confined to one method |
| No universal printer | a tool cannot print "the description" of an arbitrary `Code(fn, e)` | the tool folds into `Code.Ir` itself |
| `Site.ty` of a child | a translator that needs an operand's type, as GLSL does at `examples/reifying/glsl/Glsl.roc:268-271`, must keep it in `e` | a stock wrapper `Code.Typed(e)` that pairs every value with its `Ty` |

The first row is the real price. The initial encoding hands a translator the
whole tree and lets it traverse in any order; the final encoding fixes a
bottom-up order and makes every other order a data structure the translator
builds.

---

## 7. Migration: today's design is one algebra

The builtins ship `Code.Ir` as an algebra that implements every `on_` method by
constructing the corresponding tag:

```roc
Ir := [ ... ].{
	on_plus = |a, b, site| Ok(Ir.Binop("plus", a, b, site))
	on_field = |r, name, site| Ok(Ir.Field(r, name, site))
	# one line per construct
}

Code(fn) : Code(fn, Code.Ir)
```

The GLSL example keeps compiling unchanged, and a translator moves to its own
algebra construct by construct. A package author then chooses along the
dimension this document opens:

| Choice | Coverage checked | Traversal | Suits |
|---|---|---|---|
| `Code(fn, Code.Ir)` | at build time, by the translator | any order | optimizers, tools, translators porting from today |
| a closed union of the translator's own | at check time, by the footprint | any order, over the translator's data | a target with a small construct set that still wants a tree |
| a direct algebra | at check time, by the footprint | bottom-up, emitting as it goes | emitters: SQL predicates, GLSL expressions, DSL types |

---

## 8. Fit with the compiler's invariants

| Rule in `AGENTS.md` | How the fold keeps it |
|---|---|
| No fallbacks | one construct maps to one method; the compiler never picks a lowering by method presence (section 4) |
| No heuristics, no reconstruction | the footprint reads construct kinds from the checked body and callees from the dispatch plans the checker stamped; nothing is inferred |
| Solver-mutating rewrites need a declared rule | the footprint check and the residual program are a separate check over new code; they write nothing into the user module's solved graph, so no `RedirectRule` is involved |
| Backends follow explicit ARC only | the residual program is compile-time constant evaluation; no backend sees it |

---

## 9. Open questions

- Typed algebras. A translator would like `Expr(a)`, indexed by the Roc type of
  the node, so `on_plus : Expr(a), Expr(a), Code.Site -> Try(Expr(a), Str)`.
  That requires `Code` to take a type constructor, which Roc has no syntax for.
  The monotype `e` with `Site.ty` covers the need without it.
- Binding representation. Named binders keep the residual program readable and
  match today's `Local(Str, ...)`. Higher-order binders (`on_let : e, (e -> e)`)
  would give hygiene for free but put a function inside the fold, which the
  compile-time evaluator must then run.
- Structural equality (rule 6 of the proposal's section 3). With the translator
  owning `e`, equality and hashing are the translator's derived `is_eq` and
  `to_hash`. Alpha-equivalence holds only for algebras that do not keep names.
- Intrinsics. `examples/reifying/glsl/Glsl.roc:516` recognizes its own
  functions by string (`"Glsl.Vec2.scale"`). An algebra could name its
  intrinsics by symbol, so `on_call` receives a tag the checker verified instead
  of a string the translator compares.
- Refusal granularity. `Code.refuse` refuses a construct everywhere. A refusal
  that depends on a type (`on_plus` at `Dec`) stays a runtime `Err` from the
  method, reported at the site, but not in the footprint check.
