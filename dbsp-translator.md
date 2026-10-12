# The DBSP Translator

A worked example of the two proposals in this directory: a translator that
compiles incremental-computation expressions, and the platform extension that
runs them. One artifact, both halves.

- Language feature used: `roc-reify-proposal.md`
- Composition mechanism used: `platform-composition-proposal.md`
- Engine: a set of Rust crates that build a library binary which ingests the DBSP
  JSON IR, constructs a circuit from it, and runs that circuit over ingress
  batches.

> `~/dev/feldera/feldera-roc-backend` is an abandoned experiment that integrated
> Roc and DBSP the other way round: DBSP as the platform, circuit construction as
> an effect, operator lambdas as boxed closures called per record. It is cited
> here for measured evidence about costs, never as an architecture to preserve.

---

## 1. Frame

Five things that decide everything below.

### 1.1 The target is an application's own state, not a pipeline

The thing being built is something an ordinary Roc program uses to maintain
derived state: effective permissions from an ACL graph, a rendered UI model from
a document, spatial and relational queries over a game world, diagnostics from a
compilation unit. Roc owns the base state and the engine maintains views over it.

Streaming connectors that an application configures are possible and expected.
They are not the shape the design is fitted to. A server-shaped deployment, where
the engine owns ingress and the filesystem, is a different product and imposes
different costs; nothing here is chosen for it.

The practical consequence is that batches are small and frequent. A tick's delta
is tens to hundreds of rows, against the thousands to millions the engine's own
benchmarks assume. Section 5.4.

### 1.2 The engine ingests JSON IR, and the translator produces it

The IR is fully featured: it carries operator topology and the expressions
inside operators. So the translator has a target for both halves of a Roc query,
and neither half needs an execution engine written here.

| Half | Source in Roc | Target |
|---|---|---|
| Operator topology | `Rel.map`, `Rel.join`, … building a value | IR operator nodes |
| Expressions inside operators | Lambda bodies, reified to `Code.Ir` | IR expression nodes |

Earlier drafts of this document proposed writing a vectorized expression VM, an
instruction set, and a Cranelift backend behind it. All of that is the engine's,
maintained by the engine's team, measured once for every frontend. The
translator is a translation, which is the shape that LINQ providers, Quill and
Nx's `defn` already have.

### 1.3 The circuit is a compile-time constant

The IR is JSON, but nothing serializes it at run time. `Rel.map` and friends are
pure Roc functions that build a value; rendering that value to JSON is pure Roc;
and Roc evaluates every top-level binding at compile time. So

```roc
circuit_json : Str
```

is computed during `roc build` and lands in `.rodata`. The extension reads it at
startup. One string, one entry point.

This is what separates the design from the abandoned experiment, and the
separation survives every other change. There, circuit construction was an
effect: 67 hosted builder methods issued at process start. That made the circuit
a run-time value, forced `main!` to carry `Try({}, [DbspBuildErr(Str)])`, and
made operator lambdas run-time function values, which is the whole reason boxed
`RocClosure` existed. It also put 67 methods in a platform's `exposes`, which is
the scale that already hit the compiler's per-platform method ceiling.

An operator-per-entrypoint library API is the same shape and costs the same
things. With a fully featured IR it also buys nothing, because there is nothing
left for an operator-level API to express.

### 1.4 Nothing interprets Roc at run time

Roc's interpreter (`src/eval`, `src/interpreter_shim`) exists for compile-time
evaluation. Running it per row inside an operator would be strictly worse than a
compiled closure over a C ABI, which the abandoned experiment already had at
roughly 3 to 5 ns per record.

Nor does anything interpret `Code.Ir` at run time. `Code.Ir` is consumed
entirely at compile time, by the translator, and does not exist in the built
artifact.

### 1.5 The integration is data, not FFI

The circuit crosses the boundary as a string constant. Records cross it as
batches in the engine's own ingress format. No Roc function pointer, no boxed
closure and no schema descriptor is passed at any call site. The FFI surface is
the four engine methods in section 4 plus the allocator and panic shims.

---

## 2. What the translator does

Take `orders.map(|o| o.amount * 0.8)`.

### 2.1 What reification produces

Reification happens after type checking and monomorphization, so the compiler
has concrete types, a purity proof and a closed body:

```
Lambda {
  params: [ { name: "o", type: Record[ amount: Money, qty: I64, … ] } ],
  ret:    Money,
  body:   Binop("mul", Field(Param "o", "amount"), Lit(Money, 0.8)),
}
```

Four properties matter downstream:

- Closed. There is no environment pointer, so nothing needs a stable heap
  representation for a closure environment. A compile-time constant folds
  into a `Lit`, whether a template argument fixed at the call or a top-level
  value written as data (`roc-reify-design.md` §2 and §12,
  `src/check/code_reifier.zig:1023`), so a query can be a template over its
  threshold. A value computed at run time is still refused as a capture, and
  so is a top-level value that has to be computed.
- Typed and monomorphic. Record layout is derivable from the IR, so it is
  computed by one party instead of agreed between two. The `RecordSchema` the
  abandoned experiment passed at every call site stops being a contract.
- Explicit about totality. Whether the body can crash is a property of the IR,
  which is what lets the translator enforce a policy. Section 7.
- Explicit about its field set. The body names exactly the fields it reads, which
  is what lets ingress carry a projection rather than a record. Section 5.2.

### 2.2 The mapping

The translator's engineering content is one function from `Code.Ir` to IR
expression nodes. Most of it is mechanical.

| `Code.Ir` | Engine IR |
|---|---|
| `Lit` | Literal, once the type maps |
| `Param`, `Local`, `Field`, `Index` | Column reference or field access |
| `Binop`, `Unary` | Operator node, once the type and the overflow policy map |
| `If` | Conditional, or a mask and a select, whichever the IR offers |
| `Let` | Let-binding if the IR has one, otherwise substitute |
| `MakeRecord`, `MakeTuple` | Row construction |
| `Call` on a known builtin | Named function |
| `Call` on anything else | Section 2.3 |
| `Lambda` nested inside a body | Section 2.3 |
| `Derived(...)` | Section 2.3 |
| `Crash` | No counterpart. Section 7 |

The rows that map are not where the work is. The work is the type mapping and the
overflow policy underneath three of them, and section 2.3 for the rest.

### 2.3 Where lowering stops

Three kinds of node have no IR counterpart: a call the translator does not know,
a nested lambda, and the `Derived` node the reifier emits for a derived method
it keeps symbolic (`parser_for`, `encoder_for`, `map`, `map!`). A scalar UDF
such as base64 is the ordinary example.

Two possible fates, and which one exists is the first thing to settle against the
IR:

| Fate | Requires |
|---|---|
| An extern node naming a symbol the runtime resolves | The IR has such a node, and the runtime has a registration path for it |
| Refusal, with a diagnostic naming the node and the reason | Nothing |

If the extern node exists, the exported symbol is compiled Roc reached by one
indirect call, and the UDF question disappears: a UDF is a pure Roc function, and
either it lowers or it is a symbol. No separate UDF language, no per-UDF ABI.

If it does not, the translator refuses, and the subset boundary becomes visible
to every user who writes an ordinary-looking lambda. Then diagnostics are the
project, not an afterthought, and the refusal has to say which node stopped it,
where in the source it came from, and what to write instead.

### 2.4 Multi-lambda operators

An aggregate carries four functions (key, init, step, finalize). Each is its own
`Code` value and each lowers independently. `Rel.fix` is different in kind: it
takes an ordinary `Rel(a) -> Rel(a)`, runs at compile time against a placeholder
node, and returns a graph, so whether it works is a question about the IR's
support for nested or recursive circuits, not about the translator.

> Graph-shaping functions are ordinary Roc. Row functions are `Code`. Keeping
> those apart is the whole discipline of the API.

---

## 3. One artifact, both halves

### 3.1 Why it can be one artifact

A platform, and under the composition proposal an extension, `exposes` type
modules to the application. Those modules are ordinary pure Roc. So a single
distributable carries the pure translator and the native runtime together:

```roc
# main.roc
extension "dbsp-runtime"
	exposes [Rel, IndexedRel, Circuit, Engine]
	provides {
		"roc__dbsp_start": start!,
		"roc__dbsp_push":  push!,
		"roc__dbsp_step":  step!,
		"roc__dbsp_take":  take!,
	}
	targets : {
		inputs_dir: "targets/",
		x64linux:  { inputs: ["libdbsp_runtime.a"] },
		arm64mac:  { inputs: ["libdbsp_runtime.a"] },
	}
```

| Module | Nature | Role |
|---|---|---|
| `Rel`, `IndexedRel` | Pure Roc | The combinator API. Builds the circuit value |
| `Circuit` | Pure Roc | The IR as a Roc type, the `Code.Ir` lowering, and the render to JSON. This is the translator |
| `Engine` | Hosted, `=>` | Four effectful methods over the native runtime |
| `libdbsp_runtime.a` | Rust | The crates: IR ingest, circuit construction, scheduling, storage |

The Roc-side circuit type is an internal detail of `Circuit`, not a contract. It
mirrors the engine's IR schema closely enough that rendering is a fold, and it
exists only so the combinators have something to return. The contract is the JSON
schema, and it belongs to the engine. Section 7.

### 3.2 Bootstrapping before composition exists

The same source tree builds as a root platform by swapping the header and adding
a handful of ordinary effects:

```roc
platform "dbsp-cli"
	requires { main! : List(Str) => Try({}, [Exit(I8), ..]) }
	exposes [Rel, IndexedRel, Circuit, Engine, Stdout, File]
	provides { "roc__main_for_host": main! }
	targets : {
		inputs_dir: "targets/",
		x64linux: { inputs: ["crt1.o", "host.o", app] },
	}
```

That version needs no composition proposal. Migrating later is deleting
`requires`, deleting the `main` entry from `provides`, and dropping `Stdout` and
`File` in favour of whatever root the app picks.

So composition is what makes this pleasant, not what makes it possible.

---

## 4. The API

```roc
Rel(a) :: Node.{
	# stateless row operators
	map      : Rel(a), Code(a -> b) -> Rel(b)
	filter   : Rel(a), Code(a -> Bool) -> Rel(a)
	flat_map : Rel(a), Code(a -> List(b)) -> Rel(b)

	# Z-set algebra
	plus     : Rel(a), Rel(a) -> Rel(a)
	negate   : Rel(a) -> Rel(a)
	distinct : Rel(a) -> Rel(a)

	# time
	delay         : Rel(a) -> Rel(a)
	integrate     : Rel(a) -> Rel(a)
	differentiate : Rel(a) -> Rel(a)

	# indexing. DBSP stores OrdZSet, so a key needs a total order, not merely a
	# hash. Roc's own comparison methods say exactly that.
	key_by : Rel(a), Code(a -> k) -> IndexedRel(k, a)
		where [
			k.is_eq : k, k -> Bool,
			k.order_relative_to : k, k -> [Before, Same, After],
		]

	# feedback. An ordinary Roc function: runs at compile time, returns a graph.
	fix : (Rel(a) -> Rel(a)) -> Rel(a)
}

IndexedRel(k, v) :: Node.{
	join      : IndexedRel(k, v), IndexedRel(k, w), Code((k, v, w) -> o) -> Rel(o)
	antijoin  : IndexedRel(k, v), IndexedRel(k, w) -> IndexedRel(k, v)
	asof_join : IndexedRel(k, v), IndexedRel(k, w), Code(v -> t), Code(w -> t) -> Rel(o)
	aggregate : IndexedRel(k, v), Aggregator(v, acc, o) -> IndexedRel(k, o)
	values    : IndexedRel(k, v) -> Rel(v)
	get       : IndexedRel(k, v), k -> List(v)
}

# `step` takes the Z-set weight, because retraction is not deletion.
Aggregator(v, acc, o) : {
	init : Code({} -> acc),
	step : Code((acc, v, I64) -> acc),
	done : Code(acc -> o),
}
```

`get` is on the read path, not the graph path, and section 5.1 is why it is here.

### 4.1 The carrier is a derived codec over the engine's format

The abandoned experiment passed a `RecordSchema` at every call site because Roc
erased the record type at the platform boundary. Here the type is present, so the
layout is derivable.

The format itself is not a free choice: the engine's crates define the ingress
batch format and the layout its traces store. What Roc contributes is that
deriving an encoder for that format is an ordinary use of the codec protocol,
which is genuinely format-agnostic (`Encoding.HttpHeader` exists to prove JSON is
not special-cased).

```roc
# The engine's batch format as an ordinary Roc encoding.
# Every record type derives its codec. Nothing is passed at the call site.
Encoding.DbspRow.to_bytes : a -> List(U8)
	where [a.Encoding.DbspRow.Encodable([])]
```

Key order preservation becomes a property the format guarantees rather than one a
descriptor builder reproduces. Scalar fields memcpy; fields carrying pointers
(`Str`, `List`) encode.

Two questions stay open. Who opts a record into the boundary codec: a nominal
declaring the method, or a use-site `where` constraint that a bare record meets
structurally. And whether the package's expansion of `Derived("encoder_for")`
and its boundary codec can be one walk with two callers.

### 4.2 An application

```roc
app [main!] {
	pf:   platform  "…/game-host.tar.zst",
	dbsp: extension "…/dbsp-runtime.tar.zst",
}

import pf.Frame
import dbsp.Rel exposing [Rel]
import dbsp.Circuit
import dbsp.Engine

Entity : { id : I64, faction : I32, cell : I64, hp : I32 }
Faction : { id : I32, hostile_to : I32 }

# Ordinary Roc. Testable here, reified at the call site below.
alive : Entity -> Bool
alive = |e| e.hp > 0

expect alive({ id: 1, faction: 2, cell: 9, hp: 30 })

entities : Rel(Entity)
entities = Rel.input("entities")

factions : Rel(Faction)
factions = Rel.input("factions")

# Hostile pairs sharing a grid cell: recomputed incrementally, per tick.
threats : Rel({ cell : I64, attacker : I64, target : I64 })
threats =
	entities
		.filter(alive)
		.key_by(|e| e.faction)
		.join(factions.key_by(|f| f.id), |_k, e, f| { e, hostile: f.hostile_to })
		.key_by(|r| r.e.cell)
		.join(
			entities.filter(alive).key_by(|e| e.cell),
			|cell, a, t| { cell, attacker: a.e.id, target: t.id },
		)

# A top-level value, so Roc renders it to JSON at build time.
circuit_json : Str
circuit_json = Circuit.render(Circuit.outputs([("threats", threats)]))

main! = |_args| {
	engine = Engine.start!(circuit_json)?

	Frame.loop!(|world| {
		engine.push!("entities", world.entity_deltas)?
		engine.step!()?
		world.with_threats(engine.take!("threats")?)
	})
}
```

No `BuilderHandle`, no `main! : {} => Try({}, [DbspBuildErr(Str)])`, no
`Box((a -> b))` in any signature. Circuit construction stops being an effect;
only driving the engine is one. And the engine never owns the filesystem, because
the records come from `pf`.

---

## 5. The boundary

With the engine executing both halves, the boundary is where this design's own
costs live.

### 5.1 Egress is the hot path

A pipeline pushes data in and writes to sinks. An application reads derived state
continuously, often several times per tick, so the read side carries the traffic.
It needs two shapes:

| Shape | For | Needs |
|---|---|---|
| Delta iterator over a view | Reacting to what changed | `take!`, already in the API |
| Indexed point lookup | "Threats in this cell", asked per entity | `IndexedRel.get`, and the key ordering the format guarantees |

The second is the one the engine's own API is least likely to prioritize, and the
one an application asks for most. It is also the payoff for keys being ordered
rather than hashed.

### 5.2 Ingress is a projection, not a record

The reified lambdas name exactly the fields the circuit reads, so the translator
computes the referenced field set and the ingress row carries that, not the
whole entity. `Entity` above is four fields and all four are read; a real entity
is forty, of which the circuit reads four.

This is reification paying for something other than expression lowering, and it
matters more than the expression half, because the boundary runs every tick and
scales with the fields touched.

### 5.3 Ownership inverts, and double storage is the price

Gameplay code mutates base state outside the circuit, so Roc stays authoritative
and pushes deltas; the engine holds derived state and indexes. The columns the
circuit reads therefore exist twice. Narrowing ingress to the referenced field set
is what keeps that acceptable, and pushing deltas rather than snapshots is what
keeps the boundary cost proportional to change, which is the same cost model the
engine is built on.

### 5.4 Batch size is the open measurement

The engine's cost model assumes batches where per-step work amortizes. An
application's tick is tens to hundreds of rows. What has to be measured before
anything else is built:

| Question | Why it decides things |
|---|---|
| Fixed cost of one `step!` at a 50-row delta | If scheduling, trace maintenance and merge bookkeeping dominate, the engine is the wrong tool at tick scale regardless of how good the IR is |
| Cost of `take!` and a point lookup at that scale | Section 5.1 says this runs more often than `step!` |
| Whether batching several ticks is acceptable | Trades latency for amortization, and some derived state tolerates a frame of lag |

The abandoned experiment's measured failure was per-record FFI at analytics
scale. That is not evidence about 50 rows a tick, in either direction. This is a
new measurement and it is step 1 of section 8.

---

## 6. When none of this is needed

Worth knowing before building any of it.

Z-sets are maps from values to integers. Traces are ordered collections of them.
`map`, `filter`, `join`, `distinct`, `aggregate`, `delay`, `integrate` and `fix`
are algorithms over ordered maps, all writable in pure Roc on `Dict` and `List`,
with no FFI, no extension and no platform involvement.

And the corollary:

> If the executor is Roc, reification is unnecessary. `Rel.map` can take an ordinary
> `a -> b` and call it. No `Code`, no IR, no JSON.

Reification earns its keep exactly when the consumer is not Roc.

What a pure Roc engine gives up is real: spill-to-disk storage, a worker pool, and
constant factors. For an application maintaining derived state, thousands to
millions of records, the trade may well be right, and section 5.4 is what decides
it. For billions it is obviously wrong.

Because both share the `Rel` API, the pure engine is also the portable reference
implementation and the semantics oracle for the native one. Same source, same
types, same tests. That is worth having even after the native path works, because
the semantic mismatches in section 7 are exactly the kind of thing a differential
test finds.

---

## 7. Hard parts

Ordered by how early they have to be answered.

**Small-batch overhead.** Section 5.4. If a 50-row `step!` costs more than
recomputing the view in pure Roc, section 6 is the answer and the rest of this
document is not built. Measure first.

**Whether the IR has an escape hatch.** Section 2.3. With one, the subset
boundary is a performance cliff. Without one, it is a wall, and every Roc feature
the IR lacks becomes a refusal an application author has to work around.

**Schema ownership and versioning.** The Roc translator emits JSON against a
schema the engine defines and continues to develop. The translator should emit a
version tag the runtime validates at `start!`, because the failure mode
otherwise is a constant built against one node set handed to a runtime expecting
another, discovered at run time in an application that shipped.

**Crash semantics.** Roc's `+` crashes on overflow and pure functions are not
total. The IR presumably follows SQL, where overflow and division by zero
produce NULL or an error per a runtime flag. Two defined semantics have to be
mapped, and the mapping is not free: reified expressions written against
`plus_try` and friends are a daily ergonomic cost when the code in question is
gameplay logic written by people who expect `+` to work. Decide early whether
the translator refuses bare arithmetic with a good diagnostic or the `Rel` API
steers the types so it cannot arise.

**Nullability.** The IR has nullable columns and three-valued logic; Roc has
total types and `Try`. Whether a nullable column surfaces in Roc as an optional
tag, as `Try`, or not at all is a type-mapping decision that shows up in every
record type an application declares.

**DECIMAL.** Roc's `Dec` is fixed 128-bit fixed point scaled by 10^18, which is
not `DECIMAL(p,s)`. The answer is a nominal type with its own `from_numeral`,
which is what Roc's literal hooks are for, but it means reified code does not
use bare `Dec`.

**Recursive and nested circuits.** `Rel.fix` builds its body at compile time
against a placeholder node. Whether that renders is a question about the IR's
support for nested scopes, and it is the most likely place a flat graph value
needs a real extension rather than a translation.

**The allocator.** The engine ships mimalloc; the root platform provides
`roc_alloc` and `roc_dealloc`. One process, two allocators with different
ownership stories. Under a frame deadline this is a latency question, not a
throughput one, so it has to be decided rather than discovered at link time.

**Compiler scale limits are not fixed by this.** Emitting one string constant and
exposing four methods relieves the app-side import ceiling that the abandoned
experiment's 67-method `Builder` and 2,600-line runtime library hit. It does
nothing for the cached-artifact panic, the import-visibility collapse in large
method blocks, or the crash on an unqualified cross-module reference.

### 7.1 What survives from the abandoned experiment

Much less than before, because the engine crates now cover what that code was
reimplementing.

| Piece | Lines | Under this design |
|---|---|---|
| `direct_codec.rs` + `dyn_codec.rs`, memcomparable encode and decode | 4,259 | Reference for the Roc-side codec, if the engine's batch format differs |
| `string_abi.rs`, `array_abi.rs` | 451 | Reuse for extern-call arguments, if 2.3 has an escape hatch |
| `roc_platform_abi.rs`, `hosted_fns.rs` | 3,192 | Keep the alloc and panic shims. Delete the vtable dispatch and boxed `RocClosure` |
| `abi_types.rs`, `builder.rs`, `catalog.rs`, `host_main.rs`, `connectors_*.rs` | 9,877 | Superseded by the engine crates |
| `Builder.roc` (67 methods), `SqlRuntime*.roc` | 3,372 | Delete. The first becomes a constant, the second becomes engine builtins |

---

## 8. Sequencing

0. A pure Roc engine. Section 6. Complete, portable, needs nothing from anyone,
   and it becomes the reference implementation and semantics oracle for
   everything below.
1. Measure the engine at tick scale, with no Roc involved. Hand-write JSON IR for
   one small circuit, drive the library binary from Rust, and measure `step!`,
   `take!` and a point lookup at 50 and 500 row deltas against recomputing the
   same view. Section 5.4 decides whether the rest is worth building.
2. Settle the IR questions. The escape hatch (2.3), the overflow policy (7), the
   nullability mapping (7), and whether nested circuits render (7). These are
   reading and asking, not building, and they bound what the translator can promise.
3. One artifact as a root platform, circuit as a constant, no lambdas. `Rel` over
   a restricted expression algebra, `circuit_json` as a top-level value, the
   `platform` header of 3.2, the runtime reading the constant at startup. End to
   end with today's compiler and no language change, with predicates that read
   like `p.hp().gt(0).and(p.faction().eq(f))`.
4. Measure the ergonomic gap. Write the real queries against that algebra. The
   reification proposal is worth exactly what this step says and no more.
5. Add `Code` and `Code.Ir`. Lambdas become ordinary Roc. The only step that
   touches the Roc compiler.
6. Lower `Code.Ir` to IR expressions, with the projection fast path and either the
   escape hatch or a refusal diagnostic for everything in 2.3.
7. Narrow ingress to the referenced field set. Section 5.2. Separable from 6 and
   worth more at tick scale.
8. Switch the header to `extension` once composition lands, and drop the
   ordinary-effects modules in favour of a real root platform.

Steps 1 and 4 are measurements, step 2 is a conversation with the engine, step 5
needs the reification proposal, step 8 needs the composition proposal, and steps
0 through 4 need neither proposal.
