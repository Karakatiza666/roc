# A Shader Translator for roc-ray: the first code-reification POC

Companion to `roc-reify-proposal.md`. That document argues a translator is a
pure compile-time compiler that produces data. This one picks the cheapest case
that proves it, researches what the target platform actually provides, and
sequences the work.

Everything below marked *measured* was run against roc-ray at
`github.com/lukewilliamboswell/roc-ray` (release `0.10.0-rc3`) and the Roc
compiler at `nightly-2026-09-15-fe09c42`.

---

## 1. Why this target

Case 9.1 of the proposal, where the translator's output runs nowhere and the
consumer already exists. roc-ray happens to be the strongest instance of it.

| What a reification POC usually needs | What roc-ray already has |
| --- | --- |
| A consumer for the output | `Draw.Shader.from_source!`, `platform/Draw.roc:591` |
| An output format the compiler can emit | GLSL 330 **text**, not SPIR-V |
| A way to get the output into the binary | Any top-level `Str` is a compile-time constant |
| A running example to convert | `examples/post_process/`, 129 lines |
| A platform on the current compiler | Targets the Zig compiler, nightly-2026-09-07 |
| Host changes | None |

The output is a `Str`. There is no binary format, no descriptor, no FFI, no
serialization contract, and no new build artifact. The diff to roc-ray is zero
lines. You can read the translator's output with your eyes and paste it into any
GLSL validator.

That the format is text rather than SPIR-V is the single biggest reason this is
the first POC and not the third. `roc-reify-proposal.md` §9.1 said SPIR-V;
raylib's API takes GLSL source strings, which is easier.

### What roc-ray provides, measured

```
platform/Draw.roc:591   from_source!  : LoadShaderSource => Try(Shader, [ShaderLoadFailed, ResourceLimit, ..])
platform/Draw.roc:688   LoadShaderSource : { vertex_source : Str, fragment_source : Str }
platform/Draw.roc:625   uniform_f32!  : Shader, Str => Try(F32Uniform, [UniformNotFound, ..])
                        also uniform_i32! vec2! vec3! vec4! color! texture!
platform/Draw.roc:1115  with_shader!  : Frame, Shader, (Frame => Try(a, e)) => Try(a, e)
```

An empty `vertex_source` selects raylib's default vertex stage, which is what a
2D post-processing effect wants. The fragment interface is raylib's, fixed
(`src/graphical_smoke.zig:625`):

```glsl
#version 330
in vec2 fragTexCoord;
in vec4 fragColor;
uniform sampler2D texture0;
out vec4 finalColor;
```

Uniforms are resolved by name once and set per frame, so a translator that
invents uniform names must also report them; see §5.

---

## 2. The target: `examples/post_process`

The example loads `assets/post_process.fs` from disk and drives one `time`
uniform. The whole shader:

```glsl
vec2 uv = fragTexCoord;
float wave = sin(uv.y * 28.0 + time * 2.0) * 0.004;
vec4 color = texture(texture0, vec2(uv.x + wave, uv.y)) * fragColor;
color.rgb *= 0.92 + 0.08 * sin(time + vec3(0.0, 2.1, 4.2));
finalColor = color;
```

Arithmetic, one builtin call, one texture fetch, swizzles, scalar-vector
broadcast. No branches, no loops, no comparisons. Small enough to convert
completely, rich enough that conversion is not trivial.

The POC succeeds when `Shader.from_source!` is fed a string the Roc compiler
computed, the window looks the same, and the `.fs` file is deleted.

---

## 3. Phase 0—the library-only DSL: what today's Roc already reaches

*Measured.* Written, type-checked and run under nightly-2026-09-15. A nominal
`Expr :=` tag union with `from_numeral`, `plus`, `minus`, `times` and `sin`
methods, plus `Vec2 :=` and `Vec4 :=` wrappers carrying swizzle methods.

The shader body, written entirely in real Roc operators:

```roc
shade = |uv, time, frag_color| {
	wave = (uv.y() * 28.0 + time * 2.0).sin() * 0.004
	color = texture("texture0", vec2(uv.x() + wave, uv.y())).times(frag_color)
	dim = 0.92 + Expr.Call("vec3", [0.0, 2.1, 4.2]).plus(time).sin() * 0.08
	vec4(color.rgb() * dim, color.a())
}
```

and the GLSL it printed:

```glsl
void main() { finalColor = vec4(((texture(texture0, vec2((fragTexCoord.x +
  (sin(((fragTexCoord.y * 28) + (time * 2))) * 0.004)), fragTexCoord.y)) *
  fragColor).rgb * (0.92 + (sin((vec3(0, 2.1, 4.2) + time)) * 0.08))),
  (texture(texture0, vec2((fragTexCoord.x + (sin(((fragTexCoord.y * 28) +
  (time * 2))) * 0.004)), fragTexCoord.y)) * fragColor).w); }
```

This is real, it is valid GLSL 330, and it is roughly the right shader.
Phase 0 is worth building for that reason alone: it is a usable shader DSL, it
needs no compiler work, and it is a functioning consumer of the emitter that
Phase 2 reuses unchanged.

It also fails in four specific ways, and each one is the argument for `Code(a)`
stated as a measurement rather than an opinion.

**1. Bindings do not survive.** `color` is bound once in Roc and appears twice
in the output: two texture fetches where the source has one. A DSL builds a
tree, and a Roc `let` leaves no trace in that tree. Sharing is lost, and the
loss is multiplicative, so a shader with four chained bindings can emit an
exponentially larger program. `Code(a)` reifies the block with its bindings
intact, so the translator emits GLSL locals. This is a correctness-of-output
argument, not an ergonomic one, and it is the strongest single reason to build
Phase 1.

**2. `shade` is not a function you can test.** Its type is `Vec2, Expr, Vec4 ->
Vec4` over the DSL's own types. It cannot be called on real floats, so it
cannot be unit-tested, debugged on the CPU, or reused anywhere else. With
`Code(a)` the same source is `{ uv : Vec2, time : F32 } -> Vec4`, an ordinary
Roc function that an `expect` can call.

**3. Comparison and control flow are closed.** *Previously measured:* `>=`,
`<`, `==` are hard-wired to `Bool` and take no method hook; `and`/`or` are
keywords; `if` and `match` need a real `Bool`. A DSL predicate must be spelled
`a.gte(b).both(c)`, in invented names because `and` is a keyword, and a
conditional must be spelled `mix(a, b, step(x, y))`.
post_process needs none of these, which is exactly why it is the POC—but a
second shader will.

**4. Literals render wrong.** `28.0` came out as `28` because `F32.to_str`
drops the fraction. Harmless in GLSL, which promotes `int` to `float`, and a
trap in any target that does not.

---

## 4. Phase 1—the compiler change, scoped to this POC

The whole language proposal is `Code(a)`, `from_code`, and `Code.Ir`. The
POC needs a deliberately small slice of it.

### Where it hooks in

Roc already does everything this needs except the reification itself.

| Mechanism | Where | What it gives the POC |
| --- | --- | --- |
| Literal conversion hooks | `src/check/Check.zig:1310`, `src/check/canonical_type_keys.zig:741` | The precedent: a type declares `from_quote`, and the checker inserts a call at every literal of that type. `from_code` is the same shape with a function in place of a literal. |
| Hoisted-root selection | `src/check/hoist_roots.zig` | Decides which expressions are evaluated at check time and whether the result is a data constant. A reified `Str` is a `data_constant` root. |
| Compile-time evaluation | `src/eval/compile_time_finalization.zig`, `src/eval/interpreter.zig` | Runs the translator. The translator is pure Roc, so it runs on the existing interpreter with no new machinery. |
| Const store | `src/eval/const_store_writer.zig` | Puts the resulting `Str` in the binary. Already how any computed top-level constant works. |

So the new work is one thing: given a CIR expression in a position typed
`Code(a -> b)`, build a Roc value describing it.

### The IR, minimally

`src/canonicalize/Expression.zig` has 57 `e_*` variants. A first `Code.Ir`
should expose far fewer, and reject the rest with a diagnostic naming the
construct. For post_process:

| CIR variant | `Code.Ir` |
| --- | --- |
| `e_lookup_local` on a lambda parameter | `Param(Str)` |
| `e_block` with `let` bindings | `Let(Str, Ir, Ir)` |
| `e_binop` | `Binop(Str, Ir, Ir)` |
| `e_call` / `e_dispatch_call` to a known builtin | `Builtin(Str, List(Ir))` |
| `e_field_access` | `Field(Ir, Str)` |
| `e_record` | `Record(List((Str, Ir)))` |
| `e_typed_frac`, `e_num` | `LitF32(F32)`, `LitI32(I32)` |
| `e_if` | `If(Ir, Ir, Ir)`—defer past the POC |
| everything else | rejected by name |

Each node carries its solved type, because a shader translator must distinguish
`F32` from `Vec2` from `Dec` to emit anything at all.

### Four decisions the POC forces

**Reification happens after solving.** Types must be concrete; before solving
`0.8` is an open numeric literal. The reifier runs in the checker once
solving is done, and describes each site at the types its `Code(f)` fixes
(`roc-reify-design.md` §9).

**A reference must be followed.** `Glsl.fragment_330(wobble)` passes a
*name*, not a lambda literal. The reifier has to resolve the top-level
definition and reify its body, or the feature only works on inline lambdas,
which nobody wants. This is the one genuinely new piece of machinery.

**`Code` is closed.** No captures. `wobble` refers only to its parameters and
to builtins. Enforcing this is a check over the reified body, and the
diagnostic should name the captured binding.

**`Dec` will bite immediately.** An unsuffixed `0.8` is a 128-bit fixed-point
`Dec`, which no GPU has. In `{ uv : Vec2, time : F32 } -> Vec4` inference
pushes `F32` inward and most literals resolve correctly; the ones that do not
must produce an error that says "annotate this as `F32`", not a type name
nobody typed. This is proposal §12's open question, met on the first example.

---

## 5. Phase 2—swap the front end, keep the emitter

The Phase 0 emitter takes `Expr` and returns `Str`. Phase 2 replaces its input
with `Code.Ir` and changes nothing else. That is the point of building Phase 0
first: the GLSL knowledge, the type mapping, the interface generation and the
tests all survive, and the only thing under test in Phase 2 is the reifier.

Interface generation is the one new piece. The argument record becomes the
shader's inputs:

| Roc | GLSL |
| --- | --- |
| `uv : Vec2` in the argument record | `in vec2 uv;` |
| `time : F32` | `uniform float time;` |
| `scene : Glsl.Sampler` | `uniform sampler2D scene;` |
| return type `Vec4` | `out vec4 finalColor;` |
| `F32`, `Vec2`, `Vec3`, `Vec4`, `I32`, `Bool` | `float vec2 vec3 vec4 int bool` |
| `Dec`, `U64`, `Str`, `List`, tag unions, functions | rejected |

Distinguishing an interpolated `in` from a per-draw `uniform` needs a marker;
the cheapest is a wrapper type, `Glsl.Varying(Vec2)`, rather than a naming
convention.

Uniform names then matter to the app, which resolves them with
`shader.uniform_f32!("time")`. The translator should emit the name list
alongside the source so a rename in the Roc function does not become a runtime
`UniformNotFound`:

```roc
Glsl.Fragment : { source : Str, uniforms : List({ name : Str, kind : Glsl.Kind }) }
```

---

## 6. Sequencing

| # | Step | Compiler change | Delivers |
| --- | --- | --- | --- |
| 0 | DSL + GLSL emitter + type mapping, as a Roc package | none | A usable shader DSL; the emitter Phase 2 reuses |
| 1 | Convert `examples/post_process` to it, delete the `.fs` | none | Proof the platform side is a non-issue |
| 2 | `Code(a)` as a builtin opaque type; reject it everywhere except a `from_code` argument | small | The type exists |
| 3 | Reification of the §4 subset at checking finalization, including following a top-level reference | the real work | `Code.Ir` values |
| 4 | `from_code` dispatch, mirroring `from_quote` | small | The translator runs |
| 5 | Repoint the emitter at `Code.Ir` | none | The same window, from a testable Roc function |
| 6 | `expect` on the shader function; `if` and comparisons | medium | A second, harder shader |

Steps 0 and 1 are worth doing whatever happens to the language proposal.
Step 3 is where the design is actually tested, and steps 0-2 exist to make
step 3 cheap to evaluate and cheap to throw away.

---

## 7. What would sink it

- **`Dec` defaulting produces a bad first experience**, and the fix may be a
  numeric-defaulting override in reified contexts, which is a real language
  change rather than a small one.
- **Compile-time cost lands on editor latency**, since `from_code` runs inside
  `roc check`. A shader is small; the concern is real for a large translator and
  should be measured at step 5, not assumed away.
- **The subset is a cliff, not a slope.** A rejected construct must be
  diagnosed by name with a suggested alternative, or the feature will feel like
  a language that silently isn't Roc.
