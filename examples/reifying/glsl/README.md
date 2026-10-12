# A GLSL fragment-shader translator

A translator is a compiler written in ordinary Roc that runs during `roc build`.
This one takes the compiler's description of a pure Roc function and returns
GLSL 330 that raylib accepts.

| File | What it is |
| --- | --- |
| `Glsl.roc` | The translator. A reified function in, shader source and interface out. |
| `Interp.roc` | The same `Code.Ir`, evaluated on the CPU. |
| `main.roc` | The shader, written as a Roc function, and what the translator makes of it. |
| `expected_output.glsl` | What the translator emits for it. |

It is the shader `roc-ray/examples/post_process` loads from
`assets/post_process.fs`, written in Roc instead.

The same shader written as a library DSL over static dispatch, with no
reification, is in [`../shaders-without-reifying/`](../shaders-without-reifying/).
The two files define `post_process` under the same name and the same types;
reading them side by side is the shortest statement of what the feature buys.

## Naming a function is what reifies it

```roc
post_process : Varyings, Uniforms -> Glsl.Vec4
post_process = |frag, settings| ...

Glsl.fragment_330(post_process)
```

`fragment_330` takes a `Code(f)`, so `post_process` is checked against the
function type inside it rather than against `Code` itself. The compiler then
describes `post_process` and hands the description over; `Code.ir` opens it.
The shader is compiled during the build, not on the way to the first frame.

## The interface is the two parameter records

The first parameter holds the varyings the vertex stage interpolates, the
second the uniforms the application writes. Which record a field is in is what
makes it an `in` or a `uniform`, so the distinction is a type-level fact rather
than a naming rule:

| Roc | GLSL |
| --- | --- |
| `fragTexCoord : Glsl.Vec2`, in the first record | `in vec2 fragTexCoord;` |
| `time : F32`, in the second | `uniform float time;` |
| `texture0 : Glsl.Sampler`, in the second | `uniform sampler2D texture0;` |
| return type `Glsl.Vec4` | `out vec4 finalColor;` |

The field names are raylib's, because raylib's default vertex shader supplies
`fragTexCoord` and `fragColor` under those names and binds the render texture
to `texture0`. `Glsl.Fragment` reports every binding, so renaming one fails the
build instead of failing the first `Draw.Shader.uniform_f32!` call.

## What `Let` buys

Each Roc binding becomes one GLSL local. `color` is read four times and `pulse`
three, and each is computed once:

```glsl
vec4 color = (texture(texture0, shifted) * fragColor);
vec3 pulse = ((vec3(sin(time), sin((time + 2.1)), sin((time + 4.2))) * 0.08) + 0.92);
finalColor = vec4((color.r * pulse.x), (color.g * pulse.y), (color.b * pulse.z), color.a);
```

`examples/reifying/shaders-without-reifying/` writes the same shader as a
library DSL and emits the whole texture fetch four times, because a Roc `let`
leaves no trace in a tree built by evaluation. `Code.Ir.Let` is the node that
keeps it.

## A refusal names where to look

Every `Code.Ir` node carries the region the checker solved it at, so a shader
the translator will not compile is reported against the line that has to change:

```
main:132:2: a fragment shader must return Vec4; this one returns float
```

## Two ways to run a shader on the CPU

Calling the function is free, and it is the point of `Code(a)`: `post_process`
is ordinary Roc, so an `expect` runs it on real numbers. `Glsl.Sampler` holds
the function that samples it, so a test supplies whatever texture it wants.

`Interp.roc` is the other one. It evaluates `Code.Ir` directly, which is not a
duplicate of calling the function: it checks that the description and the
language it came from agree. `main.roc` runs the reified `wave` both ways and
compares, which is the differential test that otherwise takes looking at
pixels. It is also the software fallback for a machine with no GPU, which is
what headless CI is.

## The tradeoff, plainly

At the size of one shader the DSL looks five times cheaper: 420 lines of code
here against the 77 it spends on its `Expr` library. That ratio is an artifact
of the small demo. Nearly everything written here is fixed cost, paid
once for the target, while the shaders-without-reifying DSL pays per construct and pays twice,
once in its own source and again in the spelling each construct forces on the shader
author. Filled out to a working shading language the two cost about the same to
write, and by then the translator is the better tool for the job -
turning an expression into a target representation: it reads the whole of
Roc, keeps the bindings, keeps the types the checker solved, and keeps the
shader a function. The accounting, in three parts.

Most of the gap is coverage the demo never reaches. Strip `render` to the node
kinds this one shader uses, trim the builtin table from 34 names to the 2 it
calls, and the translator is 282 lines and still passes all five expects. Drop
source regions and interface derivation on top of that, which is what the DSL
has, and it is 244 lines emitting the same shader byte for byte. Two of the five
expects die there, and neither is a test the DSL could have written.

The rest is the seam between two languages. The DSL has one language in it:
`Expr.Call("sin", [x])` names GLSL directly, so there is nothing to map. The
translator has Roc on one side and GLSL on the other, and `operator`,
`kind_for`, `builtin_name` and `broadcast` are all that seam. `broadcast` exists
only because Roc's `*` wants both operands to have the same type, so a vector
times a scalar has to be spelled `scale`.

The two sides then grow differently, which matters more than today's ratio:

| | Grows by |
| --- | --- |
| This translator | a table entry per GLSL function, one line per GLSL type, and a Roc method that computes the function where Roc has none of its own. `render` does not grow at all: its 24 arms are exactly the 24 variants of `Code.Ir`, so the input language is already covered in full |
| An `Expr` DSL | a method per function, a method per lane per vector type, a combinator per control-flow form, and a spelling the shader author has to learn for each |

Add the sixty-odd functions a working shading library needs and both sides grow
by roughly a line each, so the line counts converge. The difference is that the
translator's line is a table entry the shader author never sees, while the DSL's
is a new word they write instead of the Roc they already know.

The DSL also has to re-invent what Roc's syntax provides already.
Bindings need an explicit binder, `let_("wave", e, |w| ...)`; branching needs
`ifte(c, a, b)`; comparison needs `gte(a, b)`, because `is_gte` is required to
return a `Bool` and so cannot build a node. At full coverage `Expr` converges on
`Code.Ir` without the regions and without the solved types, plus a builder
surface `Code.Ir` never needs, because Roc's own syntax is that surface. And the
translator is written once per target and shared by every shader; this example
looks lopsided because it holds one shader.

Four things the translator has that no amount of DSL code buys:

| | Why a DSL cannot get there |
| --- | --- |
| Source regions in refusals | Roc has no `__LINE__`. A tree built by evaluation knows where its nodes were built only if the author typed the location in |
| The checker's type on every node | `from_numeral` collapses `F32`, `I32` and `Dec` into one `Expr` |
| `in` and `uniform` read off the parameter types | needs a type read at compile time |
| A shader that is also a function | `Expr` is not `F32`, and no amount of code makes it one |

And one the other way, which is the honest cost of this design: a translator is
bounded by Roc's syntax. A DSL can expose any target construct as a combinator,
while a reified function can only use constructs that some Roc expression maps
onto. Where none does, a named method has to stand in, and that method has to
compute the real value as well. `scale` and `offset` are that, and a GLSL
swizzle is the same shape: `.rgb` is one line in a DSL, and here it would be a
`Vec4.rgb : Vec4 -> Vec3` method that genuinely builds the sub-vector, plus an
entry in the translator that maps the name.

## Status

`roc test examples/reifying/glsl/main.roc` passes five expects and
`roc examples/reifying/glsl/main.roc` prints the shader. The whole shader is a
compile-time constant, so `roc check` reports

```
● unconditional condition
This match value is known at compile time
```

on the driver's `match`, which is the point.
