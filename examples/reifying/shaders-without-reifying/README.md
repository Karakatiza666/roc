# Shaders without reification

The control experiment for [`roc-reify-proposal.md`](../../../roc-reify-proposal.md):
the shader of [`../glsl/`](../glsl/), written as a library DSL over static
dispatch instead of as a Roc function, so that what reification adds can be
measured instead of asserted.

```
roc main.roc
```

prints the shader in `expected_output.glsl`, which raylib compiles and
[roc-ray](https://github.com/lukewilliamboswell/roc-ray) accepts through
`Draw.Shader.from_source!`.

## Why it works at all

Roc's arithmetic operators are method calls, so a nominal type can implement
them. `+` dispatches to `plus`, `*` to `times`, and a numeric literal to
`from_numeral`. `Expr` implements all three, so

```roc
frag.fragTexCoord.y() * 28.0 + settings.time * 2.0
```

builds a syntax tree rather than computing a number, and the tree prints as
GLSL. The two parameter records, the vector types and the sampler all survive
the translation: `post_process` reads the same here as it does next door,
line for line.

## Where it stops

| Limit | Shows up as |
| --- | --- |
| A `let` leaves no trace in the tree | four texture fetches and thirteen `sin` calls, where the source writes one and four |
| The function is over `Expr`, not `F32` | `post_process` cannot be called on real numbers, run on the CPU, or reached by an `expect` |
| `is_gte` must return `Bool`; `and`, `or`, `if` are keywords | a predicate is written in invented names, `a.gte(b).both(c)`; a conditional as `mix(a, b, step(x, y))` |
| Field access is syntax, not a method | a lane is `uv.x()`, and the DSL has to define one method per lane per vector type |
| Nothing reads the parameter types | the `in` and `uniform` lines and the `Var` names are two hand-written lists, and nothing checks one against the other |

The first is the one that matters, because it is a defect in the output rather
than in the ergonomics, and it compounds with every binding: this shader is 925
characters against the translator's 508. A GLSL driver will likely recover the
sharing by common-subexpression elimination, which is the charitable case. A
target with no optimizer behind it, a SQL engine or an interpreter, runs what it
is given. Either way the author cannot say what they meant. Reifying the
function body keeps the bindings, and the translator emits one GLSL local for
each.
