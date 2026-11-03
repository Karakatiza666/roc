# Hello, translator

A translator is a Roc function that runs while the compiler runs. It reads the
compiler's description of another Roc function and returns something else, here
an arithmetic expression as text. This is the smallest useful one. Read it
first, then read `../glsl/`, `../sql/` and `../dbsp/`.

| File | What it is |
| --- | --- |
| `Calc.roc` | The translator. `to_expr` returns a `Try`. `to_expr_or_stop` stops the build at the source line of a node it cannot translate. |
| `main.roc` | Two ordinary Roc functions, the translation of one, and three `expect`s. |
| `refused.roc` | A function that `to_expr_or_stop` refuses, so `roc check` prints a report. |
| `expected_output.txt` | What `roc main.roc` prints. |

```
roc examples/reifying/hello/main.roc         # prints the text in expected_output.txt
roc test examples/reifying/hello/main.roc    # 3 expects
roc check examples/reifying/hello/refused.roc  # exit status 1, prints the report below
```

## How a function becomes a description

```roc
area : F64, F64 -> F64
area = |w, h| w * h + 1.0

Calc.to_expr(area)
```

`to_expr` takes a `Code(f)`. A function that stands where a `Code(f)` is
expected is not called. The compiler describes it and passes the description.
`area` stays an ordinary function, so the first `expect` calls it.

| Step | In `Calc.roc` |
| --- | --- |
| Get the function as a graph, and take its root row | `code.graph().root_row()` |
| The row ends in one value | `row.body.end` is `Value([result])` |
| A value is a parameter, or the output of the node at an index in `row.nodes` | `Param(k)`, `Node(index)` |
| A node is a literal, or a call of a builtin | `Lit(..)`, `Prim({ method, .. })` |

`area` has three nodes. A node can read only nodes before it.

| Index | `op` | `args` |
| --- | --- | --- |
| 0 | `Prim({ owner: "Num.F64", method: "times" })` | `Param(0)`, `Param(1)` |
| 1 | `Lit(Frac(1, F64))` | none |
| 2 | `Prim({ owner: "Num.F64", method: "plus" })` | `Node(0)`, `Node(1)` |

The body ends in `Value([Node(2)])`. So `to_expr(area)` is
`Ok("((p0 * p1) + 1)")`. A literal `1.0` prints as `1`, because a whole
`F64` prints without a decimal point.

## A refusal is an `Err`

`root` calls `sqrt`, and `Calc` has no operator for it. `to_expr` returns an
`Err`, and the third `expect` tests it:

```roc
expect Calc.to_expr(root) == Err(Unsupported("`sqrt` has no operator here"))
```

An `Err` has no source line. The caller gets the reason and no more.

## A refusal that stops the build

`to_expr_or_stop` calls `Code.refuse_at` with the row and the index of the
node it cannot translate. `refused.roc` evaluates it at the top level, so the
compiler stops and reports the reason at the source the node came from:

```
$ roc check refused.roc
── ✗ translation refused ────────────────────────────────────── refused.roc:6:12

A translator refused code that this expression built.

root = |x| x.sqrt() + 1.0
           ^^^^^^^^

The translator gave this reason:

    `sqrt` has no operator here

── 1 error and 0 warnings ────────────────────────────────────────── refused.roc
```

The exit status is 1. The title line has the path as you give it to `roc`.

An `expect` cannot test this path, because the compile stops. Test the `Err`
path with an `expect`. Use `refuse_at` for the user who wants a line number.
If the translator runs when the program runs, `refuse_at` crashes with the
reason and does not make a report.

See `docs/langref/reifying.md` for the full guide.
