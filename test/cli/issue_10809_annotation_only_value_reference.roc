# Repro for https://github.com/roc-lang/roc/issues/10809:
# a top-level declaration that has a type annotation and no value is an intrinsic,
# so each reference to one that runs is reported, never handed to post-check
# lowering as a procedure use. A reference in code that never runs is fine.
d : i

o = || {
    D() = d
}

n : U64

p = n

f : U64 -> U64

q = f(1)

add_n = |x| x + n

main! = |_| {
    _ = add_n(1)
    Ok({})
}
