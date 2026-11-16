# Each `Code.prim` argument here names no definition. Each is reported once
# at the argument, and the call is a runtime error. The compiler must not
# lower the `Code.prim` callee as a value (task 13e).
p = Code.prim(Str.nope_nope)
q = Code.prim(Nope.x)
r = Code.prim(nope)
s = Code.prim(1 + 2)

f = |x| {
    _t = Code.prim(Str.nope_nope)
    _u = Code.prim(nope)
    x
}

main! = |_args| {
    _n = f(1)
    Ok({})
}
