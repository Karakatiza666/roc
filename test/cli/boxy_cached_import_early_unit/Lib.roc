import Base

# `named_only` holds a Code instance inventory.
Lib := {}.{
    filter : Q(row), Code(row -> Bool) -> Q(row)
    filter = |q, code| Q.({ log: "${q.log} | ${code.graph().slots().len().to_str()}" })

    named_only : Q({ name : Str, ..r }) -> Q({ name : Str, ..r })
    named_only = |q| Lib.filter(q, |x| x.name != "")

    label : Base -> Str
    label = |_b| "lib"
}

Q(row) := { log : Str }
