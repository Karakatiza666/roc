# A record extension slot `..r` refuses a type that is not a record
# (design.md "Record Extension Well-Formedness"). `Ref(Str)` crashed later
# stages before the rule (structural proposal Y10).
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout

Ref(r) := { ..r }

show : Ref(Str) -> Str
show = |_x| "ok"

main! = || Stdout.line!(show(crash "never"))
