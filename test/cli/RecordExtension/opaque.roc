# A `::` opaque type is refused in a record extension slot, in another
# module as in its own (design.md "Record Extension Well-Formedness").
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import Own

Ref(r) := { ..r }

name_of : Ref(Own) -> Str
name_of = |o| o.name

main! = || Stdout.line!(name_of(crash "never"))
