# A `Code` argument named through a rejected import has one report: the
# import's.
#
# The package `pa` does not expose `Preds`, so the import is rejected,
# `Preds.adult` resolves to nothing, and the `filter(..)` call that passes it
# is retired into a runtime error that still evaluates its receiver: a
# closing use of the package's fragment `Frag.named_only`, which gets its
# instance table like any other.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Frag
import pa.Preds

Pet : { name : Str, age : U8 }

pets : Frag.Q(Pet)
pets = Frag.from("pets")

shown : Str
shown = Frag.named_only(pets).filter(Preds.adult).show()

main! = || Stdout.line!(shown)
