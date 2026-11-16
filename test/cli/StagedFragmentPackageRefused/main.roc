# A refusal inside a package fragment's site is reported at the app's use
# that fixes the fragment's types, in the package's file (D1 of
# roc-reify-structural-proposal.md).
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Db
import pa.Frag

Pet : { id : Str, age : I64 }

main! = || {
	pets : Db.Q(Pet)
	pets = Db.from("pet")
	Stdout.line!(Frag.recent(pets).show())
}
