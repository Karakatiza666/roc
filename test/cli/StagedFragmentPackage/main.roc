# A fragment of a package, used from the app (D1 of
# roc-reify-structural-proposal.md). The app's use fixes the fragment's
# types, so the description is written where the app is published.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Db
import pa.Frag

Pet : { id : Str, name : Str, age : U8 }
Owner : { id : Str, name : Str, city : Str }

main! = || {
	pets : Db.Q(Pet)
	pets = Db.from("pet")
	owners : Db.Q(Owner)
	owners = Db.from("owner")
	Stdout.line!("named: ${Frag.named_only(pets).show()}")
	Stdout.line!("card: ${Frag.card(owners).show()}")
}
