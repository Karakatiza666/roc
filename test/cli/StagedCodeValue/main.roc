# A clause that reads a constant holding a `Code` value is refused, and the
# report names the constant (structural proposal D7, Y4). The constant's
# method is in this module but outside the site, so the report names the
# site that reached it too (D9, Y11). The `Plain` handle holds no `Code` and
# is the control.
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import Db
import T

Visit : { id : Str, vet : Str }
Vet : { id : Str, name : Str }

vets : T.Table(Vet)
vets = T.table("vet", |v| v)

plain_vets : T.Plain(Vet)
plain_vets = T.plain("vet")

main! = || {
	visits : Db.Q(Visit)
	visits = Db.from("visit")
	Stdout.line!("plain: ${visits.filter(|v| v.vet == plain_vets.key("ruth")).show()}")
	Stdout.line!("table: ${visits.filter(|v| v.vet == vets.key("ruth")).show()}")
}
