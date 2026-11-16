# Package values that compute query fragments, with no annotation. Each use
# in another module fixes the value's row: two modules of the package and
# the app use `Frag.pick` at three rows, and `Frag.pick_again` reads `pick`
# at its own row. `here` is a value of the app that its one use fixes, so
# compile-time evaluation stores it.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Db
import pa.Frag
import pa.Pets
import pa.People

Item : { name : Str, id : U64 }
Dog : { name : Str, breed : Str }

here = if Bool.True Frag.named_only else Frag.named_only

main! = || {
	items : Db.Q(Item)
	items = Db.from("item")
	Stdout.line!("pets: ${Pets.named({})}")
	Stdout.line!("people: ${People.named({})}")
	Stdout.line!("app: ${Frag.pick(items).show()}")
	dogs : Db.Q(Dog)
	dogs = Db.from("dog")
	Stdout.line!("again: ${Frag.pick_again(dogs).show()}")
	Stdout.line!("here: ${here(items).show()}")
}
