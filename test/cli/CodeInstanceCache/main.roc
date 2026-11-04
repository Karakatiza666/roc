# Code descriptions under a warm `--specialize=no` cache. Each value is a
# constant, so the compile-time program computes it against the cached
# objects of the package's modules; an edit to the body of a definition a
# description reads must reach every object that restores the description.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Db
import pa.Pick
import pa.Made

Pet : { id : Str, name : Str }

main! = || {
	pets : Db.Q(Pet)
	pets = Db.from("pets")
	tags : Db.Q(Pick.Tag)
	tags = Db.from("tags")
	Stdout.line!("site: ${Pick.direct(pets).show()}")
	Stdout.line!("table: ${Pick.wrap(pets).show()}")
	Stdout.line!("method table: ${Pick.wrap_tags(tags).show()}")
	Stdout.line!("stored table: ${Made.run(tags).show()}")
}
