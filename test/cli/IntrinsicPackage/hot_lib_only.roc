# The app imports Lib and not Text, which holds the intrinsic. Lib exports the
# full chain of `hot`, so the report names Text.is_email and its place.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Db
import pa.Lib

main! = || {
	people : Db.Q({ name : Str })
	people = Db.Q.new({})
	name = "a"
	Stdout.line!("clause: ${people.filter(|p| Lib.hot(p.name)).show()}")
	Stdout.line!("run: ${Str.inspect(Lib.hot(name))}")
}
