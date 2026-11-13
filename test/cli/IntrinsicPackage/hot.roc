# A package definition that reaches an intrinsic is described in a clause. Used as a
# value at run time it is an error, with the chain into the package file.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Db
import pa.Lib
import pa.Text # hot_lib_only.roc gives the same chain without this import.

main! = || {
	people : Db.Q({ name : Str })
	people = Db.Q.new({})
	name = "a"
	Stdout.line!("clause: ${people.filter(|p| Lib.hot(p.name)).show()}")
	Stdout.line!("run: ${Str.inspect(Lib.hot(name))}")
}
