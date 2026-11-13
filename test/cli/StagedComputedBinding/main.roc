# A value of an imported module that computes a function holding a `Code`
# site, used at the app's row.
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import Lib

main! = || {
	q : Lib.Q({ name : Str, age : U8 })
	q = Lib.Q.({ log: "y" })
	Stdout.line!(Lib.pick(q).log)
}
