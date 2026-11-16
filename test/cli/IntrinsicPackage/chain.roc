# A generic package definition reaches an intrinsic at a use that fixes its type
# to T. Inside a Code lambda the use is described. At run time it is an error.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Db
import pa.Lib
import pa.T

main! = || {
	t : T
	t = { n: 1 }
	Stdout.line!("described: ${Db.count(|x| Lib.outer(x))}")
	Stdout.line!("intrinsic: ${Str.inspect(Lib.outer(t))}")
}
