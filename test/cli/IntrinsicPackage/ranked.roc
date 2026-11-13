# A package function named as a Code argument is described. The same name used
# as a value that runs is an error at the name.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Db
import pa.Hit
import pa.Lib

main! = || {
	seed : List(Hit)
	seed = [{ s: 1 }]
	Stdout.line!("select: ${Db.select(Lib.ranked)}")
	Stdout.line!("map: ${Str.inspect(seed.map(Lib.ranked))}")
}
