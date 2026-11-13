# A row requirement inside the filter lambda is described. The same requirement
# outside the lambda runs.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Db
import pa.T

row_first = |q, row| if (row.t.now()) q else Db.Q.filter(q, |x| x.t.now())

main! = || {
	clocks : Db.Q({ t : T })
	clocks = Db.Q.new({})
	clock : T
	clock = { n: 1 }
	Stdout.line!("row: ${clocks.filter(|x| x.t.now()).show()}")
	Stdout.line!("row outside: ${row_first(clocks, { t: clock }).show()}")
}
