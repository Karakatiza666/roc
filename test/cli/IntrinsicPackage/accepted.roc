# Intrinsics declared in a package. Every use here is described in a clause
# or never reaches an intrinsic, so the app runs.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Db
import pa.Hit
import pa.Lib
import pa.T

# An app type whose `now` has a body.
M := { n : U64 }.{
	now : M -> Bool
	now = |m| m.n > 0
}

main! = || {
	people : Db.Q({ e : Str, name : Str })
	people = Db.Q.new({})
	clocks : Db.Q({ t : T })
	clocks = Db.Q.new({})
	rows : Db.Q({ h : Hit })
	rows = Db.Q.new({})
	m : M
	m = { n: 1 }
	Stdout.line!("clause: ${people.filter(|p| Lib.hot(p.name)).show()}")
	Stdout.line!("fragment: ${Lib.named_only(people).show()}")
	Stdout.line!("select: ${Db.select(Lib.ranked)}")
	Stdout.line!("count: ${Db.count(|t| Lib.outer(t))}")
	Stdout.line!("row: ${clocks.filter(|x| x.t.now()).show()}")
	Stdout.line!("eq: ${rows.filter(|r| [r.h] == [r.h]).show()}")
	Stdout.line!("body: ${Str.inspect(Lib.outer(m))}")
}
