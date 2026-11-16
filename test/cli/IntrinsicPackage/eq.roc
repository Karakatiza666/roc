# A derived equality reaches its element's intrinsic is_eq. In a clause it is
# described. At run time it is an error.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Db
import pa.Hit

main! = || {
	rows : Db.Q({ h : Hit })
	rows = Db.Q.new({})
	h : Hit
	h = { s: 1 }
	Stdout.line!("clause: ${rows.filter(|r| [r.h] == [r.h]).show()}")
	Stdout.line!("run: ${Str.inspect([h] == [h])}")
}
