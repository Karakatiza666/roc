# A package exports an opaque nominal type built on `Code.Bound` and a
# builder whose terminal call returns it (R5 option A' of the Gap 1 design).
# The app never names `Code.Bound`: its chain ends in the package's type,
# which binds the run-time reads of its lambdas.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Q
import pa.Prepared

cheaper_than : U16 -> Prepared(Str)
cheaper_than = |limit| Q.from("meds").filter(|m| m < limit).filter(|m| m != limit + 1).ready()

show : Prepared(Str) -> Str
show = |p| "${p.value() ?? "err"} inputs ${Str.inspect(p.inputs())}"

main! = || {
	Stdout.line!(show(cheaper_than(3)))
	Stdout.line!(show(cheaper_than(9)))
}
