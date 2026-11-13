# A refusal inside another module's source is reported in that module's file,
# with the site that reached it (F4 of roc-reify-opaque-proposal.md). The body
# of `ATime.shifted` builds an opaque record, which a description has no
# form for, so the report names `pa/Time.roc` and the site in this file. A
# refusal in this module's own source stays in this file.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Time as ATime

Stage := {}.{
	describe : Code(f) -> Str
	describe = |code| "lambda/${Code.graph(code).root_row().params.len().to_str()}"
}

Stamp :: { n : I64 }

away : Str
away = Stage.describe(|x| ATime.shifted(x))

here : Str
here = Stage.describe(|n| Stamp.{ n })

main! = || {
	Stdout.line!(away)
	Stdout.line!(here)
}
