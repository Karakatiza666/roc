# An imported reify-only definition, an imported intrinsic method, and an
# imported method whose body is reify-only each make the caller reify-only.
app [main!] { pf: platform "../../fx/platform/main.roc" }

import Frag

caller = |s| Frag.uses_hot(s)

plain_caller = |s| Frag.plain(s)

clock_now : Frag.Clock -> Bool
clock_now = |c| c.now()

meter_now : Frag.Meter -> Bool
meter_now = |m| m.now()

main! = || {}
