# A call that fixes a row variable to `Str` is a type mismatch, with a hint
# that names the record extension (design.md "Record Extension
# Well-Formedness").
app [main!] { pf: platform "../../fx/platform/main.roc" }

import pf.Stdout

wrap : r -> { z : I64, ..r }
wrap = |_x| crash "never"

use_str : Str -> I64
use_str = |s| wrap(s).z

main! = || Stdout.line!(use_str("a").to_str())
