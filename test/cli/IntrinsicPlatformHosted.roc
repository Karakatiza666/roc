# A bodyless declaration in a platform module stays hosted: the host gives it
# its body, so code that runs calls it. Only a bodyless declaration outside
# the platform is an intrinsic.
app [main!] { pf: platform "../fx/platform/main.roc" }

import pf.Stdout

main! = || Stdout.line!("hosted line")
