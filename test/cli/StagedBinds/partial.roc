# A lambda at a `Code` position calls a name that the block around it binds
# to a call that hands back a function: `pred = above(n)`, then `pred(x)`.
# The walk replays the binding and reads the call as `above(n)(x)` written
# in the lambda: one `Call` of the row that gathers the parameters of both
# lambdas of `above`. The run-time `n` is one input slot.
app [main!] { st: "../StagedValueSites/st/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import st.Stage

Keep := {}.{
	keep : Code(I64 -> Bool) -> Code.Bound(Str)
	keep = |code| Code.bound(code, Stage.describe(code))
}

above : I64 -> (I64 -> Bool)
above = |n| |y| y > n

shown : Code.Bound(Str) -> Str
shown = |bound| "${bound.value()} inputs ${Str.inspect(bound.inputs())}"

bound : I64 -> Str
bound = |n| {
	pred = above(n)
	shown(Keep.keep(|x| pred(x)))
}

inline : I64 -> Str
inline = |n| shown(Keep.keep(|x| above(n)(x)))

main! = || {
	Stdout.line!("bound: ${bound(3)}")
	Stdout.line!("inline: ${inline(3)}")
}
