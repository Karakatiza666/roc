# Two packages each declare an opaque type `Time` with a method `is_lt`, and a
# transparent type `Point` of one backing. They are two types of each name and
# two primitives, so the descriptions that read one package's types and the
# other's differ, and two functions that compare one package's times are one
# description (F2 and Q13 of roc-reify-opaque-proposal.md).
app [main!] { pa: "pa/main.roc", pb: "pb/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Time as ATime
import pb.Time as BTime
import pa.Point as APoint
import pb.Point as BPoint

Stage := {}.{
	## The digest of the node the root returns, which is its last node.
	result : Code.Inlined(f) -> U128
	result = |code| {
		root = code.inline().root_row()
		digests = root.nodes.map_with_index(|_, node| code.inline_digest({ row: root.id, node: node.to_u32_wrap() }).to_u128())
		digests.last().ok_or(0)
	}
}

a_before : ATime, ATime -> Bool
a_before = |x, y| x < y

a_again : ATime, ATime -> Bool
a_again = |t, u| t < u

b_before : BTime, BTime -> Bool
b_before = |x, y| x < y

a_list : ATime -> List(ATime)
a_list = |x| [x]

b_list : BTime -> List(BTime)
b_list = |x| [x]

a_point : APoint -> List(APoint)
a_point = |p| [p]

b_point : BPoint -> List(BPoint)
b_point = |p| [p]

main! = || {
	Stdout.line!("one package: ${Str.inspect(Stage.result(a_before) == Stage.result(a_again))}")
	Stdout.line!("two primitives: ${Str.inspect(Stage.result(a_before) != Stage.result(b_before))}")
	Stdout.line!("two types: ${Str.inspect(Stage.result(a_list) != Stage.result(b_list))}")
	Stdout.line!("two named types: ${Str.inspect(Stage.result(a_point) != Stage.result(b_point))}")
}
