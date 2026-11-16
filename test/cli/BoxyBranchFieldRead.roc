# A branch that reads a record field or a tuple item into a match result that
# other branches also fill. Under Boxy the read value is described by its
# static descriptor, the same on every path, so no branch leaves the result's
# descriptor unassigned.
End : [Value(List(U32)), Jump({ args : List(U32), target : U32 }), Pair((List(U32), U32))]

end_vals : End -> List(U32)
end_vals = |end| match end {
	Value(vals) => vals
	Jump(jump) => jump.args
	Pair(pair) => pair.0
}

expect end_vals(Value([1, 2])) == [1, 2]
expect end_vals(Jump({ args: [3], target: 0 })) == [3]
expect end_vals(Pair(([4], 5))) == [4]
