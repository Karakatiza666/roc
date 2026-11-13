# A top-level value that holds a closure made in a generalized local
# function. Monotype restores the closure, and it replays the dispatch
# relations of each lexical scope of the closure. An evidence index counts
# frames from the scope of its own dispatch, so each scope must replay with
# its own frame as the head of the evidence chain.
RestoredClosureOfGeneralizedLocal := {}

## The dispatch `a + b` belongs to the root scope, and `take_first` belongs
## to the generalized scope of `joined`.
take_by_sum : U64, U64 -> (List(Str) -> List(Str))
take_by_sum = |x, y| {
	joined = |a, b| {
		read = |outcomes| outcomes.take_first(a)
		_sum = a + b
		read
	}
	joined(x, y)
}

## Here `a + 1` dispatches on a number type of the generalized scope.
take_second : U64, U64 -> (List(Str) -> List(Str))
take_second = |x, y| {
	joined = |a, b| {
		read = |outcomes| outcomes.take_first(b)
		{ count: a + 1, read }
	}
	joined(x, y).read
}

first_one : List(Str) -> List(Str)
first_one = take_by_sum(1, 1)

first_two : List(Str) -> List(Str)
first_two = take_second(1, 2)

expect first_one(["x", "y"]) == ["x"]

expect first_two(["x", "y", "z"]) == ["x", "y"]
