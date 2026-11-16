# The item of each step is a field of the step's payload. One branch drops
# the item's `name` and the other moves it, and the rest of the item lives on
# past the branches. ARC certification carries the item across the join.
Item : { name : Str, value : Str }

next : List(Item) -> [One({ item : Item, rest : List(Item) }), Done]
next = |xs| match xs {
	[first, .. as rest] => if first.name == "" next(rest) else One({ item: first, rest })
	[] => Done
}

go : List(Item), Bool, List(Item) -> List(Item)
go = |xs, edge, acc| match next(xs) {
	One({ item, rest }) => {
		name = if edge "x" else if edge "y" else item.name
		go(rest, edge, acc.append({ name, value: item.value }))
	}
	Done => acc
}

spell : Str, Bool -> Str
spell = |name, edge| if edge and name == "from" "in" else if edge and name == "to" "out" else Str.concat(name, "!")

renamed : Iter(Item), Bool -> List(Item)
renamed = |items, edge| {
	var $out = []
	for item in items {
		$out = $out.append({ name: spell(item.name, edge), value: item.value })
	}
	$out
}

main! = |args| {
	list = [{ name: "from", value: "a" }, { name: "", value: "b" }, { name: "to", value: "c" }]
	items = if args.len() > 0 list.iter() else list.iter().map(|item| { ..item, value: "d" })
	echo!("${Str.inspect(go(list, args.len() > 0, []))}\n")
	echo!("${Str.inspect(renamed(items, args.len() == 0))}\n")
	Ok({})
}
