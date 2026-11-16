# Helper chains over open records (structural proposal Y2). A type reference
# names the frame its variables belong to (D2), so an annotated open-row helper
# that calls another one describes at the row the site fixed, and a named site
# hands its root the evidence its lookup recorded (D3), so an unannotated root
# that forwards a `where` requirement to another helper describes too. Each
# line prints the parameter types the translator receives.
Stage := {}.{
	owners : Code(Owner -> Bool) -> Str
	owners = |code| Stage.params(code)

	pairs : Code({ a : Owner, b : Pet } -> Bool) -> Str
	pairs = |code| Stage.params(code)

	nested : Code(Visit -> Bool) -> Str
	nested = |code| Stage.params(code)

	tagged : Code([Cat, Dog] -> Bool) -> Str
	tagged = |code| Stage.params(code)

	params : Code(f) -> Str
	params = |code| {
		graph = Code.graph(code)
		rows = graph.rows().map(|row| Str.inspect(row.params))
		Str.join_with(rows, " ; ")
	}
}

Owner : { id : Str, name : Str, city : Str }
Pet : { id : Str, city : Str, legs : U8 }
Visit : { id : Str, owner : { city : Str, name : Str } }

in_oslo : { city : Str, ..r } -> Bool
in_oslo = |x| x.city == "Oslo"

## An annotated open-row helper that calls another one.
named_in_oslo : { city : Str, name : Str, ..r } -> Bool
named_in_oslo = |x| in_oslo(x) and x.name != ""

## An annotated helper over an unannotated inner one.
plain_in_oslo = |x| x.city == "Oslo"

outer_over_plain : { city : Str, name : Str, ..r } -> Bool
outer_over_plain = |x| plain_in_oslo(x) and x.name != ""

## An unannotated outer helper over an annotated inner one.
unannotated_outer = |x| in_oslo(x) and x.name != ""

## A nested record field of a row-bound use is read in the caller's frame.
owner_in_oslo : { owner : { city : c, ..o }, ..r } -> Bool where [c.is_eq : c, c -> Bool]
owner_in_oslo = |v| v.owner.city == v.owner.city

## An open tag row in an annotated chain.
is_cat : [Cat, ..t] -> Bool
is_cat = |pet| match pet {
	Cat => True
	_ => False
}

cat_chain : [Cat, ..t] -> Bool
cat_chain = |pet| is_cat(pet)

## A recursive open-row helper over a tag union keeps its row as
## `city_after` does: the key digests the union, so it does not grow.
depth : [Cat, ..t], U8 -> U8
depth = |pet, k| if k == 0 0 else depth(pet, k - 1) + 1

cat_depth : [Cat, ..t] -> Bool
cat_depth = |pet| is_cat(pet) and depth(pet, 2) > 0

## A recursive open-row helper keeps its row, so each row it is called at
## shows: two calls at two records are two rows.
city_after : { city : Str, ..r }, U8 -> Bool
city_after = |x, k| if k == 0 x.city == "Oslo" else city_after(x, k - 1)

## An annotated outer helper over the recursive one: the inner row is the
## outer's row as the site fixed it, read in the outer's frame.
named_city_after : { city : Str, name : Str, ..r } -> Bool
named_city_after = |x| city_after(x, 2) and x.name != ""

## Two unannotated helpers: `same` has a `where` requirement (`a.is_eq`).
same = |a, b| a == b
city_is_oslo = |x| same(x.city, "Oslo")

annotated_named : Str
annotated_named = Stage.owners(named_in_oslo)

annotated_inline : Str
annotated_inline = Stage.owners(|p| named_in_oslo(p))

over_plain : Str
over_plain = Stage.owners(outer_over_plain)

over_annotated : Str
over_annotated = Stage.owners(unannotated_outer)

two_rows : Str
two_rows = Stage.pairs(|v| city_after(v.a, 2) and city_after(v.b, 2))

inner_row : Str
inner_row = Stage.owners(named_city_after)

nested_field : Str
nested_field = Stage.nested(owner_in_oslo)

tag_chain : Str
tag_chain = Stage.tagged(cat_chain)

tag_depth : Str
tag_depth = Stage.tagged(cat_depth)

forwarded_inline : Str
forwarded_inline = Stage.owners(|o| city_is_oslo(o))

forwarded_named : Str
forwarded_named = Stage.owners(city_is_oslo)

main! = |_args| {
	echo!("annotated named: ${annotated_named}\n")
	echo!("annotated inline: ${annotated_inline}\n")
	echo!("over plain: ${over_plain}\n")
	echo!("over annotated: ${over_annotated}\n")
	echo!("two rows: ${two_rows}\n")
	echo!("inner row: ${inner_row}\n")
	echo!("nested field: ${nested_field}\n")
	echo!("tag chain: ${tag_chain}\n")
	echo!("tag depth: ${tag_depth}\n")
	echo!("forwarded inline: ${forwarded_inline}\n")
	echo!("forwarded named: ${forwarded_named}\n")
	Ok({})
}
