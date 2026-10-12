# An annotated recursive function whose body narrows its annotation.
#
# The result's `[Required, Optional]` is open in the annotation and closed by
# the body, which returns the union `Shape` holds. The self-reference
# instantiates the annotation's scheme, which quantifies one variable more than
# the body's, and calls itself at `U8` where `main!` calls it at `Str`.
Shape := [Leaf(List({ name : Str, presence : [Required, Optional] })), Wrap(Shape)]

fields_of : Shape, a -> (a, List({ name : Str, presence : [Required, Optional] }))
	where [a.to_str : a -> Str]
fields_of = |shape, tag| match shape {
	Leaf(fields) => (tag, fields.map(|f| { ..f, name: "${f.name}${tag.to_str()}" }))
	Wrap(inner) => {
		(_, fs) = fields_of(inner, 7.U8)
		(tag, fs)
	}
}

main! = |_args| {
	(label, fs) = fields_of(Shape.Wrap(Shape.Leaf([{ name: "a", presence: Required }])), "x")
	echo!("${label} ${Str.join_with(fs.map(|f| f.name), ",")}\n")
	Ok({})
}
