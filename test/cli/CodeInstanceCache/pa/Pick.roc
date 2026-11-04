# Closing uses of Frag's fragments, a Code site that reads Frag.check, and
# a stored function that captured one of this module's instance tables.
import Db
import Frag

Pet : { id : Str, name : Str }

Pick := {}.{
	Tag := { label : Str }.{
		keep : Tag -> Bool
		keep = |t| t.label != "pick-one"
	}

	direct : Db.Q(Pet) -> Db.Q(Pet)
	direct = |q| q.filter(|x| Frag.check(x.name))

	wrap : Db.Q(Pet) -> Db.Q(Pet)
	wrap = |q| Frag.named_only(q)

	wrap_tags : Db.Q(Tag) -> Db.Q(Tag)
	wrap_tags = |q| Frag.kept(q)

	make : {} -> (Db.Q(Tag) -> Db.Q(Tag))
	make = |_| Frag.kept

	made : Db.Q(Tag) -> Db.Q(Tag)
	made = Pick.make({})
}
