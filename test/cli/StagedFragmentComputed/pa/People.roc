# A second module of the package that uses `Frag.pick`, at another row.
import Db
import Frag

People := {}.{
	Person : { name : Str, age : U8, city : Str }

	named : {} -> Str
	named = |{}| {
		people : Db.Q(People.Person)
		people = Db.from("person")
		Frag.pick(people).show()
	}
}
