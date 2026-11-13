# A module of the package that uses `Frag.pick` at its own row.
import Db
import Frag

Pets := {}.{
	Pet : { id : Str, name : Str, age : U8 }

	named : {} -> Str
	named = |{}| {
		pets : Db.Q(Pets.Pet)
		pets = Db.from("pet")
		Frag.pick(pets).show()
	}
}
