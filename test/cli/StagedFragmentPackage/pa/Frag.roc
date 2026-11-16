# Query fragments of the package. The package has no description of them:
# each use that fixes their types describes their sites.
import Db

Frag := {}.{
	named_only : Db.Q({ name : Str, ..r }) -> Db.Q({ name : Str, ..r })
	named_only = |q| q.filter(|x| x.name != "")

	card : Db.Q({ id : Str, name : Str, ..r }) -> Db.Q({ id : Str, name : Str, ..r })
	card = |q| Frag.named_only(q).filter(|x| x.id != "")
}
