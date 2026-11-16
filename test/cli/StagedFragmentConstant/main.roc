# Constants of a package that hold query fragments, with no annotation
# (Q16 of roc-reify-structural-proposal.md). Each use of a constant fixes
# its types, and gives the fragments it holds the table of their sites at
# those types: a tuple, a record, and a constant that holds the other two.
app [main!] { pa: "pa/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pa.Db
import pa.Frag

Pet : { id : Str, name : Str, age : U8 }
Person : { name : Str, age : U8, city : Str }

main! = || {
	pets : Db.Q(Pet)
	pets = Db.from("pet")
	people : Db.Q(Person)
	people = Db.from("person")
	Stdout.line!("tuple: ${(Frag.pair.0)(pets).show()} ; ${(Frag.pair.0)(people).show()} ; ${(Frag.pair.1)(people).show()}")
	Stdout.line!("record: ${(Frag.both.named)(people).show()} ; ${(Frag.both.grown)(pets).show()}")
	Stdout.line!("nested: ${(Frag.nested.inner.1)(pets).show()} ; ${(Frag.nested.more)(people).show()}")
}
