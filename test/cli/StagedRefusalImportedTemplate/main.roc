# A use of an imported generic function whose Code site is at the
# function's own row. The use fixes the row, so this module describes the
# site, and the walk refuses it here: the report is in this module, at the
# use, and names the import's source. The use is a crash in place, after
# the line before it ran.
import Lib

Pet : { id : Str, name : Str, age : U8 }

main! = |_args| {
	pets : Lib.Q(Pet)
	pets = Lib.from("pet")
	echo!("before\n")
	echo!("${Lib.render(pets)}\n")
	echo!("after\n")
	Ok({})
}
