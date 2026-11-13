# Values at `Code` positions (R12). A call argument at a `Code(a)` position
# is decided by its solved type: a function is described as code, a `Code`
# value is passed on, and any other value is described as the literal it is
# fixed to, or as one input slot that holds the whole value when it reads
# what exists only when the program runs. The translator is in a package.
app [main!] { st: "st/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdin
import pf.Stdout
import st.Stage

# A query whose `limit` takes a value at a `Code(U64)` position.
Q := [Q(Str)].{
	from : Str -> Q
	from = |table| Q("FROM ${table}")

	filter : Q, Code(U16 -> Bool) -> Q
	filter = |Q(text), _code| Q("${text} WHERE")

	limit : Q, Code(U64) -> Q
	limit = |Q(text), code| Q("${text} LIMIT [${Stage.describe(code)}]")

	ready : Q -> Code.Bound(Str)
	ready = |Q(text)| Code.Bound.of(text)
}

ten : U64
ten = 10

# A name of a function at a `Code` position is described as code.
triple : U64 -> U64
triple = |x| x * 3

shown_bound : Code.Bound(Str) -> Str
shown_bound = |b| "${b.value()} inputs ${Str.inspect(b.inputs())}"

# A value that reads a parameter is one input slot.
doubled : U64 -> Str
doubled = |n| shown_bound(Stage.bind_u64(n * 2))

# A fixed value in a chain is a literal; one that reads a parameter is an
# input slot after the lambda's.
fixed : U16 -> Str
fixed = |least| shown_bound(Q.from("meds").filter(|m| m > least).limit(10).ready())

limited : U16, U64 -> Str
limited = |least, n| shown_bound(Q.from("meds").filter(|m| m > least).limit(n * 2).ready())

# An `if` gives the position to each branch, and each branch is decided on
# its own: here each is a literal.
chosen : Bool -> Str
chosen = |up| Stage.show_u64(if up 10 else 20)

# A `Code` parameter at a `Code` position is passed on.
relay : Code(U64) -> Str
relay = |code| Stage.show_u64(code)

# With no annotation, an earlier line fixes `code` to `Code(U64)`, so it is
# passed on.
early : Bool, Code(U64) -> Str
early = |flag, known| {
	inner = |code| {
		_chosen = if flag code else known
		Stage.show_u64(code)
	}
	inner(known)
}

# With no annotation, a variable at a `Code` position whose content is a
# function is passed on.
relay_fn = |code| Stage.show_fn(code)

# A fixed value of a generic function is described at each closing use.
Id(r) := [Id(Str)].{
	named : Str -> Id(r)
	named = |s| Id(s)
}

fixed_id : {} -> (Id(r), Str)
fixed_id = |_| {
	id = Id.named("k1")
	(id, Stage.shown(id))
}

take_u8 : Id(U8) -> {}
take_u8 = |_| {}

take_str : Id(Str) -> {}
take_str = |_| {}

main! = || {
	Stdout.line!("lit: ${Stage.show_u64(10)}")
	Stdout.line!("top: ${Stage.show_u64(ten)}")
	Stdout.line!("sum: ${Stage.show_u64(ten * 2 + 1)}")
	Stdout.line!("bare value: ${Stage.shown(7)}")
	Stdout.line!("bare lambda: ${Stage.shown(|s| Str.concat(s, "!"))}")
	Stdout.line!("record: ${Stage.shown({ a: 1.U8, b: "x" })}")
	Stdout.line!("tag: ${Stage.shown(Ok(3.U8))}")
	Stdout.line!("list: ${Stage.shown([1.U8, 2])}")
	Stdout.line!("lambda: ${Stage.show_fn(|x| x + 1)}")
	Stdout.line!("named: ${Stage.show_fn(triple)}")
	Stdout.line!("doubled: ${doubled(4)}")
	Stdout.line!("fixed: ${fixed(3)}")
	Stdout.line!("limited: ${limited(3, 4)}")
	Stdout.line!("chosen: ${chosen(Bool.False)}")
	Stdout.line!("relay: ${relay(5)}")
	Stdout.line!("early: ${early(True, 6)}")
	Stdout.line!("relay_fn: ${relay_fn(|x| x * 3)}")
	(a, s) = fixed_id({})
	take_u8(a)
	(b, t) = fixed_id({})
	take_str(b)
	Stdout.line!("closing: ${s} / ${t}")
	typed = Stdin.line!().count_utf8_bytes()
	Stdout.line!("read: ${doubled(typed)} / ${limited(1, typed)}")
}
