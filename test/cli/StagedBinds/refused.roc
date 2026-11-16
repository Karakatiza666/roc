# The refused side of `Code.Binds` (D5 of roc-reify-opaque-proposal.md): a
# captured value of an opaque type at a `Code` position that names no format,
# and one the function reads other than as a captured name or a field path of
# one.
app [main!] { pt: "pt/main.roc", pf: platform "../../fx/platform/main.roc" }

import pf.Stdout
import pt.Time

Fmt := [Default].{
	default : () -> Fmt
	default = || Default

	encode_i128 : I128, List(U8) -> Try(List(U8), [])
	encode_i128 = |n, out| Ok(out.concat(n.to_str().to_utf8()))

	encode_i64 : I64, List(U8) -> Try(List(U8), [])
	encode_i64 = |n, out| Ok(out.concat(n.to_str().to_utf8()))

	rename_field : Fmt, Str -> Str
	rename_field = |_, name| name

	encode_record : List(U8), U64, (List(U8), (List(U8), Str, (List(U8) -> Try(List(U8), [])) -> Try(List(U8), [])) -> Try(List(U8), [])) -> Try(List(U8), [])
	encode_record = |state, _count, write_fields| write_fields(state, |acc, name, write_value| write_value(acc.concat(name.to_utf8())))
}

Event : { at : Time, id : I64 }

Stage := {}.{
	plain : Code(Event -> Bool) -> Code.Bound(Str)
	plain = |code| Code.bound(code, "plain")

	render : Code.Binds(Code(Event -> Bool), Fmt) -> Code.Bound(Str)
	render = |code| Code.bound(code, "render")
}

unbound : Time -> Str
unbound = |cutoff| Stage.plain(|e| e.at.is_before(cutoff)).value()

destructured : Event -> Str
destructured = |order| Stage.render(|e| {
	{ at, .. } = order
	e.at.is_before(at)
}).value()

main! = || {
	Stdout.line!(unbound(Time.from_nanos(1)))
	Stdout.line!(destructured({ at: Time.from_nanos(1), id: 2 }))
}
