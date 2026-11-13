# `Code.prim` of a method the compiler derives, and of a method of a module
# whose name is a builtin type's.
#
# `F32` and `F64` derive `is_eq` (`is_eq : _`), and `Code.prim(F64.is_eq)` is
# the id of the `Prim` a float `==` carries. `import Bool as Flag` names the
# app's own `Bool`, so `Flag.not` is its `not`, not the builtin `Bool.not`,
# and `Flag.level` is found, though the builtin `Bool` has no `level`. The
# methods a module declares on its own type are primitives, so each call is
# a `Prim`.
import Bool as Flag

Tr := {}.{
	ids : Code(f) -> List(Code.PrimId)
	ids = |code| code.graph().root_row().nodes.keep_oks(|node| match node.op {
		Prim(p) => Ok(p.id)
		_ => Err(NotPrim)
	})
}

same64 : F64, F64 -> Bool
same64 = |a, b| a == b

same32 : F32, F32 -> Bool
same32 = |a, b| a == b

flip : Flag -> I64
flip = |f| f.not().level()

negate : Bool -> Bool
negate = |b| !b

main! = |_args| {
	echo!("f64 eq: ${Str.inspect(Tr.ids(same64) == [Code.prim(F64.is_eq)])}\n")
	echo!("f32 eq: ${Str.inspect(Tr.ids(same32) == [Code.prim(F32.is_eq)])}\n")
	echo!("f32 is not f64: ${Str.inspect(Code.prim(F32.is_eq) != Code.prim(F64.is_eq))}\n")
	echo!("flag: ${Str.inspect(Tr.ids(flip) == [Code.prim(Flag.not), Code.prim(Flag.level)])}\n")
	echo!("builtin not: ${Str.inspect(Tr.ids(negate) == [Code.prim(Bool.not)])}\n")
	echo!("flag is not builtin: ${Str.inspect(Code.prim(Flag.not) != Code.prim(Bool.not))}\n")
	Ok({})
}
