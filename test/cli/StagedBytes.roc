# An embedded file in a reified body.
#
# A file embedded as `List(U8)` describes as a single `Bytes` literal rather
# than one `Int` node per byte, because a file is as large as it is and a
# translator wants the blob as one value. A file embedded as `Str` is a `Str`
# literal instead.
import "staged_bytes_blob.bin" as blob : List(U8)
import "staged_bytes_text.txt" as source : Str

StagedBytes := {}.{
	describe : Code(f) -> Str
	describe = |code| StagedBytes.node(code.ir())

	node : Code.Ir -> Str
	node = |ir| match ir {
		Lambda(_, body, _) => StagedBytes.node(body)
		Param(name, _) => name
		Lit(value, _) => StagedBytes.lit(value)
		_ => "other"
	}

	lit : Code.Lit -> Str
	lit = |value| match value {
		Bool(flag) => if flag "True" else "False"
		Int(number, _) => number.to_str()
		Frac(number, _) => number.to_str()
		Fixed(number) => number.to_str()
		Str(text) => "'${text}'"
		Bytes(bytes) => "bytes[${Str.join_with(bytes.map(|byte| byte.to_str()), " ")}]"
	}
}

embedded_bytes : U8 -> List(U8)
embedded_bytes = |_n| blob

embedded_text : U8 -> Str
embedded_text = |_n| source

staged_bytes : Str
staged_bytes = StagedBytes.describe(embedded_bytes)

staged_text : Str
staged_text = StagedBytes.describe(embedded_text)

main! = |_args| {
	echo!("${staged_bytes}\n")
	echo!("${staged_text}\n")
	Ok({})
}
