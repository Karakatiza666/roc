# The glue between `time` and `sql`, a package of its own. Neither package
# knows the other: `Time` cannot gain SQL methods outside its own module, and
# `Sql.roc` does not change. This extension names `Time`'s operations and
# the type itself by the identity the compiler gives them, and says what each
# is in SQL.
#
# `Sql.Param` writes a `Time` as bytes that sort as its nanoseconds do, and a
# database compares two blobs byte by byte. So `<`, `>` and `=` on a `BLOB`
# column compute what `is_lt`, `is_gt` and `is_eq` compute. That is the claim
# this package makes; the translator cannot check it.
import sql.Sql
import time.Time

TimeSql :: {}.{
	time_proxy : Code.Proxy(Time)
	time_proxy = Code.proxy()

	extension : Sql.Extension
	extension = Sql.extension({
		prims: [
			{ prim: Code.prim(Time.is_lt), render: TimeSql.binary("<") },
			{ prim: Code.prim(Time.is_gt), render: TimeSql.binary(">") },
			{ prim: Code.prim(Time.is_eq), render: TimeSql.binary("=") },
		],
		types: [{ type: Code.type_id(TimeSql.time_proxy), column: "BLOB" }],
	})

	binary : Str -> ({ args : List(Str), evidence : List(Code.Evidence) } -> Try(Str, Str))
	binary = |op| |call| match call.args {
		[a, b] => Ok("(${a} ${op} ${b})")
		_ => Err("`${op}` takes two operands")
	}
}
