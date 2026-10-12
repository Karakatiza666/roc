# A file with no header is compiled with app wiring written on top of it, so a
# region the compiler hands to a stage counts lines from the file its author
# wrote rather than from what the compiler prepended.

Stage := {}.{
	## Where the staged function was written, as a stage would report it.
	where_written : Code(f) -> Str
	where_written = |code| {
		region = Code.ir(code).node_region()
		"${region.module_name}:${region.start_line.to_str()}:${region.start_column.to_str()}"
	}
}

double : F32 -> F32
double = |x| x * 2.0

main! = |_args| {
	echo!("${Stage.where_written(double)}\n")
	Ok({})
}
