# Each op below gives a result that holds a part of its argument's
# allocation. After the op, the argument is not unique, so the next
# in-place op on the argument must copy it and leave the parts as they are.

header : Str -> { words : List(Str), loud : Bool }
header = |text| {
	words = text.split_on(" ")
	{ words, loud: text.with_ascii_uppercased().contains("ALPHA") }
}

main! = |args| {
	n = Str.inspect(List.len(args))
	h = header(Str.concat("-- replaces alpha_one beta_two ", n))
	echo!("${Str.inspect(h.words)} ${Str.inspect(h.loud)}\n")
	t1 = Str.concat("split on: a string long enough for the heap ", n)
	parts = t1.split_on(" ")
	up1 = t1.with_ascii_uppercased()
	echo!("${Str.inspect(parts)} ${up1}\n")
	t2 = Str.concat("split first: a string long enough for the heap ", n)
	first = t2.split_first(":")
	up2 = t2.with_ascii_uppercased()
	echo!("${Str.inspect(first)} ${up2}\n")
	t3 = Str.concat("split last: a string long enough for the heap ", n)
	last = t3.split_last(" ")
	up3 = t3.with_ascii_uppercased()
	echo!("${Str.inspect(last)} ${up3}\n")
	t4 = Str.concat("PREFIX-caseless: a string long enough for the heap ", n)
	dropped = t4.drop_prefix_caseless_ascii("prefix-")
	low4 = t4.with_ascii_lowercased()
	echo!("${Str.inspect(dropped)} ${low4}\n")
	t5 = Str.concat("to utf8: a string long enough for the heap ", n)
	bytes = t5.to_utf8()
	up5 = t5.with_ascii_uppercased()
	echo!("${Str.from_utf8_lossy(bytes)} ${up5}\n")
	b6 = Str.concat("from utf8: a string long enough for the heap ", n).to_utf8().append('!')
	s6 = Str.from_utf8(b6)
	b6x = b6.set(0, 'F') ?? []
	echo!("${s6 ?? "bad"} ${Str.from_utf8_lossy(b6x)}\n")
	t7 = Str.concat("drop prefix: a string long enough for the heap ", n)
	d7 = t7.drop_prefix("drop ")
	up7 = t7.with_ascii_uppercased()
	echo!("${d7} ${up7}\n")
	Ok({})
}
