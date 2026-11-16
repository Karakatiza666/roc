# A record field that is a refcounted tag union, matched only for its tag after
# a call that receives the record, or the field alone, while the record is
# still read afterwards. ARC releases or takes the field before the call, and
# the match reads the tag from the record's inline bytes.
Kind : [Plain, Named(Str)]

keep : { name : Str, kind : Kind } -> Str
keep = |t| match t.kind {
	Named(n) => n
	Plain => t.name
}

suffix : Kind -> Str
suffix = |kind| match kind {
	Named(n) => n
	Plain => "p"
}

## The record moves whole into `keep`, and `kind` is not read for its payload
## after the call.
after_whole : { name : Str, kind : Kind } -> Str
after_whole = |t| {
	part = keep(t)
	head = match t.kind {
		Named(_) => "named"
		Plain => "plain"
	}
	"${head} ${t.name} ${part}"
}

## `kind` alone moves into `suffix`, and is then read only for its tag.
after_take : { name : Str, kind : Kind } -> Str
after_take = |t| {
	part = suffix(t.kind)
	head = match t.kind {
		Named(_) => "named"
		Plain => "plain"
	}
	"${head} ${t.name} ${part}"
}

expect after_whole({ name: "n", kind: Named("k") }) == "named n k"
expect after_whole({ name: "n", kind: Plain }) == "plain n n"
expect after_take({ name: "n", kind: Named("k") }) == "named n k"
expect after_take({ name: "n", kind: Plain }) == "plain n p"
