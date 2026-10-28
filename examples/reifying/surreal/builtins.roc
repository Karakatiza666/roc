# Live check of the builtins that `Translate.roc` maps to SurrealQL.
#
# One table, `sample`, with rows chosen so that a naive mapping gives a wrong
# result: `straße`, U+200E, an empty needle, 2.5 and -2.5, a zero divisor and
# out-of-range integers. Each query is a Roc function. Its `-- roc:` reference
# is the same function run over the seed rows, as in `main.roc`.
#
# `roc builtins.roc` prints a script in the block format of `check.py`, which
# runs it after the script of `main.roc`.

app [main!] { surreal: "package.roc" }

import surreal.Surreal

Sample : {
	id : Str,
	text : Str,
	other : Str,
	n : I64,
	m : I64,
	k : I64,
	p : I64,
	v : I64,
	d : Dec,
	nums : List(I64),
	words : List(Str),
}

samples : Surreal.Table(Sample)
samples = Surreal.table("sample", |s| s)

sample_def : Surreal.Defined
sample_def = samples.define().done()

# ------------------------------------------------------------------- seeds

## A row with harmless values in every field. Each seed changes only the
## fields that its block reads. `k` is never 0 and `p` is never negative.
base : Sample
base = { id: "", text: "", other: "", n: 1, m: 1, k: 1, p: 0, v: 0, d: 0, nums: [], words: [] }

with_text : Str, Str, Str -> Sample
with_text = |id, text, other| { ..base, id, text, other }

with_ints : Str, I64, I64, I64, I64 -> Sample
with_ints = |id, n, m, k, p| { ..base, id, n, m, k, p }

with_dec : Str, Dec -> Sample
with_dec = |id, d| { ..base, id, d }

with_v : Str, I64 -> Sample
with_v = |id, v| { ..base, id, v }

with_nums : Str, List(I64) -> Sample
with_nums = |id, nums| { ..base, id, nums }

seed_samples : List(Sample)
seed_samples = [
	# case: `straße`, `ǆ` and an accent change in SQL `uppercase` but not in Roc
	with_text("t01", "Ada", "ada"),
	with_text("t02", "ÀDA é ß", "àda é ß"),
	with_text("t03", "straße", "STRASSE"),
	with_text("t04", "ǆ", "Ǆ"),
	with_text("t05", "a😀B", "A😀b"),
	with_text("t06", "  a b  ", " "),
	with_text("t07", "\t x\n", "x"),
	# trim: U+00A0, U+2003, U+3000, U+0085, U+200E and U+200F around a letter
	with_text("t08", "\u(A0)a\u(2003)", "a"),
	with_text("t09", "\u(3000)a\u(85)", "a"),
	with_text("t10", "\u(200E)a b\u(200F)", "a"),
	with_text("t11", "\u(200E)\u(200F)", "\u(200E)"),
	with_text("t12", "   ", " "),
	# drop_prefix and drop_suffix: a prefix, a suffix, no match, empty, the whole text
	with_text("t13", "héllo", "hé"),
	with_text("t14", "héllo", "llo"),
	with_text("t15", "héllo", "x"),
	with_text("t16", "héllo", ""),
	with_text("t17", "héllo", "héllo"),
	with_text("t18", "héé", "é"),
	# split_on and replace_each: an empty needle, adjacent separators, overlap
	with_text("t19", "a,b,,c", ","),
	with_text("t20", ",", ","),
	with_text("t21", "aaa", "aa"),
	with_text("t22", "abc", ""),
	with_text("t23", "😀", "😀"),
	with_text("t24", "abc", "b"),
	{ ..with_text("w01", "x", ""), words: [] },
	{ ..with_text("w02", "x", ""), words: ["a"] },
	{ ..with_text("w03", "x", ""), words: ["a", "", "é"] },
	with_ints("i01", -7, 3, 3, 2),
	with_ints("i02", 7, -3, -3, 3),
	with_ints("i03", -7, -3, -3, 0),
	with_ints("i04", 7, 3, 3, 1),
	with_ints("i05", 0, 0, 5, 0),
	with_ints("i06", 5, 0, 5, 2),
	with_ints("i07", -3, 2, 2, 3),
	with_ints("i08", 2, 1, 7, 10),
	with_ints("i09", -12, 4, 5, 1),
	with_dec("d01", 2.5),
	with_dec("d02", -2.5),
	with_dec("d03", 3.5),
	with_dec("d04", 0.5),
	with_dec("d05", 2.4),
	with_dec("d06", -2.7),
	with_dec("d07", 2.7),
	with_dec("d08", -0.5),
	with_dec("d09", 9223372036854775807.5),
	with_dec("d10", 9223372036854775808),
	with_v("v01", 255),
	with_v("v02", 256),
	with_v("v03", -1),
	with_v("v04", 3000000000),
	with_v("v05", 0),
	with_nums("l01", []),
	with_nums("l02", [7]),
	with_nums("l03", [4, 5, 6]),
]

# ------------------------------------------------------------------ queries

Case : { id : Str, up : Str, low : Str, same : Bool }

case_line : Sample -> Case
case_line = |s| { id: s.id, up: s.text.with_ascii_uppercased(), low: s.text.with_ascii_lowercased(), same: s.text.caseless_ascii_equals(s.other) }

Trimmed : { id : Str, both : Str, start : Str, end : Str }

trim_line : Sample -> Trimmed
trim_line = |s| { id: s.id, both: s.text.trim(), start: s.text.trim_start(), end: s.text.trim_end() }

Edited : { id : Str, drop_p : Str, drop_s : Str, rep : Str, pre : Str, joined : Str }

edit_line : Sample -> Edited
edit_line = |s| { id: s.id, drop_p: s.text.drop_prefix(s.other), drop_s: s.text.drop_suffix(s.other), rep: s.text.repeat(3), pre: s.text.with_prefix("a"), joined: Str.join_with(s.words, ",") }

Pieces : { id : Str, parts : List(Str), parts_lit : List(Str), swapped : Str, gone : Str }

piece_line : Sample -> Pieces
piece_line = |s| { id: s.id, parts: s.text.split_on(s.other), parts_lit: s.text.split_on(","), swapped: s.text.replace_each(s.other, "-"), gone: s.text.replace_each("", "-") }

Counted : { id : Str, bytes : I64 }

byte_line : Sample -> Counted
byte_line = |s| { id: s.id, bytes: s.text.count_utf8_bytes().to_i64_try().ok_or(-1) }

Ints : { id : Str, lo : I64, hi : I64, pw : I64, md : I64, mult : Bool, even : Bool, text : Str }

int_line : Sample -> Ints
int_line = |s| { id: s.id, lo: s.n.min(s.m), hi: s.n.max(s.m), pw: s.n.pow(s.p), md: s.n.mod_by(s.k), mult: s.n.is_multiple_of(s.m), even: s.n.is_even(), text: s.n.to_str() }

Decs : { id : Str, rnd : Dec, flr : Dec, cel : Dec, trn : Dec }

dec_line : Sample -> Decs
dec_line = |s| { id: s.id, rnd: s.d.round(), flr: s.d.floor(), cel: s.d.ceiling(), trn: s.d.trunc() }

Tried : { id : Str, u8 : I64, i32 : Bool, u64 : Bool, dec : I64 }

try_line : Sample -> Tried
try_line = |s| {
	id: s.id,
	u8: match s.v.to_u8_try() {
		Ok(x) => x.to_i64()
		Err(_) => -1
	},
	i32: s.v.to_i32_try().is_ok(),
	u64: s.v.to_u64_try().is_ok(),
	dec: s.d.to_i64_try().ok_or(-1),
}

Listed : {
	id : Str,
	first : I64,
	last : I64,
	get1 : I64,
	get5 : I64,
	hi : I64,
	lo : I64,
	take : List(I64),
	none : List(I64),
	drop : List(I64),
	drop_all : List(I64),
	cat : List(I64),
	rev : List(I64),
}

list_line : Sample -> Listed
list_line = |s| {
	id: s.id,
	first: s.nums.first().ok_or(-1),
	last: s.nums.last().ok_or(-1),
	get1: s.nums.get(1).ok_or(-1),
	get5: s.nums.get(5).ok_or(-1),
	hi: s.nums.max().ok_or(-1),
	lo: s.nums.min().ok_or(-1),
	take: s.nums.take_first(9),
	none: s.nums.take_first(0),
	drop: s.nums.drop_first(1),
	drop_all: s.nums.drop_first(9),
	cat: s.nums.concat(s.nums),
	rev: s.nums.rev(),
}

expect case_line(with_text("x", "straße", "")).up == "STRAßE"
expect trim_line(with_text("x", "\u(200E)a\u(200F)", "")).both == "a"
expect piece_line(with_text("x", "abc", "")).parts == ["abc"]
expect dec_line(with_dec("x", 2.5)).rnd == 3
expect dec_line(with_dec("x", -2.5)).rnd == -3
expect try_line(with_v("x", 256)).u8 == -1

# ------------------------------------------------- the package functions

# The functions of `Surreal` that Roc has no builtin for. A mirror has a Roc
# body, so its reference result is computed in Roc like the blocks above. A
# database-only function has no Roc body, so the expected rows are written by
# hand next to the seed rows, and each block says what it checks.

moment : Str -> Surreal.Datetime
moment = |text| match Surreal.datetime(text) {
	Ok(d) => d
	Err(_) => crash "a valid datetime"
}

## The text rows of the validators, the distances and the hashes. `kind` names
## the block that reads the row.
Phrase : { id : Str, kind : Str, text : Str, other : Str }

phrases : Surreal.Table(Phrase)
phrases = Surreal.table("phrase", |p| p)

phrase_def : Surreal.Defined
phrase_def = phrases.define().done()

phrase : Str, Str, Str, Str -> Phrase
phrase = |kind, id, text, other| { id, kind, text, other }

## The time rows. `n` is only read by `from_unix`.
Stamp : { id : Str, kind : Str, at : Surreal.Datetime, n : I64 }

stamps : Surreal.Table(Stamp)
stamps = Surreal.table("stamp", |s| s)

stamp_def : Surreal.Defined
stamp_def = stamps.define().done()

stamp : Str, Str, Str -> Stamp
stamp = |kind, id, text| { id, kind, at: moment(text), n: 0 }

## Two lists of numbers and two of words, for the `array::` functions.
Pair : { id : Str, a : List(I64), b : List(I64), left : List(Str), right : List(Str) }

pairs : Surreal.Table(Pair)
pairs = Surreal.table("pair", |p| p)

pair_def : Surreal.Defined
pair_def = pairs.define().done()

## A list of numbers for the statistics, and a value for the groups.
Reading : { id : Str, kind : Str, grp : Str, v : F64, scores : List(F64) }

readings : Surreal.Table(Reading)
readings = Surreal.table("reading", |r| r)

reading_def : Surreal.Defined
reading_def = readings.define().done()

## A row of the groups: `grp` and `v`, and no list.
grouped : Str, Str, F64 -> Reading
grouped = |id, grp, v| { id, kind: "group", grp, v, scores: [] }

## A row of the list statistics: a list, and no group.
scored : Str, List(F64) -> Reading
scored = |id, scores| { id, kind: "stats", grp: "", v: 0, scores }

## A row that links to a text row, and holds the id of another.
Ref : { id : Str, to : Surreal.Link(Phrase), mine : Surreal.Id(Phrase) }

refs : Surreal.Table(Ref)
refs = Surreal.table("ref", |r| r)

ref_def : Surreal.Defined
ref_def = refs.define().done()

## A row with defaults and a computed field that call `Rand`. The front desk
## types only the name, so the form has no other field. The unique indexes
## refuse the second row if a default ran once and not for each row.
Keyed : { id : Str, name : Str, uid : Str, uuid : Str, roll : I64, tag : Str }

KeyedForm : { id : Str, name : Str }

keyeds : Surreal.Table(Keyed)
keyeds = Surreal.table("keyed", |k| k)

keyed_forms : Surreal.Table(KeyedForm)
keyed_forms = Surreal.table("keyed", |k| k)

keyed_def : Surreal.Defined
keyed_def =
	keyeds.define()
		.unique(|k| k.uid)
		.unique(|k| k.uuid)
		.default_by(|k| k.uid, |_| Surreal.Rand.ulid())
		.default_by(|k| k.uuid, |_| Surreal.Rand.uuid())
		.default_by(|k| k.roll, |_| Surreal.Rand.int(1, 6))
		.computed(|k| k.tag, |_| Surreal.Rand.ulid())
		.done()

## Constants that a clause compares with a datetime. A constant is a literal in
## the clause, so these show how SurrealDB spells a fraction.
half_second : Surreal.Datetime
half_second = Surreal.Datetime.({ iso: "2026-03-04T05:06:07.5Z" })

milli_120 : Surreal.Datetime
milli_120 = Surreal.Datetime.({ iso: "2026-03-04T05:06:07.12Z" })

nano_123 : Surreal.Datetime
nano_123 = Surreal.Datetime.({ iso: "2026-03-04T05:06:07.123456789Z" })

whole_second : Surreal.Datetime
whole_second = Surreal.Datetime.({ iso: "2026-03-04T05:06:07Z" })

# ----------------------------------------------- validators: database only

Checked : { id : Str, text : Str, email : Bool, url : Bool, domain : Bool }

checked_cases : List(Checked)
checked_cases = [
	{ id: "c01", text: "ada@example.org", email: Bool.True, url: Bool.False, domain: Bool.False },
	{ id: "c02", text: "ada.example.org", email: Bool.False, url: Bool.False, domain: Bool.True },
	{ id: "c03", text: "a@b", email: Bool.True, url: Bool.False, domain: Bool.False },
	{ id: "c04", text: "", email: Bool.False, url: Bool.False, domain: Bool.False },
	{ id: "c05", text: "a b@c.d", email: Bool.False, url: Bool.False, domain: Bool.False },
	{ id: "c06", text: "ftp://a.b", email: Bool.False, url: Bool.True, domain: Bool.False },
	{ id: "c07", text: "https://example.org/x?y=1", email: Bool.False, url: Bool.True, domain: Bool.False },
	{ id: "c08", text: "localhost", email: Bool.False, url: Bool.False, domain: Bool.True },
	{ id: "c09", text: "a..b", email: Bool.False, url: Bool.False, domain: Bool.False },
]

checked_line : Phrase -> Checked
checked_line = |p| { id: p.id, text: p.text, email: Surreal.Text.is_email(p.text), url: Surreal.Text.is_url(p.text), domain: Surreal.Text.is_domain(p.text) }

Addressed : { id : Str, text : Str, ip : Bool, ipv4 : Bool, ipv6 : Bool }

addressed_cases : List(Addressed)
addressed_cases = [
	{ id: "a01", text: "127.0.0.1", ip: Bool.True, ipv4: Bool.True, ipv6: Bool.False },
	{ id: "a02", text: "::1", ip: Bool.True, ipv4: Bool.False, ipv6: Bool.True },
	{ id: "a03", text: "fe80::1", ip: Bool.True, ipv4: Bool.False, ipv6: Bool.True },
	{ id: "a04", text: "999.1.1.1", ip: Bool.False, ipv4: Bool.False, ipv6: Bool.False },
	{ id: "a05", text: "1.2.3", ip: Bool.False, ipv4: Bool.False, ipv6: Bool.False },
	{ id: "a06", text: "", ip: Bool.False, ipv4: Bool.False, ipv6: Bool.False },
]

addressed_line : Phrase -> Addressed
addressed_line = |p| { id: p.id, text: p.text, ip: Surreal.Text.is_ip(p.text), ipv4: Surreal.Text.is_ipv4(p.text), ipv6: Surreal.Text.is_ipv6(p.text) }

Identified : { id : Str, text : Str, uuid : Bool, ulid : Bool, semver : Bool }

identified_cases : List(Identified)
identified_cases = [
	{ id: "u01", text: "550e8400-e29b-41d4-a716-446655440000", uuid: Bool.True, ulid: Bool.False, semver: Bool.False },
	{ id: "u02", text: "550E8400E29B41D4A716446655440000", uuid: Bool.True, ulid: Bool.False, semver: Bool.False },
	{ id: "u03", text: "01ARZ3NDEKTSV4RRFFQ69G5FAV", uuid: Bool.False, ulid: Bool.True, semver: Bool.False },
	{ id: "u04", text: "01arz3ndektsv4rrffq69g5fav", uuid: Bool.False, ulid: Bool.True, semver: Bool.False },
	{ id: "u05", text: "1.2.3", uuid: Bool.False, ulid: Bool.False, semver: Bool.True },
	{ id: "u06", text: "1.2.3-beta+5", uuid: Bool.False, ulid: Bool.False, semver: Bool.True },
	{ id: "u07", text: "1.2", uuid: Bool.False, ulid: Bool.False, semver: Bool.False },
	{ id: "u08", text: "v1.2.3", uuid: Bool.False, ulid: Bool.False, semver: Bool.False },
	{ id: "u09", text: "", uuid: Bool.False, ulid: Bool.False, semver: Bool.False },
]

identified_line : Phrase -> Identified
identified_line = |p| { id: p.id, text: p.text, uuid: Surreal.Text.is_uuid(p.text), ulid: Surreal.Text.is_ulid(p.text), semver: Surreal.Text.is_semver(p.text) }

## The three Unicode checks are database only. `is_ascii` and `is_hexadecimal`
## are mirrors, so the expected rows call them in Roc.
Lettered : { id : Str, text : Str, alpha : Bool, alphanum : Bool, numeric : Bool, ascii : Bool, hex : Bool }

LetterCase : { id : Str, text : Str, alpha : Bool, alphanum : Bool, numeric : Bool }

letter_cases : List(LetterCase)
letter_cases = [
	{ id: "l01", text: "abé", alpha: Bool.True, alphanum: Bool.True, numeric: Bool.False },
	{ id: "l02", text: "ab1", alpha: Bool.False, alphanum: Bool.True, numeric: Bool.False },
	{ id: "l03", text: "", alpha: Bool.False, alphanum: Bool.False, numeric: Bool.False },
	{ id: "l04", text: "١٢٣", alpha: Bool.False, alphanum: Bool.True, numeric: Bool.True },
	{ id: "l05", text: "12", alpha: Bool.False, alphanum: Bool.True, numeric: Bool.True },
	{ id: "l06", text: "a b", alpha: Bool.False, alphanum: Bool.False, numeric: Bool.False },
	{ id: "l07", text: "FF0a", alpha: Bool.False, alphanum: Bool.True, numeric: Bool.False },
	{ id: "l08", text: "0xff", alpha: Bool.False, alphanum: Bool.True, numeric: Bool.False },
]

lettered_line : Phrase -> Lettered
lettered_line = |p| {
	id: p.id,
	text: p.text,
	alpha: Surreal.Text.is_alpha(p.text),
	alphanum: Surreal.Text.is_alphanum(p.text),
	numeric: Surreal.Text.is_numeric(p.text),
	ascii: Surreal.Text.is_ascii(p.text),
	hex: Surreal.Text.is_hexadecimal(p.text),
}

lettered_expected : List(Lettered)
lettered_expected = letter_cases.map(|c| { id: c.id, text: c.text, alpha: c.alpha, alphanum: c.alphanum, numeric: c.numeric, ascii: Surreal.Text.is_ascii(c.text), hex: Surreal.Text.is_hexadecimal(c.text) })

Placed : { id : Str, text : Str, lat : Bool, lon : Bool }

placed_cases : List(Placed)
placed_cases = [
	{ id: "g01", text: "-90", lat: Bool.True, lon: Bool.True },
	{ id: "g02", text: "91", lat: Bool.False, lon: Bool.True },
	{ id: "g03", text: "180", lat: Bool.False, lon: Bool.True },
	{ id: "g04", text: "45.5", lat: Bool.True, lon: Bool.True },
	{ id: "g05", text: "abc", lat: Bool.False, lon: Bool.False },
	{ id: "g06", text: "", lat: Bool.False, lon: Bool.False },
]

placed_line : Phrase -> Placed
placed_line = |p| { id: p.id, text: p.text, lat: Surreal.Text.is_latitude(p.text), lon: Surreal.Text.is_longitude(p.text) }

## A text and the pattern that it is read with. A date without a time is not a datetime.
Dated : { id : Str, text : Str, other : Str, ok : Bool }

dated_cases : List(Dated)
dated_cases = [
	{ id: "d01", text: "2020-01-01T00:00:00Z", other: "%Y-%m-%dT%H:%M:%SZ", ok: Bool.True },
	{ id: "d02", text: "2020-01-01", other: "%Y-%m-%dT%H:%M:%SZ", ok: Bool.False },
	{ id: "d03", text: "2020-01-01", other: "%Y-%m-%d", ok: Bool.False },
	{ id: "d04", text: "x", other: "%Y", ok: Bool.False },
]

dated_line : Phrase -> Dated
dated_line = |p| { id: p.id, text: p.text, other: p.other, ok: Surreal.Text.is_datetime(p.text, p.other) }

## `matches` takes Rust regex syntax, and a pattern that is not anchored finds a part of the text.
Matched : { id : Str, text : Str, other : Str, ok : Bool }

matched_cases : List(Matched)
matched_cases = [
	{ id: "m01", text: "abc", other: "^a.c$", ok: Bool.True },
	{ id: "m02", text: "xbc", other: "^a", ok: Bool.False },
	{ id: "m03", text: "abc", other: "b", ok: Bool.True },
	{ id: "m04", text: "", other: "^$", ok: Bool.True },
]

matched_line : Phrase -> Matched
matched_line = |p| { id: p.id, text: p.text, other: p.other, ok: Surreal.Text.matches(p.text, p.other) }

# ------------------------------------ similarity and distance: database only

Similar : { id : Str, text : Str, other : Str, jaro : F64, winkler : F64 }

similar_cases : List(Similar)
similar_cases = [
	{ id: "s01", text: "martha", other: "marhta", jaro: 0.9444444444444445, winkler: 0.9611111111111111 },
	{ id: "s02", text: "", other: "x", jaro: 0, winkler: 0 },
	{ id: "s03", text: "a", other: "a", jaro: 1, winkler: 1 },
	{ id: "s04", text: "abc", other: "xyz", jaro: 0, winkler: 0 },
]

similar_line : Phrase -> Similar
similar_line = |p| { id: p.id, text: p.text, other: p.other, jaro: Surreal.Text.similarity_jaro(p.text, p.other), winkler: Surreal.Text.similarity_jaro_winkler(p.text, p.other) }

## The distances count characters, not bytes. `normalized` is a similarity: 1 for equal texts.
Distant : { id : Str, text : Str, other : Str, lev : I64, damerau : I64, normalized : F64 }

distant_cases : List(Distant)
distant_cases = [
	{ id: "e01", text: "kitten", other: "sitting", lev: 3, damerau: 3, normalized: 0.5714285714285714 },
	{ id: "e02", text: "é", other: "e", lev: 1, damerau: 1, normalized: 0 },
	{ id: "e03", text: "ab", other: "ba", lev: 2, damerau: 1, normalized: 0 },
	{ id: "e04", text: "", other: "abc", lev: 3, damerau: 3, normalized: 0 },
	{ id: "e05", text: "same", other: "same", lev: 0, damerau: 0, normalized: 1 },
]

distant_line : Phrase -> Distant
distant_line = |p| {
	id: p.id,
	text: p.text,
	other: p.other,
	lev: Surreal.Text.distance_levenshtein(p.text, p.other),
	damerau: Surreal.Text.distance_damerau_levenshtein(p.text, p.other),
	normalized: Surreal.Text.distance_normalized_levenshtein(p.text, p.other),
}

# ------------------------------------------------------------------ hashes

Digest : { id : Str, text : Str, sha256 : Str, blake3 : Str }

digest_line : Phrase -> Digest
digest_line = |p| { id: p.id, text: p.text, sha256: Surreal.Hash.sha256(p.text), blake3: Surreal.Hash.blake3(p.text) }

old_digests : List({ id : Str, text : Str, md5 : Str, sha1 : Str, sha512 : Str })
old_digests = [
	{ id: "h01", text: "abc", md5: "900150983cd24fb0d6963f7d28e17f72", sha1: "a9993e364706816aba3e25717850c26c9cd0d89d", sha512: "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f" },
	{ id: "h02", text: "", md5: "d41d8cd98f00b204e9800998ecf8427e", sha1: "da39a3ee5e6b4b0d3255bfef95601890afd80709", sha512: "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e" },
	{ id: "h03", text: "é", md5: "66ddcd97cfdeabb2f6fb8a999b4bc76f", sha1: "bf15be717ac1b080b4f1c456692825891ff5073d", sha512: "9e2ad28633f24451bd4f3c1cb20586a21a44c3aeedbdc01b9cc8fa72917ea7bd689c82b8bf1fef89b911cf8cc46fa2c1ccc10087b2094fd4d3350ecd88526a2c" },
]

OldDigest : { id : Str, text : Str, md5 : Str, sha1 : Str, sha512 : Str }

old_digest_line : Phrase -> OldDigest
old_digest_line = |p| { id: p.id, text: p.text, md5: Surreal.Hash.md5(p.text), sha1: Surreal.Hash.sha1(p.text), sha512: Surreal.Hash.sha512(p.text) }

# ------------------------------------------------------------------ arrays

Sets : { id : Str, distinct : List(I64), union : List(I64), intersect : List(I64), complement : List(I64), words : List(Str), shared : List(Str) }

set_line : Pair -> Sets
set_line = |p| {
	id: p.id,
	distinct: Surreal.Array.distinct(p.a),
	union: Surreal.Array.union(p.a, p.b),
	intersect: Surreal.Array.intersect(p.a, p.b),
	complement: Surreal.Array.complement(p.a, p.b),
	words: Surreal.Array.distinct(p.left),
	shared: Surreal.Array.intersect(p.left, p.right),
}

pair : Str, List(I64), List(I64), List(Str), List(Str) -> Pair
pair = |id, a, b, left, right| { id, a, b, left, right }

seed_pairs : List(Pair)
seed_pairs = [
	pair("p1", [3, 1, 3, 2, 1], [2, 3], ["b", "B", "a", "é", "a"], ["a", "é", "é"]),
	pair("p2", [], [], [], []),
	pair("p3", [1, 1], [1, 2, 2], ["x"], ["y"]),
	pair("p4", [3, 1, 2, 3], [2], [], ["a"]),
	pair("p5", [1, 2, 3], [3, 4, 4], ["a", "A"], ["A", "a"]),
	pair("p6", [1, 1, 2], [2, 3, 3], ["é", "é"], []),
]

# -------------------------------------------------------------------- time

seed_stamps : List(Stamp)
seed_stamps = [
	# `now`: the past is selected, the far future is not
	stamp("now", "n01", "2026-03-04T05:06:07Z"),
	stamp("now", "n02", "1970-01-01T00:00:00Z"),
	stamp("now", "n03", "2999-01-01T00:00:00Z"),
	stamp("now", "n04", "2999-12-31T23:59:59.5Z"),
	# `buckets`: a whole hour, a half, one second before it, a fraction
	stamp("buckets", "b01", "2026-03-04T05:06:07Z"),
	stamp("buckets", "b02", "2026-03-04T05:36:07Z"),
	stamp("buckets", "b03", "2026-03-04T05:30:00Z"),
	stamp("buckets", "b04", "2026-03-04T05:29:59Z"),
	stamp("buckets", "b05", "2026-03-04T06:00:00Z"),
	stamp("buckets", "b06", "2026-03-04T05:00:00.5Z"),
	# `group`
	stamp("group", "g01", "2026-03-04T05:06:07Z"),
	stamp("group", "g02", "2026-12-31T23:59:59.5Z"),
	# `plus`
	stamp("plus", "a01", "2026-03-04T05:06:07Z"),
	stamp("plus", "a02", "2026-03-01T00:00:00.5Z"),
	stamp("plus", "a03", "2024-03-01T00:00:00Z"),
	# `parts`, `epoch` and `format`: a leap day, the end of a year, before 1970, a fraction
	stamp("parts", "p01", "2026-03-04T05:06:07Z"),
	stamp("parts", "p02", "2026-12-31T23:59:59.5Z"),
	stamp("parts", "p03", "2024-02-29T12:00:00Z"),
	stamp("parts", "p04", "1969-12-31T23:59:59.5Z"),
	stamp("parts", "p05", "2026-03-04T05:06:07.123456789Z"),
	# `from_unix`
	{ ..stamp("from_unix", "u01", "2026-03-04T05:06:07Z"), n: 1772600767 },
	{ ..stamp("from_unix", "u02", "1970-01-01T00:00:00Z"), n: 0 },
	{ ..stamp("from_unix", "u03", "1969-12-31T23:59:59Z"), n: -1 },
	# `frac`: one instant written three ways, other fractions, and a whole second
	stamp("frac", "f01", "2026-03-04T05:06:07.5Z"),
	stamp("frac", "f02", "2026-03-04T05:06:07.500Z"),
	stamp("frac", "f03", "2026-03-04T05:06:07.120Z"),
	stamp("frac", "f04", "2026-03-04T05:06:07.123456789Z"),
	stamp("frac", "f05", "2026-03-04T05:06:07.1Z"),
	stamp("frac", "f06", "2026-03-04T05:06:07Z"),
]

expect moment("2026-03-04T05:06:07.500Z") == half_second
expect moment("2026-03-04T05:06:07.120Z") == milli_120
expect moment("2026-03-04T05:06:07.123456789Z") == nano_123
expect moment("2026-03-04T05:06:07.123456789Z").to_unix_nanos() == 1772600767123456789
expect Surreal.Datetime.from_unix_nanos(1772600767123456789) == Ok(nano_123)
expect moment("1969-12-31T23:59:59.5Z").to_unix_nanos() == -500000000

Buckets : { id : Str, at : Surreal.Datetime, floor : Surreal.Datetime, ceil : Surreal.Datetime, round : Surreal.Datetime, quarter : Surreal.Datetime }

bucket_line : Stamp -> Buckets
bucket_line = |s| {
	id: s.id,
	at: s.at,
	floor: Surreal.Time.floor(s.at, Surreal.Time.hours(1)),
	ceil: Surreal.Time.ceil(s.at, Surreal.Time.hours(1)),
	round: Surreal.Time.round(s.at, Surreal.Time.hours(1)),
	quarter: Surreal.Time.floor(s.at, Surreal.Time.mins(15)),
}

## An hour is 3600 seconds, a quarter is 900. `round` takes a half up.
bucket_expected : List(Buckets)
bucket_expected = [
	{ id: "b01", at: moment("2026-03-04T05:06:07Z"), floor: moment("2026-03-04T05:00:00Z"), ceil: moment("2026-03-04T06:00:00Z"), round: moment("2026-03-04T05:00:00Z"), quarter: moment("2026-03-04T05:00:00Z") },
	{ id: "b02", at: moment("2026-03-04T05:36:07Z"), floor: moment("2026-03-04T05:00:00Z"), ceil: moment("2026-03-04T06:00:00Z"), round: moment("2026-03-04T06:00:00Z"), quarter: moment("2026-03-04T05:30:00Z") },
	{ id: "b03", at: moment("2026-03-04T05:30:00Z"), floor: moment("2026-03-04T05:00:00Z"), ceil: moment("2026-03-04T06:00:00Z"), round: moment("2026-03-04T06:00:00Z"), quarter: moment("2026-03-04T05:30:00Z") },
	{ id: "b04", at: moment("2026-03-04T05:29:59Z"), floor: moment("2026-03-04T05:00:00Z"), ceil: moment("2026-03-04T06:00:00Z"), round: moment("2026-03-04T05:00:00Z"), quarter: moment("2026-03-04T05:15:00Z") },
	{ id: "b05", at: moment("2026-03-04T06:00:00Z"), floor: moment("2026-03-04T06:00:00Z"), ceil: moment("2026-03-04T06:00:00Z"), round: moment("2026-03-04T06:00:00Z"), quarter: moment("2026-03-04T06:00:00Z") },
	{ id: "b06", at: moment("2026-03-04T05:00:00.5Z"), floor: moment("2026-03-04T05:00:00Z"), ceil: moment("2026-03-04T06:00:00Z"), round: moment("2026-03-04T05:00:00Z"), quarter: moment("2026-03-04T05:00:00Z") },
]

TimeGroups : { id : Str, year : Surreal.Datetime, month : Surreal.Datetime, day : Surreal.Datetime, hour : Surreal.Datetime, minute : Surreal.Datetime, second : Surreal.Datetime }

group_line : Stamp -> TimeGroups
group_line = |s| {
	id: s.id,
	year: Surreal.Time.group(s.at, Year),
	month: Surreal.Time.group(s.at, Month),
	day: Surreal.Time.group(s.at, Day),
	hour: Surreal.Time.group(s.at, Hour),
	minute: Surreal.Time.group(s.at, Minute),
	second: Surreal.Time.group(s.at, Second),
}

time_group_expected : List(TimeGroups)
time_group_expected = [
	{ id: "g01", year: moment("2026-01-01T00:00:00Z"), month: moment("2026-03-01T00:00:00Z"), day: moment("2026-03-04T00:00:00Z"), hour: moment("2026-03-04T05:00:00Z"), minute: moment("2026-03-04T05:06:00Z"), second: moment("2026-03-04T05:06:07Z") },
	{ id: "g02", year: moment("2026-01-01T00:00:00Z"), month: moment("2026-12-01T00:00:00Z"), day: moment("2026-12-31T00:00:00Z"), hour: moment("2026-12-31T23:00:00Z"), minute: moment("2026-12-31T23:59:00Z"), second: moment("2026-12-31T23:59:59Z") },
]

Shifted : { id : Str, later : Surreal.Datetime, earlier : Surreal.Datetime, week : Surreal.Datetime }

shift_line : Stamp -> Shifted
shift_line = |s| {
	id: s.id,
	later: Surreal.Time.plus(s.at, Surreal.Time.hours(1)),
	earlier: Surreal.Time.minus(s.at, Surreal.Time.days(1)),
	week: Surreal.Time.plus(s.at, Surreal.Time.weeks(1)),
}

shift_expected : List(Shifted)
shift_expected = [
	{ id: "a01", later: moment("2026-03-04T06:06:07Z"), earlier: moment("2026-03-03T05:06:07Z"), week: moment("2026-03-11T05:06:07Z") },
	{ id: "a02", later: moment("2026-03-01T01:00:00.5Z"), earlier: moment("2026-02-28T00:00:00.5Z"), week: moment("2026-03-08T00:00:00.5Z") },
	{ id: "a03", later: moment("2024-03-01T01:00:00Z"), earlier: moment("2024-02-29T00:00:00Z"), week: moment("2024-03-08T00:00:00Z") },
]

## The parts of a time are mirrors, so Roc computes the expected rows.
Parts : { id : Str, year : I64, month : I64, day : I64, hour : I64, minute : I64, second : I64 }

part_line : Stamp -> Parts
part_line = |s| {
	id: s.id,
	year: Surreal.Time.year(s.at),
	month: Surreal.Time.month(s.at),
	day: Surreal.Time.day(s.at),
	hour: Surreal.Time.hour(s.at),
	minute: Surreal.Time.minute(s.at),
	second: Surreal.Time.second(s.at),
}

## Monday is 1 and Sunday is 7, the week is the ISO week, and a day of the year counts from 1.
Calendar : { id : Str, wday : I64, yday : I64, week : I64 }

calendar_line : Stamp -> Calendar
calendar_line = |s| { id: s.id, wday: Surreal.Time.wday(s.at), yday: Surreal.Time.yday(s.at), week: Surreal.Time.week(s.at) }

calendar_expected : List(Calendar)
calendar_expected = [
	{ id: "p01", wday: 3, yday: 63, week: 10 },
	{ id: "p02", wday: 4, yday: 365, week: 53 },
	{ id: "p03", wday: 4, yday: 60, week: 9 },
	{ id: "p04", wday: 3, yday: 365, week: 1 },
	{ id: "p05", wday: 3, yday: 63, week: 10 },
]

## The seconds, milliseconds, microseconds and nanoseconds since 1970, rounded down.
Epoch : { id : Str, unix : I64, millis : I64, micros : I64, nano : I64 }

epoch_line : Stamp -> Epoch
epoch_line = |s| {
	id: s.id,
	unix: Surreal.Time.unix(s.at),
	millis: Surreal.Time.unix_millis(s.at),
	micros: Surreal.Time.unix_micros(s.at),
	nano: Surreal.Time.nano(s.at),
}

epoch_expected : List(Epoch)
epoch_expected = [
	{ id: "p01", unix: 1772600767, millis: 1772600767000, micros: 1772600767000000, nano: 1772600767000000000 },
	{ id: "p02", unix: 1798761599, millis: 1798761599500, micros: 1798761599500000, nano: 1798761599500000000 },
	{ id: "p03", unix: 1709208000, millis: 1709208000000, micros: 1709208000000000, nano: 1709208000000000000 },
	{ id: "p04", unix: -1, millis: -500, micros: -500000, nano: -500000000 },
	{ id: "p05", unix: 1772600767, millis: 1772600767123, micros: 1772600767123456, nano: 1772600767123456789 },
]

Written : { id : Str, ymd : Str, day : Str }

written_line : Stamp -> Written
written_line = |s| { id: s.id, ymd: Surreal.Time.format(s.at, "%Y/%m/%d"), day: Surreal.Time.format(s.at, "%A") }

written_expected : List(Written)
written_expected = [
	{ id: "p01", ymd: "2026/03/04", day: "Wednesday" },
	{ id: "p02", ymd: "2026/12/31", day: "Thursday" },
	{ id: "p03", ymd: "2024/02/29", day: "Thursday" },
	{ id: "p04", ymd: "1969/12/31", day: "Wednesday" },
	{ id: "p05", ymd: "2026/03/04", day: "Wednesday" },
]

FromUnix : { id : Str, n : I64, at : Surreal.Datetime }

unix_line : Stamp -> FromUnix
unix_line = |s| { id: s.id, n: s.n, at: Surreal.Time.from_unix(s.n) }

unix_expected : List(FromUnix)
unix_expected = [
	{ id: "u01", n: 1772600767, at: moment("2026-03-04T05:06:07Z") },
	{ id: "u02", n: 0, at: moment("1970-01-01T00:00:00Z") },
	{ id: "u03", n: -1, at: moment("1969-12-31T23:59:59Z") },
]

## SurrealDB prints a fraction with 3, 6 or 9 digits (`.500Z`) and Roc without
## trailing zeros (`.5Z`), so a datetime is compared as a datetime. Roc computes
## the expected rows with its own `==`.
Fractions : { id : Str, half : Bool, milli : Bool, nano : Bool, whole : Bool, not_half : Bool }

fraction_line : Stamp -> Fractions
fraction_line = |s| { id: s.id, half: s.at == half_second, milli: s.at == milli_120, nano: s.at == nano_123, whole: s.at == whole_second, not_half: s.at != half_second }

# --------------------------------------------------------------- statistics

seed_readings : List(Reading)
seed_readings = [
	scored("r01", [1, 2, 3, 4]),
	scored("r02", [0.1, 0.2, 0.3]),
	scored("r03", [0.1, 0.7, 0.2, 0.4, 0.9]),
	scored("r04", [10, 20]),
	scored("r05", [2, 4, 4, 4, 5, 5, 7, 9]),
	scored("r06", [1.5, 2.5]),
	{ ..scored("r07", [5]), kind: "means" },
	{ ..scored("r08", [10000000000000000, 1, -10000000000000000]), kind: "means" },
	grouped("v01", "a", 1),
	grouped("v02", "a", 2),
	grouped("v03", "b", 4),
	grouped("v04", "b", 5),
	grouped("v05", "b", 6),
	grouped("v06", "b", 9),
	grouped("v07", "c", 2),
	grouped("v08", "c", 4),
]

## `mean` is a mirror: Roc sums from the left, as SurrealDB does.
Means : { id : Str, mean : F64 }

mean_line : Reading -> Means
mean_line = |r| { id: r.id, mean: Surreal.Math.mean(r.scores) }

Spread : { id : Str, median : F64, stddev : F64, variance : F64, p90 : F64, p50 : F64 }

spread_line : Reading -> Spread
spread_line = |r| {
	id: r.id,
	median: Surreal.Math.median(r.scores),
	stddev: Surreal.Math.stddev(r.scores),
	variance: Surreal.Math.variance(r.scores),
	p90: Surreal.Math.percentile(r.scores, 90),
	p50: Surreal.Math.percentile(r.scores, 50),
}

## The sample deviation and variance, and a percentile that is interpolated.
spread_expected : List(Spread)
spread_expected = [
	{ id: "r01", median: 2.5, stddev: 1.2909944487358056, variance: 1.6666666666666667, p90: 3.7, p50: 2.5 },
	{ id: "r02", median: 0.2, stddev: 0.09999999999999999, variance: 0.009999999999999998, p90: 0.28, p50: 0.2 },
	{ id: "r03", median: 0.4, stddev: 0.3361547262794322, variance: 0.113, p90: 0.8200000000000001, p50: 0.4 },
	{ id: "r04", median: 15, stddev: 7.0710678118654755, variance: 50, p90: 19, p50: 15 },
	{ id: "r05", median: 4.5, stddev: 2.138089935299395, variance: 4.571428571428571, p90: 7.6, p50: 4.5 },
	{ id: "r06", median: 2, stddev: 0.7071067811865476, variance: 0.5, p90: 2.4, p50: 2 },
]

Stats : { grp : Str, avg : F64, mid : F64, sd : F64, spread : F64, total : F64, n : I64 }

## Each statistic reads the same `rows.map(..)`, and each writes its own aggregate.
group_stat : Str, List(Reading) -> Stats
group_stat = |grp, rows| {
	values = rows.map(|r| r.v)
	{
		grp,
		avg: Surreal.Math.mean(values),
		mid: Surreal.Math.median(values),
		sd: Surreal.Math.stddev(values),
		spread: Surreal.Math.variance(values),
		total: values.sum(),
		n: rows.len().to_i64_wrap(),
	}
}

stats_expected : List(Stats)
stats_expected = [
	{ grp: "a", avg: 1.5, mid: 1.5, sd: 0.7071067811865476, spread: 0.5, total: 3, n: 2 },
	{ grp: "b", avg: 6, mid: 5.5, sd: 2.160246899469287, spread: 4.666666666666667, total: 24, n: 4 },
	{ grp: "c", avg: 3, mid: 3, sd: 1.4142135623730951, spread: 2, total: 6, n: 2 },
]

## Each aggregate writes its own `rows.map(..)`.
Averages : { grp : Str, avg : F64, total : F64 }

average_line : Str, List(Reading) -> Averages
average_line = |grp, rows| { grp, avg: Surreal.Math.mean(rows.map(|r| r.v)), total: rows.map(|r| r.v).sum() }

average_expected : List(Averages)
average_expected = [
	{ grp: "a", avg: 1.5, total: 3 },
	{ grp: "b", avg: 6, total: 24 },
	{ grp: "c", avg: 3, total: 6 },
]

# ----------------------------------------------------- Rand and Id.table

## Every generated value has the shape of its kind. The values themselves differ on each run.
Shaped : { id : Str, name : Str, uid_ok : Bool, uuid_ok : Bool, roll_ok : Bool, tag_ok : Bool }

shaped_line : Keyed -> Shaped
shaped_line = |k| { id: k.id, name: k.name, uid_ok: Surreal.Text.is_ulid(k.uid), uuid_ok: Surreal.Text.is_uuid(k.uuid), roll_ok: k.roll >= 1 and k.roll <= 6, tag_ok: Surreal.Text.is_ulid(k.tag) }

shaped_expected : List(Shaped)
shaped_expected = [
	{ id: "k1", name: "Ada", uid_ok: Bool.True, uuid_ok: Bool.True, roll_ok: Bool.True, tag_ok: Bool.True },
	{ id: "k2", name: "Bo", uid_ok: Bool.True, uuid_ok: Bool.True, roll_ok: Bool.True, tag_ok: Bool.True },
	{ id: "k3", name: "Cy", uid_ok: Bool.True, uuid_ok: Bool.True, roll_ok: Bool.True, tag_ok: Bool.True },
]

## An update sets new random values: the roll becomes 9, and `uid` is another ulid.
## The call is written in the lambda of the update: a named function that calls
## `Rand` with constant arguments runs the call when it compiles, and stops.
Rerolled : { id : Str, roll : I64, uid_ok : Bool }

reroll_line : Keyed -> Rerolled
reroll_line = |k| { id: k.id, roll: k.roll, uid_ok: Surreal.Text.is_ulid(k.uid) }

reroll_expected : List(Rerolled)
reroll_expected = [
	{ id: "k1", roll: 9, uid_ok: Bool.True },
	{ id: "k2", roll: 9, uid_ok: Bool.True },
	{ id: "k3", roll: 9, uid_ok: Bool.True },
]

Linked : { id : Str, to_table : Str, to_key : Str, mine_table : Str }

link_line : Ref -> Linked
link_line = |r| { id: r.id, to_table: Surreal.Id.table(r.to.id()), to_key: r.to.id().key(), mine_table: Surreal.Id.table(r.mine) }

seed_refs : List(Ref)
seed_refs = [
	{ id: "r1", to: phrases.link("c01"), mine: phrases.id("c02") },
	{ id: "r2", to: phrases.link("u03"), mine: phrases.id("h01") },
]

seed_phrases : List(Phrase)
seed_phrases = List.join([
	checked_cases.map(|c| phrase("checks", c.id, c.text, "")),
	addressed_cases.map(|c| phrase("addresses", c.id, c.text, "")),
	identified_cases.map(|c| phrase("identifiers", c.id, c.text, "")),
	letter_cases.map(|c| phrase("letters", c.id, c.text, "")),
	placed_cases.map(|c| phrase("places", c.id, c.text, "")),
	dated_cases.map(|c| phrase("dates", c.id, c.text, c.other)),
	matched_cases.map(|c| phrase("patterns", c.id, c.text, c.other)),
	similar_cases.map(|c| phrase("similar", c.id, c.text, c.other)),
	distant_cases.map(|c| phrase("distances", c.id, c.text, c.other)),
	old_digests.map(|c| phrase("hashes", c.id, c.text, "")),
])

in_kind : Str -> List(Phrase)
in_kind = |kind| seed_phrases.keep_if(|p| p.kind == kind)

stamps_of : Str -> List(Stamp)
stamps_of = |kind| seed_stamps.keep_if(|s| s.kind == kind)

# --------------------------------------------------------------- the script

## One block: the statement, then the Roc result for the same question.
block : Str, Try(Surreal.Statement, Surreal.Error), Try(Str, Surreal.Error) -> Str
block = |header, statement, reference| match (statement, reference) {
	(Ok(s), Ok(literal)) => s.block(header, ["-- roc: ${literal}"])
	(Err(e), _) | (_, Err(e)) => "-- unsupported ${header}: ${Str.inspect(e)}"
}

## A write, then the rows it changed.
then_read : Try(Surreal.Statement, Surreal.Error), Try(Surreal.Statement, Surreal.Error) -> Try(Surreal.Statement, Surreal.Error)
then_read = |first, second| match (first, second) {
	(Ok(a), Ok(b)) => a.then(b)
	(Err(e), _) | (_, Err(e)) => Err(e)
}

package_queries : List(Str)
package_queries = [
	block("-- query: text_checks", Surreal.from(phrases).filter(|p| p.kind == "checks").select(checked_line).bind({}), Surreal.literal(checked_cases)),
	block("-- query: text_addresses", Surreal.from(phrases).filter(|p| p.kind == "addresses").select(addressed_line).bind({}), Surreal.literal(addressed_cases)),
	block("-- query: text_identifiers", Surreal.from(phrases).filter(|p| p.kind == "identifiers").select(identified_line).bind({}), Surreal.literal(identified_cases)),
	block("-- query: text_unicode", Surreal.from(phrases).filter(|p| p.kind == "letters").select(lettered_line).bind({}), Surreal.literal(lettered_expected)),
	block("-- query: text_places", Surreal.from(phrases).filter(|p| p.kind == "places").select(placed_line).bind({}), Surreal.literal(placed_cases)),
	block("-- query: text_dates", Surreal.from(phrases).filter(|p| p.kind == "dates").select(dated_line).bind({}), Surreal.literal(dated_cases)),
	block("-- query: text_pattern", Surreal.from(phrases).filter(|p| p.kind == "patterns").select(matched_line).bind({}), Surreal.literal(matched_cases)),
	block("-- query: text_similarity", Surreal.from(phrases).filter(|p| p.kind == "similar").select(similar_line).bind({}), Surreal.literal(similar_cases)),
	block("-- query: text_distance", Surreal.from(phrases).filter(|p| p.kind == "distances").select(distant_line).bind({}), Surreal.literal(distant_cases)),
	block("-- query: hashes", Surreal.from(phrases).filter(|p| p.kind == "hashes").select(digest_line).bind({}), Surreal.literal(in_kind("hashes").map(digest_line))),
	block("-- query: hashes_old", Surreal.from(phrases).filter(|p| p.kind == "hashes").select(old_digest_line).bind({}), Surreal.literal(old_digests)),
	block("-- query: arrays", Surreal.from(pairs).select(set_line).bind({}), Surreal.literal(seed_pairs.map(set_line))),
	block("-- query: now_filter", Surreal.from(stamps).filter(|s| s.kind == "now" and s.at < Surreal.Time.now()).select_value(|s| s.id).bind({}), Surreal.literal(["n01", "n02"])),
	block("-- query: now_future", Surreal.from(stamps).filter(|s| s.kind == "now" and Surreal.Time.now() < s.at).select_value(|s| s.id).bind({}), Surreal.literal(["n03", "n04"])),
	block("-- query: time_buckets", Surreal.from(stamps).filter(|s| s.kind == "buckets").select(bucket_line).bind({}), Surreal.literal(bucket_expected)),
	block("-- query: time_group", Surreal.from(stamps).filter(|s| s.kind == "group").select(group_line).bind({}), Surreal.literal(time_group_expected)),
	block("-- query: time_plus", Surreal.from(stamps).filter(|s| s.kind == "plus").select(shift_line).bind({}), Surreal.literal(shift_expected)),
	block("-- query: time_parts", Surreal.from(stamps).filter(|s| s.kind == "parts").select(part_line).bind({}), Surreal.literal(stamps_of("parts").map(part_line))),
	block("-- query: time_calendar", Surreal.from(stamps).filter(|s| s.kind == "parts").select(calendar_line).bind({}), Surreal.literal(calendar_expected)),
	block("-- query: time_epoch", Surreal.from(stamps).filter(|s| s.kind == "parts").select(epoch_line).bind({}), Surreal.literal(epoch_expected)),
	block("-- query: time_format", Surreal.from(stamps).filter(|s| s.kind == "parts").select(written_line).bind({}), Surreal.literal(written_expected)),
	block("-- query: time_from_unix", Surreal.from(stamps).filter(|s| s.kind == "from_unix").select(unix_line).bind({}), Surreal.literal(unix_expected)),
	block("-- query: datetime_fraction", Surreal.from(stamps).filter(|s| s.kind == "frac").select(fraction_line).bind({}), Surreal.literal(stamps_of("frac").map(fraction_line))),
	block("-- query: datetime_unequal", Surreal.from(stamps).filter(|s| s.kind == "frac" and s.at != half_second).select_value(|s| s.id).bind({}), Surreal.literal(["f03", "f04", "f05", "f06"])),
	block("-- query: stats_mean", Surreal.from(readings).filter(|r| r.kind != "group").select(mean_line).bind({}), Surreal.literal(seed_readings.keep_if(|r| r.kind != "group").map(mean_line))),
	block("-- query: stats_spread", Surreal.from(readings).filter(|r| r.kind == "stats").select(spread_line).bind({}), Surreal.literal(spread_expected)),
	block("-- query: group_shared_map", Surreal.from(readings).filter(|r| r.kind == "group").group_by(|r| r.grp).aggregate(group_stat).bind({}), Surreal.literal(stats_expected)),
	block("-- query: group_means", Surreal.from(readings).filter(|r| r.kind == "group").group_by(|r| r.grp).aggregate(average_line).bind({}), Surreal.literal(average_expected)),
	block("-- query: ids", Surreal.from(refs).select(link_line).bind({}), Surreal.literal(seed_refs.map(link_line))),
	block(
		"-- write: rand_defaults",
		then_read(
			then_read(then_read(keyed_forms.create({ id: "k1", name: "Ada" }), keyed_forms.create({ id: "k2", name: "Bo" })), keyed_forms.create({ id: "k3", name: "Cy" })),
			Surreal.from(keyeds).select(shaped_line).bind({}),
		),
		Surreal.literal(shaped_expected),
	),
	block(
		"-- write: rand_update",
		then_read(keyeds.update(|k| k.roll >= 0, |k| { ..k, roll: Surreal.Rand.int(9, 9), uid: Surreal.Rand.ulid() }).bind({}), Surreal.from(keyeds).select(reroll_line).bind({})),
		Surreal.literal(reroll_expected),
	),
]

schema_block : Str
schema_block = match Surreal.schema([sample_def, phrase_def, stamp_def, pair_def, reading_def, ref_def, keyed_def]) {
	Ok(text) => "-- schema\n${text}"
	Err(e) => "-- bad schema: ${Str.inspect(e)}"
}

## One seed block for a table, in the block format of `check.py`.
seed : Str, Try(Surreal.Statement, Surreal.Error) -> Str
seed = |name, statement| match statement {
	Ok(s) => s.block("-- seed: ${name}", [])
	Err(e) => "-- unsupported -- seed: ${name}: ${Str.inspect(e)}"
}

seed_blocks : List(Str)
seed_blocks = [
	seed("sample", samples.insert(seed_samples)),
	seed("phrase", phrases.insert(seed_phrases)),
	seed("stamp", stamps.insert(seed_stamps)),
	seed("pair", pairs.insert(seed_pairs)),
	seed("reading", readings.insert(seed_readings)),
	seed("ref", refs.insert(seed_refs)),
]

queries : List(Str)
queries = [
	block("-- query: str_case", Surreal.from(samples).select(case_line).bind({}), Surreal.literal(seed_samples.map(case_line))),
	block("-- query: str_trim", Surreal.from(samples).select(trim_line).bind({}), Surreal.literal(seed_samples.map(trim_line))),
	block("-- query: str_edit", Surreal.from(samples).select(edit_line).bind({}), Surreal.literal(seed_samples.map(edit_line))),
	block("-- query: str_split_replace", Surreal.from(samples).select(piece_line).bind({}), Surreal.literal(seed_samples.map(piece_line))),
	block("-- query: str_bytes", Surreal.from(samples).select(byte_line).bind({}), Surreal.literal(seed_samples.map(byte_line))),
	block("-- query: int_ops", Surreal.from(samples).select(int_line).bind({}), Surreal.literal(seed_samples.map(int_line))),
	block("-- query: dec_ops", Surreal.from(samples).select(dec_line).bind({}), Surreal.literal(seed_samples.map(dec_line))),
	block("-- query: int_try", Surreal.from(samples).select(try_line).bind({}), Surreal.literal(seed_samples.map(try_line))),
	block("-- query: list_try", Surreal.from(samples).select(list_line).bind({}), Surreal.literal(seed_samples.map(list_line))),
]

script : Str
script = Str.join_with([schema_block].concat(seed_blocks).concat(queries).concat(package_queries), "\n\n")

main! = |_args| {
	echo!("${script}\n")
	Ok({})
}
