# An incremental view, written as Roc: `alerts`, `breaches`, `bands` and
# `weighted` below are circuits for Feldera's DBSP engine, and every row they
# read, every test they make and every number they compute is ordinary Roc.
#
# DBSP keeps a query's answer current under insertions and deletions by
# computing the change rather than the answer again. The query is a circuit of
# operators, and the operators take closures. Here each closure is a Roc
# function handed to a `Code(f)` parameter, so the compiler describes it and
# `Dbsp.circuit` writes it again as a Rust closure. The combinators fix the
# topology of the circuit. The reified functions supply the expressions it is
# built out of.
#
# What that buys is the proposal's case for reification (section 15): a
# predicate that is also a function. `is_hot` is a stage of the circuit and is
# also called directly by the `expect`s below and by the pure-Roc reference
# engine at the end, which recomputes a view from scratch and checks the
# incremental answer against it. One definition, three uses.
#
# `roc main.roc` prints the Rust source. Nothing here compiles or runs it: the
# executor is native, so some platform has to carry the `dbsp` crate
# (proposal section 11.3).

app [main!] { dbsp: "package.roc" }

import dbsp.Dbsp

# ------------------------------------------------------------------- rows

## Rows are nominal records, so each becomes one Rust struct, under its name.
Reading := { sensor : Str, celsius : F64 }.{
	is_eq : _
}

Site := { sensor : Str, room : Str, limit : F64 }.{
	is_eq : _
}

Alert := { sensor : Str, breaches : I64 }.{
	is_eq : _
}

Breach := { room : Str, sensor : Str, over_by : F64, ratio : F64 }.{
	is_eq : _
}

Band := { sensor : Str, cold : F64, hot : F64 }.{
	is_eq : _
}

## The inputs a circuit has. An input is typed here, because the row type of
## `Dbsp.input` has no other place to come from.
readings : Dbsp.Rel(Reading)
readings = Dbsp.input("readings")

sites : Dbsp.Rel(Site)
sites = Dbsp.input("sites")

# --------------------------------------------------- ordinary Roc functions

## A reading hot enough to count.
is_hot : Reading -> Bool
is_hot = |r| r.celsius > 80.0

sensor_of : Reading -> Str
sensor_of = |r| r.sensor

## A sensor that was hot at least three times. The row is a sensor and its count.
is_noisy : (Str, I64) -> Bool
is_noisy = |(_, n)| n >= 3

to_alert : (Str, I64) -> Alert
to_alert = |(sensor, n)| Alert.({ sensor, breaches: n })

## How far a reading is over its sensor's limit.
excess : Reading, Site -> F64
excess = |r, s| r.celsius - s.limit

## One line of the report. It calls `excess` twice over, once for the margin and
## once for the ratio, so the circuit computes it once.
breach_line : Reading, Site -> Breach
breach_line = |r, s| Breach.({ room: s.room, sensor: r.sensor, over_by: excess(r, s), ratio: excess(r, s) / s.limit })

## A breach worth a page: a real margin, in a room that is not a test rig.
is_urgent : Breach -> Bool
is_urgent = |b| b.over_by > 5.0 and !b.room.starts_with("test-")

## A temperature held between a floor and a ceiling. `bands` calls it twice
## with different limits, so Roc keeps it as a function and the translator
## writes it as one.
clamp : F64, F64, F64 -> F64
clamp = |degrees, low, high| if degrees < low low else if degrees > high high else degrees

## Integer power by repeated multiplication. It calls itself, so Roc keeps it
## as a function whatever the number of its callers.
power : I64, I64 -> I64
power = |base, times| if times <= 0 1 else base * power(base, times - 1)

reading : Str, F64 -> Reading
reading = |sensor, celsius| Reading.({ sensor, celsius })

expect is_hot(reading("a", 90.0))

expect !is_hot(reading("a", 80.0))

expect is_noisy(("a", 3)) and !is_noisy(("a", 2))

expect excess(reading("a", 90.0), Site.({ sensor: "a", room: "lab", limit: 85.0 })) == 5.0

expect {
	line = breach_line(reading("a", 90.0), Site.({ sensor: "a", room: "lab", limit: 80.0 }))
	line.over_by == 10.0 and line.ratio == 0.125
}

expect clamp(30.0, 0.0, 20.0) == 20.0 and clamp(-5.0, 0.0, 20.0) == 0.0 and clamp(10.0, 0.0, 20.0) == 10.0

expect power(3, 0) == 1 and power(3, 4) == 81

expect is_urgent(Breach.({ room: "lab", sensor: "a", over_by: 6.0, ratio: 0.1 }))

expect !is_urgent(Breach.({ room: "test-rig", sensor: "a", over_by: 6.0, ratio: 0.1 }))

# ------------------------------------------------------------------ views

## Readings over 80 degrees, counted per sensor, kept when a sensor has three of
## them, and reported as an alert. This is the view of proposal section 14.3.
alerts : Dbsp.Rel(Alert)
alerts =
	readings
		.filter(|r| r.celsius > 80.0)
		.key_by(|r| r.sensor)
		.count()
		.filter(|(_, n)| n >= 3)
		.map(|(sensor, n)| Alert.({ sensor, breaches: n }))

## The same view, with every lambda replaced by the function it was a copy of.
## A function that is named is a function that is called: the reference engine
## below calls these very functions.
alerts_by_name : Dbsp.Rel(Alert)
alerts_by_name =
	readings
		.filter(is_hot)
		.key_by(sensor_of)
		.count()
		.filter(is_noisy)
		.map(to_alert)

## Readings joined to the site their sensor stands in, reported as a breach
## when they are over the site's limit. The join's function calls `breach_line`,
## which calls `excess`: the translator reads one body, with both inlined.
breaches : Dbsp.Rel(Breach)
breaches =
	readings
		.key_by(sensor_of)
		.join(sites.key_by(|s| s.sensor), |_sensor, r, s| breach_line(r, s))
		.filter(is_urgent)

## Every reading, as the part of it inside the cold band and the part inside
## the hot band. Both parts come from `clamp`, which the circuit defines once
## as a Rust function and calls twice.
bands : Dbsp.Rel(Band)
bands =
	readings.map(
		|r| Band.({ sensor: r.sensor, cold: clamp(r.celsius, -40.0, 20.0), hot: clamp(r.celsius, 80.0, 125.0) }),
	)

## Each sensor's hot readings, counted, and the count squared as a weight. The
## circuit defines `power` as a recursive Rust function.
weighted : Dbsp.Rel(Alert)
weighted =
	readings
		.filter(is_hot)
		.key_by(sensor_of)
		.count()
		.map(|(sensor, n)| Alert.({ sensor, breaches: power(n, 2) }))

## Every circuit the application runs, in one Rust program.
program : Try(Str, Dbsp.Error)
program = Dbsp.circuit([Dbsp.view("alerts", alerts), Dbsp.view("breaches", breaches), Dbsp.view("bands", bands), Dbsp.view("weighted", weighted)])

expected : Str
expected =
	\\// Generated by examples/reifying/dbsp/Dbsp.roc from reified Roc functions.
	\\// Targets the Feldera `dbsp` crate, in the form where `OrdZSet<T>` takes one type parameter.
	\\use anyhow::Result as AnyResult;
	\\#[allow(unused_imports)]
	\\use dbsp::{algebra::{F32, F64}, utils::*, OrdZSet, OutputHandle, RootCircuit, ZSetHandle};
	\\use rkyv::{Archive, Deserialize, Serialize};
	\\use size_of::SizeOf;
	\\
	\\#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, SizeOf, Archive, Serialize, Deserialize)]
	\\#[archive_attr(derive(Clone, Ord, Eq, PartialEq, PartialOrd))]
	\\pub struct Reading {
	\\    pub celsius: F64,
	\\    pub sensor: String,
	\\}
	\\
	\\#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, SizeOf, Archive, Serialize, Deserialize)]
	\\#[archive_attr(derive(Clone, Ord, Eq, PartialEq, PartialOrd))]
	\\pub struct Alert {
	\\    pub breaches: i64,
	\\    pub sensor: String,
	\\}
	\\
	\\#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, SizeOf, Archive, Serialize, Deserialize)]
	\\#[archive_attr(derive(Clone, Ord, Eq, PartialEq, PartialOrd))]
	\\pub struct Site {
	\\    pub limit: F64,
	\\    pub room: String,
	\\    pub sensor: String,
	\\}
	\\
	\\#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, SizeOf, Archive, Serialize, Deserialize)]
	\\#[archive_attr(derive(Clone, Ord, Eq, PartialEq, PartialOrd))]
	\\pub struct Breach {
	\\    pub over_by: F64,
	\\    pub ratio: F64,
	\\    pub room: String,
	\\    pub sensor: String,
	\\}
	\\
	\\#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, SizeOf, Archive, Serialize, Deserialize)]
	\\#[archive_attr(derive(Clone, Ord, Eq, PartialEq, PartialOrd))]
	\\pub struct Band {
	\\    pub cold: F64,
	\\    pub hot: F64,
	\\    pub sensor: String,
	\\}
	\\
	\\fn helper_0(p0: F64, p1: F64, p2: F64) -> F64 {
	\\    if p0 < p1 { p1 } else { if p2 < p0 { p2 } else { p0 } }
	\\}
	\\
	\\fn helper_1(p0: i64, p1: i64) -> i64 {
	\\    if p0 > 0i64 { p1 * helper_1(p0 - 1i64, p1) } else { 1i64 }
	\\}
	\\
	\\pub fn build_circuit(circuit: &mut RootCircuit) -> AnyResult<(ZSetHandle<Reading>, ZSetHandle<Site>, OutputHandle<OrdZSet<Alert>>, OutputHandle<OrdZSet<Breach>>, OutputHandle<OrdZSet<Band>>, OutputHandle<OrdZSet<Alert>>)> {
	\\    let (readings, readings_handle) = circuit.add_input_zset::<Reading>();
	\\    let (sites, sites_handle) = circuit.add_input_zset::<Site>();
	\\    let alerts = readings
	\\        .filter(|row| row.celsius > F64::new(80.0))
	\\        .map_index(|row| (row.sensor.clone(), row.clone()))
	\\        .aggregate_linear(|_| 1i64)
	\\        .map(|(key, n)| Tup2(key.clone(), *n))
	\\        .filter(|row| row.1 >= 3i64)
	\\        .map(|row| Alert { breaches: row.1, sensor: row.0.clone() });
	\\    let breaches = readings
	\\        .map_index(|row| (row.sensor.clone(), row.clone()))
	\\        .join(
	\\            &sites
	\\                .map_index(|row| (row.sensor.clone(), row.clone())),
	\\            |_key, left, right| {
	\\                let n4 = left.celsius - right.limit;
	\\                Breach { over_by: n4, ratio: n4 / right.limit, room: right.room.clone(), sensor: left.sensor.clone() }
	\\            },
	\\        )
	\\        .filter(|row| row.over_by > F64::new(5.0) && !row.room.starts_with("test-"));
	\\    let bands = readings
	\\        .map(|row| Band { cold: helper_0(row.celsius, F64::new(-40.0), F64::new(20.0)), hot: helper_0(row.celsius, F64::new(80.0), F64::new(125.0)), sensor: row.sensor.clone() });
	\\    let weighted = readings
	\\        .filter(|row| row.celsius > F64::new(80.0))
	\\        .map_index(|row| (row.sensor.clone(), row.clone()))
	\\        .aggregate_linear(|_| 1i64)
	\\        .map(|(key, n)| Tup2(key.clone(), *n))
	\\        .map(|row| Alert { breaches: helper_1(2i64, row.1), sensor: row.0.clone() });
	\\    Ok((readings_handle, sites_handle, alerts.output(), breaches.output(), bands.output(), weighted.output()))
	\\}

expect program == Ok(expected)

# A helper with two callers, and a function that calls itself, are Rust
# functions placed before `build_circuit`, and a `Call` is a call of one.
expect {
	text = Dbsp.circuit([Dbsp.view("bands", bands)]) ?? ""
	text.contains("fn helper_0(p0: F64, p1: F64, p2: F64) -> F64 {") and text.contains("cold: helper_0(row.celsius, F64::new(-40.0), F64::new(20.0))")
}

expect {
	text = Dbsp.circuit([Dbsp.view("weighted", weighted)]) ?? ""
	text.contains("fn helper_0(p0: i64, p1: i64) -> i64 {") and text.contains("p1 * helper_0(p0 - 1i64, p1)") and text.contains("breaches: helper_0(2i64, row.1)")
}

# Two stages hold the same helper in two descriptions, and the program defines
# it once. A helper of another body is another function.
bands_in_range : Dbsp.Rel(Band)
bands_in_range =
	readings
		.filter(|r| r.celsius > 0.0)
		.map(|r| Band.({ sensor: r.sensor, cold: clamp(r.celsius, -10.0, 30.0), hot: clamp(r.celsius, 60.0, 90.0) }))

expect {
	text = Dbsp.circuit([Dbsp.view("bands", bands), Dbsp.view("bands_in_range", bands_in_range), Dbsp.view("weighted", weighted)]) ?? ""
	text.split_on("fn helper_").len() == 3 and text.contains("let bands_in_range = readings") and text.contains("helper_0(row.celsius, F64::new(60.0), F64::new(90.0))")
}

# Naming a function is the same as writing its body where it is called. The
# normal form has no names, so both ways of writing `alerts` reach the
# translator as one description, and one circuit.
expect Dbsp.circuit([Dbsp.view("alerts", alerts_by_name)]) == Dbsp.circuit([Dbsp.view("alerts", alerts)])

# ----------------------------------------------------------------- refusals

# A refusal names the stage and the construct. The description does not carry
# source regions yet, so the stage stands for the place: the view, the position
# of the combinator in its chain, and which combinator it is.
#
# Roc's `trim` and Rust's `trim` may not strip the same characters, so the
# translator does not map one onto the other.
trimmed : Dbsp.Rel(Reading)
trimmed = readings.filter(|r| r.sensor.trim() == "a")

expect Dbsp.circuit([Dbsp.view("trimmed", trimmed)]) == Err(Unsupported("view `trimmed`, stage 1 (`filter`): `Str.trim` has no Rust form in this translator"))

# `dbsp`'s operators are the loops, so a loop inside a closure is refused.
looped : Dbsp.Rel(Reading)
looped = readings.filter(
	|r| {
		var $bytes = 0.U64
		for _byte in r.sensor.to_utf8() {
			$bytes = $bytes + 1
		}
		$bytes > 3
	},
)

expect Dbsp.circuit([Dbsp.view("looped", looped)]) == Err(Unsupported("view `looped`, stage 1 (`filter`): a loop has no closure form; `dbsp`'s operators are the loops, so write the step as a `filter`, a `map` or a `count`"))

## A helper is a Rust function, so what Rust has no form for is refused in its
## body, at the stage that calls it. `tidy` has two callers, so it stays a
## function, and `Str.trim` is the construct with no Rust form.
tidy : Str -> Str
tidy = |text| text.trim()

tidied : Dbsp.Rel(Site)
tidied = readings.map(|r| Site.({ sensor: tidy(r.sensor), room: tidy(r.sensor.concat("-room")), limit: 0.0 }))

expect Dbsp.circuit([Dbsp.view("tidied", tidied)]) == Err(Unsupported("view `tidied`, stage 1 (`map`): `Str.trim` has no Rust form in this translator"))

## A `Dec` is 128-bit fixed point, and `dbsp` has no column type for it.
Price := { sku : Str, amount : Dec }.{
	is_eq : _
}

prices : Dbsp.Rel(Price)
prices = Dbsp.input("prices")

pricey : Dbsp.Rel(Price)
pricey = prices.filter(|p| p.amount > 10)

expect Dbsp.circuit([Dbsp.view("pricey", pricey)]) == Err(BadType("view `pricey`, stage 1 (`filter`): Dec has no `dbsp` column type; use I64 or F64"))

# ------------------------------------------------------- the reference engine

# DBSP's data is a Z-set: rows with an integer weight. An insertion has weight 1
# and a deletion weight -1, and a change to a relation is a Z-set too.
#
# This is the same view, `alerts_by_name`, as ordinary Roc. It is small because
# it calls the view's own functions, `is_hot`, `is_noisy` and `to_alert`. A
# `Code` cannot be called, so the engine could not call the circuit itself.

ZSet(row) : List({ row : row, weight : I64 })

## Add up the weights of equal rows, and drop the rows that cancel.
consolidate : ZSet(row) -> ZSet(row) where [row.is_eq : row, row -> Bool]
consolidate = |entries| {
	merged = entries.fold(
		[],
		|acc, entry| match acc.find_first_index(|seen| seen.row == entry.row) {
			Ok(at) => acc.map_with_index(|seen, i| { row: seen.row, weight: if i == at seen.weight + entry.weight else seen.weight })
			Err(_) => acc.append(entry)
		},
	)
	merged.keep_if(|entry| entry.weight != 0)
}

same : ZSet(row), ZSet(row) -> Bool where [row.is_eq : row, row -> Bool]
same = |a, b| {
	left = consolidate(a)
	right = consolidate(b)
	left.len() == right.len() and left.all(|entry| right.contains(entry))
}

## How many hot readings each sensor has had, over every batch so far.
Counts : Dict(Str, I64)

count_of : Counts, Str -> I64
count_of = |counts, sensor| counts.get(sensor) ?? 0

## The alert a sensor has when `n` of its readings are hot, at a weight.
alert_at : Str, I64, I64 -> ZSet(Alert)
alert_at = |sensor, n, weight| if is_noisy((sensor, n)) [{ row: to_alert((sensor, n)), weight }] else []

## What one batch of readings changes: the counts afterwards, and the alerts
## that appear (weight 1) or go away (weight -1). Only the sensors the batch
## touches are read, which is the whole point of an incremental engine.
step : Counts, ZSet(Reading) -> { counts : Counts, out : ZSet(Alert) }
step = |counts, batch| {
	hot = batch.keep_if(|entry| is_hot(entry.row))
	touched = hot.fold([], |seen, entry| if seen.contains(entry.row.sensor) seen else seen.append(entry.row.sensor))
	moves = touched.map(
		|sensor| {
			before = count_of(counts, sensor)
			change = hot.keep_if(|entry| entry.row.sensor == sensor).fold(0, |sum, entry| sum + entry.weight)
			{ sensor, before, after: before + change }
		},
	)
	{
		counts: moves.fold(counts, |acc, move| acc.insert(move.sensor, move.after)),
		out: moves.join_map(|move| alert_at(move.sensor, move.before, -1).concat(alert_at(move.sensor, move.after, 1))),
	}
}

## The view over a whole relation, with no memory of any earlier answer.
from_scratch : List(Reading) -> ZSet(Alert)
from_scratch = |all| {
	hot = all.keep_if(is_hot)
	sensors = hot.fold([], |seen, r| if seen.contains(r.sensor) seen else seen.append(r.sensor))
	sensors.join_map(|sensor| alert_at(sensor, hot.fold(0, |n, r| if r.sensor == sensor n + 1 else n), 1))
}

batch_one : ZSet(Reading)
batch_one = [
	{ row: reading("a", 90.0), weight: 1 },
	{ row: reading("a", 95.0), weight: 1 },
	{ row: reading("a", 70.0), weight: 1 },
	{ row: reading("b", 85.0), weight: 1 },
]

batch_two : ZSet(Reading)
batch_two = [
	{ row: reading("a", 99.0), weight: 1 },
	{ row: reading("b", 86.0), weight: 1 },
	{ row: reading("b", 87.0), weight: 1 },
]

## A reading is withdrawn, which a snapshot engine could only say by resending
## every other reading.
batch_three : ZSet(Reading)
batch_three = [{ row: reading("a", 90.0), weight: -1 }]

expect {
	first = step(Dict.empty(), batch_one)
	second = step(first.counts, batch_two)
	third = step(second.counts, batch_three)
	everything = consolidate(batch_one.concat(batch_two).concat(batch_three)).map(|entry| entry.row)
	integrated = first.out.concat(second.out).concat(third.out)
	# Nothing is an alert yet, two sensors are after the second batch, and the
	# third batch takes one back: its answer is that one change and no more.
	nothing_yet = first.out.is_empty()
	both_appear = same(second.out, [{ row: to_alert(("a", 3)), weight: 1 }, { row: to_alert(("b", 3)), weight: 1 }])
	one_goes = same(third.out, [{ row: to_alert(("a", 3)), weight: -1 }])
	nothing_yet and both_appear and one_goes and same(integrated, from_scratch(everything))
}

main! = |_args| {
	match program {
		Ok(rust) => echo!("${rust}\n")
		Err(Unsupported(message)) => echo!("unsupported: ${message}\n")
		Err(BadType(message)) => echo!("bad type: ${message}\n")
		Err(BadCircuit(message)) => echo!("bad circuit: ${message}\n")
	}
	Ok({})
}
