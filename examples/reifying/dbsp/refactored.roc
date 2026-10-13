# `alerts`, `breaches`, `bands` and `weighted` of `main.roc`, refactored by
# hand: every lambda parameter and every local renamed, the bindings in another
# order, the fields of every record in another order, and a comparison written
# the other way round. The two helpers that stay Rust functions, `clamp` and
# `power`, are refactored the same way. None of it changes what a function computes, so the translator gets the
# same descriptions and writes the same Rust, byte for byte, down to the names of
# its locals (`expected_output.rs`).
#
# This is the claim of reification on the program a reader looks at first: a
# refactor that keeps the meaning keeps the output. A DSL that built the circuit
# by running its lambdas would see the names and the order.

app [main!] { dbsp: "package.roc" }

import dbsp.Dbsp
import "expected_output.rs" as expected_output : Str

Reading := { celsius : F64, sensor : Str }.{
	is_eq : _
}

Site := { limit : F64, room : Str, sensor : Str }.{
	is_eq : _
}

Alert := { breaches : I64, sensor : Str }.{
	is_eq : _
}

Breach := { over_by : F64, ratio : F64, room : Str, sensor : Str }.{
	is_eq : _
}

Band := { cold : F64, hot : F64, sensor : Str }.{
	is_eq : _
}

readings : Dbsp.Rel(Reading)
readings = Dbsp.input("readings")

sites : Dbsp.Rel(Site)
sites = Dbsp.input("sites")

## The margin is bound once, under another name, before the ratio that uses it.
breach_line : Reading, Site -> Breach
breach_line = |seen, place| {
	margin = seen.celsius - place.limit
	ratio = margin / place.limit
	Breach.({ sensor: seen.sensor, room: place.room, ratio, over_by: margin })
}

## The operands of `and` keep their order: it short-circuits, so swapping them
## is not a refactor, and the description keeps the order they were written in.
is_urgent : Breach -> Bool
is_urgent = |found| found.over_by > 5.0 and !found.room.starts_with("test-")

## The ceiling test is written the other way round. The order of the tests is
## kept: they pick different results when the floor is above the ceiling.
clamp : F64, F64, F64 -> F64
clamp = |value, floor, ceiling| if value < floor floor else if ceiling < value ceiling else value

## The counter is named for what it counts down, and its test is written the
## other way round.
power : I64, I64 -> I64
power = |number, remaining| if 0 >= remaining 1 else number * power(number, remaining - 1)

alerts : Dbsp.Rel(Alert)
alerts =
	readings
		.filter(|reading| 80.0 < reading.celsius)
		.key_by(|reading| reading.sensor)
		.count()
		.filter(|(_, hits)| hits >= 3)
		.map(|(id, hits)| Alert.({ breaches: hits, sensor: id }))

breaches : Dbsp.Rel(Breach)
breaches =
	readings
		.key_by(|reading| reading.sensor)
		.join(sites.key_by(|site| site.sensor), |_id, reading, site| breach_line(reading, site))
		.filter(is_urgent)

bands : Dbsp.Rel(Band)
bands =
	readings.map(
		|seen| Band.({ hot: clamp(seen.celsius, 80.0, 125.0), sensor: seen.sensor, cold: clamp(seen.celsius, -40.0, 20.0) }),
	)

weighted : Dbsp.Rel(Alert)
weighted =
	readings
		.filter(|seen| 80.0 < seen.celsius)
		.key_by(|seen| seen.sensor)
		.count()
		.map(|(id, hits)| Alert.({ sensor: id, breaches: power(hits, 2) }))

program : Try(Str, Dbsp.Error)
program = Dbsp.circuit([Dbsp.view("alerts", alerts), Dbsp.view("breaches", breaches), Dbsp.view("bands", bands), Dbsp.view("weighted", weighted)])

expect {
	match program {
		Ok(rust) => "${rust}\n" == expected_output
		Err(_) => Bool.False
	}
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
