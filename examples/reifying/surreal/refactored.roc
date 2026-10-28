# `main.roc`, refactored by hand: the parameters of the functions the
# queries and constraints reify renamed, bindings added, bindings in another
# order, and some helpers inlined or extracted. None of it changes what a
# function computes, so every description is the same, and the script this
# prints is `expected_output.surql`, byte for byte, which the `expect` at the
# end checks.
#
# A veterinary clinic's schema and queries, written against `Surreal.roc`.
#
# The rows are ordinary Roc records. The same `Owner`, `Patient` and `Visit`
# values the queries describe are the ones the application builds, inserts,
# passes to its own functions and tests with `expect`. Every clause, and every
# database constraint, is a Roc function over those records, reified where a
# builder method asks for a `Code(f)`.
#
# `roc main.roc` prints one SurrealQL script: the schema, the seed rows, the
# queries, the writes the database must refuse, and the writes it must accept.
# `check.py` runs it. Each query carries the result Roc computes with the same
# functions over the same rows, and the database must return the same result.

app [main!] { surreal: "package.roc" }

import surreal.Surreal
import "expected_output.surql" as expected_output : Str

# ------------------------------------------------------------------- rows

Address : { city : Str, line : Str, zip ?: Str }

## `referred_by` links to another owner: a row that links to its own table.
Owner := { id : Str, name : Str, email : Str, phone ?: Str, address : Address, tags : List(Str), referred_by ?: Surreal.Link(Owner) }.{
	encoder_for : _
}

Contact : { email : Str, phone : Str }

## A vet's specialty is a union. `Surgery` carries the board that certified it.
Specialty : [General, Surgery({ board : Str }), Dental]

## The years of a vet. `U8` makes the database keep it between 0 and 255.
VetRow(years) : { id : Str, name : Str, license : Str, contact : Contact, years : years, rate : Dec, specialty : Specialty }

Vet : VetRow(U8)

Medication : { id : Str, name : Str, form : Str, label : Str, unit_price : Dec, stock : I32 }

## What the front desk types in. The label is computed and the stock has a
## default, so a new medication does not say either.
MedicationForm : { id : Str, name : Str, form : Str, unit_price : Dec }

## What a select of every field returns for a medication: the key is a record id.
StoredMedication : { id : Surreal.Id(Medication), name : Str, form : Str, label : Str, unit_price : Dec, stock : I32 }

Species : [Dog, Cat, Bird({ wingspan_cm : U8 }), Exotic({ latin : Str })]

## A link inside a list of records.
Vaccine : { name : Str, given : Str, vet : Surreal.Link(Vet) }

## A link inside an optional record.
Chip : { code : Str, implanted_by : Surreal.Link(Vet) }

Patient : {
	id : Str,
	name : Str,
	species : Species,
	age : U8,
	weight_kg : Dec,
	owner : Surreal.Link(Owner),
	allergies : List(Surreal.Link(Medication)),
	chip ?: Chip,
	vaccines : List(Vaccine),
}

Dose : { medication : Surreal.Link(Medication), doses : I64 }

## A link inside an arm of a union.
Outcome : [Treated, Followup({ days : U8 }), Referred({ to : Surreal.Link(Vet), reason : Str })]

Visit : {
	id : Str,
	patient : Surreal.Link(Patient),
	vet : Surreal.Link(Vet),
	seen : Surreal.Datetime,
	items : List(Dose),
	outcome : Outcome,
	fee : Dec,
}

## A graph edge from a vet to a patient.
Treats : { id : Str, from : Surreal.Link(Vet), to : Surreal.Link(Patient), since_year : I64, primary : Bool }

owners : Surreal.Table(Owner)
owners = Surreal.table("owner", |o| o)

vets : Surreal.Table(Vet)
vets = Surreal.table("vet", |v| v)

## The same table as `vets`, for a row whose `years` is not yet checked.
unchecked_vets : Surreal.Table(VetRow(I64))
unchecked_vets = Surreal.table("vet", |v| v)

medications : Surreal.Table(Medication)
medications = Surreal.table("medication", |m| m)

medication_forms : Surreal.Table(MedicationForm)
medication_forms = Surreal.table("medication", |m| m)

patients : Surreal.Table(Patient)
patients = Surreal.table("patient", |p| p)

visits : Surreal.Table(Visit)
visits = Surreal.table("visit", |v| v)

treats : Surreal.Table(Treats)
treats = Surreal.relation("treats", vets, patients, |e| e)

ruth_id : Surreal.Id(Vet)
ruth_id = Surreal.id_of("vet", "ruth")

# --------------------------------------------------- ordinary Roc functions

## Used by the database, as a constraint, and by the application.
valid_email : Str -> Bool
valid_email = |address| {
	not_first = !address.starts_with("@")
	has_at = address.contains("@")
	has_at and not_first
}

## The computed label of a medication, in the database and in the program.
label_of : Str, Str -> Str
label_of = |title, kind| "${title} (${kind})"

species_label : Species -> Str
species_label = |kind| match kind {
	Dog => "dog"
	Cat => "cat"
	Bird(_) => "bird"
	Exotic(other) => other.latin
}

outcome_text : Outcome -> Str
outcome_text = |result| match result {
	Treated => "treated"
	Followup(_) => "follow-up"
	Referred(referral) => {
		vet_name = referral.to.get().name
		"referred to ${vet_name}"
	}
}

needs_attention : Outcome -> Bool
needs_attention = |result| match result {
	Treated => Bool.False
	_ => Bool.True
}

## What a visit costs: the fee and the medication that was given.
bill : Visit -> Dec
bill = |stay| {
	given = stay.items.map(|line| line.doses.to_dec() * line.medication.get().unit_price).sum()
	stay.fee + given
}

wide_wings : Patient -> Bool
wide_wings = |pet| match pet.species {
	Bird(wings) => {
		wide = 20
		wings.wingspan_cm >= wide
	}
	_ => Bool.False
}

expect valid_email("ada@example.org")
expect !valid_email("ada.example.org")
expect label_of("Aspirin", "tablet") == "Aspirin (tablet)"
expect species_label(Bird({ wingspan_cm: 30 })) == "bird"
expect species_label(Exotic({ latin: "gecko" })) == "gecko"
expect needs_attention(Followup({ days: 7 }))
expect !needs_attention(Treated)

## The constraints are functions too. Each one is named, used in the schema,
## and tried on a bad row in Roc and in the database.
positive_doses : Dose -> Bool
positive_doses = |line| {
	none = 0
	line.doses > none
}

## A visit that gave medication has a fee. It reads two fields, so it is an
## event, not a field constraint.
fee_covers_items : Visit -> Bool
fee_covers_items = |stay| {
	paid = stay.fee > 0
	free = stay.items.is_empty()
	free or paid
}

sane_outcome : Outcome -> Bool
sane_outcome = |result| match result {
	Followup(plan) => {
		started = plan.days > 0
		short = plan.days <= 90
		started and short
	}
	_ => Bool.True
}

## A bird of any wingspan, or any other animal.
possible_species : Species -> Bool
possible_species = |kind| match kind {
	Bird(wings) => wings.wingspan_cm > 0
	_ => Bool.True
}

named : Str -> Bool
named = |text| text != ""

# ---------------------------------------------------------------- the data

at : Str -> Surreal.Datetime
at = |text| match Surreal.datetime(text) {
	Ok(d) => d
	Err(_) => crash "a valid datetime in the seed data"
}

ruth : Vet
ruth = { id: "ruth", name: "Ruth Okafor", license: "VET-1001", contact: { email: "ruth@paws.example", phone: "555-0101" }, years: 12, rate: 80, specialty: General }

sam : Vet
sam = { id: "sam", name: "Sam Petrov", license: "VET-1002", contact: { email: "sam@paws.example", phone: "555-0102" }, years: 8, rate: 140, specialty: Surgery({ board: "ACVS" }) }

tia : Vet
tia = { id: "tia", name: "Tia Brandt", license: "VET-1003", contact: { email: "tia@paws.example", phone: "555-0103" }, years: 3, rate: 95.5, specialty: Dental }

seed_vets : List(Vet)
seed_vets = [ruth, sam, tia]

jon : Owner
jon = { id: "jon", name: "Jon Berg", email: "jon@example.org", address: { city: "Oslo", line: "Storgata 4", zip: "0155" }, tags: ["new"] }

lena : Owner
lena = { id: "lena", name: "Lena Roux", email: "lena@example.org", phone: "555-0188", address: { city: "Lyon", line: "Rue Merciere 9" }, tags: [] }

mara : Owner
mara = { id: "mara", name: "Mara Ito", email: "mara@example.org", phone: "555-0142", address: { city: "Oslo", line: "Akersgata 12", zip: "0158" }, tags: ["vip"] }

noor : Owner
noor = { id: "noor", name: "Noor Haddad", email: "noor@example.org", address: { city: "Porto", line: "Rua das Flores 7" }, tags: ["vip", "new"], referred_by: owner_link(mara) }

seed_owners : List(Owner)
seed_owners = [jon, lena, mara, noor]

medication : Str, Str, Str, Dec, I32 -> Medication
medication = |id, name, form, unit_price, stock| { id, name, form, label: label_of(name, form), unit_price, stock }

amoxicillin : Medication
amoxicillin = medication("amoxicillin", "Amoxicillin", "tablet", 0.8, 200)

aspirin : Medication
aspirin = medication("aspirin", "Aspirin", "tablet", 0.2, 500)

gabapentin : Medication
gabapentin = medication("gabapentin", "Gabapentin", "capsule", 1.4, 40)

ivermectin : Medication
ivermectin = medication("ivermectin", "Ivermectin", "injection", 3.5, 15)

seed_medications : List(Medication)
seed_medications = [amoxicillin, aspirin, gabapentin, ivermectin]

## A link the program has the row for. In a clause, `get` is a traversal;
## here it reads the row.
vet_link : Vet -> Surreal.Link(Vet)
vet_link = |v| Surreal.fetched(vets, v)

owner_link : Owner -> Surreal.Link(Owner)
owner_link = |o| Surreal.fetched(owners, o)

medication_link : Medication -> Surreal.Link(Medication)
medication_link = |m| Surreal.fetched(medications, m)

patient_link : Patient -> Surreal.Link(Patient)
patient_link = |p| Surreal.fetched(patients, p)

bo : Patient
bo = {
	id: "bo",
	name: "Bo",
	species: Dog,
	age: 12,
	weight_kg: 31.5,
	owner: owner_link(jon),
	allergies: [],
	vaccines: [{ name: "rabies", given: "2025-05-02", vet: vet_link(ruth) }],
}

kiwi : Patient
kiwi = { id: "kiwi", name: "Kiwi", species: Bird({ wingspan_cm: 25 }), age: 2, weight_kg: 0.4, owner: owner_link(lena), allergies: [], vaccines: [] }

luna : Patient
luna = {
	id: "luna",
	name: "Luna",
	species: Cat,
	age: 3,
	weight_kg: 4.2,
	owner: owner_link(mara),
	allergies: [medication_link(aspirin)],
	chip: { code: "985-112", implanted_by: vet_link(sam) },
	vaccines: [],
}

mimi : Patient
mimi = { id: "mimi", name: "Mimi", species: Cat, age: 9, weight_kg: 5.1, owner: owner_link(noor), allergies: [], vaccines: [] }

rex : Patient
rex = {
	id: "rex",
	name: "Rex",
	species: Dog,
	age: 5,
	weight_kg: 28,
	owner: owner_link(mara),
	allergies: [medication_link(aspirin), medication_link(amoxicillin)],
	chip: { code: "985-100", implanted_by: vet_link(ruth) },
	vaccines: [
		{ name: "rabies", given: "2025-06-11", vet: vet_link(ruth) },
		{ name: "distemper", given: "2025-06-11", vet: vet_link(sam) },
	],
}

zed : Patient
zed = { id: "zed", name: "Zed", species: Exotic({ latin: "gecko" }), age: 4, weight_kg: 0.1, owner: owner_link(noor), allergies: [], vaccines: [] }

seed_patients : List(Patient)
seed_patients = [bo, kiwi, luna, mimi, rex, zed]

dose : Medication, I64 -> Dose
dose = |m, doses| { medication: medication_link(m), doses }

visit : Str, Patient, Vet, Str, List(Dose), Outcome, Dec -> Visit
visit = |id, patient, vet, seen, items, outcome, fee| {
	id,
	patient: patient_link(patient),
	vet: vet_link(vet),
	seen: at(seen),
	items,
	outcome,
	fee,
}

seed_visits : List(Visit)
seed_visits = [
	visit("v1", rex, ruth, "2026-01-10T09:00:00Z", [dose(amoxicillin, 14)], Treated, 80),
	visit("v2", rex, sam, "2026-02-03T14:30:00Z", [], Followup({ days: 14 }), 140),
	visit("v3", luna, ruth, "2026-02-20T10:15:00Z", [dose(gabapentin, 10)], Referred({ to: vet_link(tia), reason: "dental scale" }), 80),
	visit("v4", bo, ruth, "2026-03-05T11:00:00Z", [dose(amoxicillin, 7), dose(ivermectin, 1)], Treated, 80),
	visit("v5", mimi, sam, "2026-03-18T16:45:00Z", [], Treated, 140),
	visit("v6", kiwi, ruth, "2026-04-02T08:30:00Z", [dose(ivermectin, 1)], Followup({ days: 7 }), 40),
	visit("v7", zed, sam, "2026-04-11T13:00:00Z", [], Treated, 60),
]

edge : Str, Vet, Patient, I64, Bool -> Treats
edge = |id, v, p, since_year, primary| { id, from: vet_link(v), to: patient_link(p), since_year, primary }

seed_treats : List(Treats)
seed_treats = [
	edge("e1", ruth, rex, 2022, Bool.True),
	edge("e2", sam, rex, 2024, Bool.False),
	edge("e3", ruth, bo, 2020, Bool.True),
	edge("e4", sam, luna, 2025, Bool.True),
	edge("e5", tia, luna, 2025, Bool.False),
	edge("e6", ruth, kiwi, 2026, Bool.True),
	edge("e7", sam, mimi, 2023, Bool.True),
	edge("e8", ruth, zed, 2026, Bool.True),
]

# ------------------------------------------------------------------ schema

owner_def : Surreal.Defined
owner_def =
	owners.define()
		.unique(|who| who.email)
		.unique(|who| { line: who.address.line, city: who.address.city })
		.assert(|who| who.email, valid_email)
		.assert_each(|who| who.tags, |tag| tag != "")
		.check("named", |who| who.name != "")
		.default(|who| who.tags, [])
		.index(|who| who.address.city)
		.on_delete(owners, Unset)
		.done()

vet_def : Surreal.Defined
vet_def =
	vets.define()
		.unique(|doc| doc.contact.email)
		.assert(|doc| doc.contact.email, |address| Surreal.Text.is_email(address))
		.assert(|doc| doc.license, |code| code.starts_with("VET-"))
		.readonly(|doc| doc.license)
		.check("positive rate", |doc| doc.rate > 0)
		.done()

medication_def : Surreal.Defined
medication_def =
	medications.define()
		.computed(|med| med.label, |med| label_of(med.name, med.form))
		.default(|med| med.stock, 0)
		.done()

## The weight rule, extracted from the schema into a function of its own.
has_weight : Patient -> Bool
has_weight = |pet| pet.weight_kg > 0

patient_def : Surreal.Defined
patient_def =
	patients.define()
		.unique(|pet| { owner: pet.owner, name: pet.name })
		.assert(|pet| pet.species, possible_species)
		.assert_each(|pet| pet.vaccines, |shot| named(shot.name))
		.check("weight above zero", has_weight)
		.default(|pet| pet.allergies, [])
		.index(|pet| pet.age)
		.on_delete(owners, Cascade)
		.on_delete(vets, Reject)
		.on_delete_at(|pet| pet.allergies, Unset)
		.done()

visit_def : Surreal.Defined
visit_def =
	visits.define()
		.assert_each(|stay| stay.items, positive_doses)
		.assert(|stay| stay.outcome, sane_outcome)
		.check("items need a fee", fee_covers_items)
		.check("fee not negative", |stay| stay.fee >= 0)
		.index(|stay| stay.seen)
		.on_delete(patients, Cascade)
		.on_delete(medications, Reject)
		.done()

treats_def : Surreal.Defined
treats_def =
	treats.define()
		.check("since a real year", |link| link.since_year >= 1990)
		.unique(|link| { to: link.to, from: link.from })
		.done()

# ---------------------------------------------------------------- queries

CityParam : { city : Str }

in_city : CityParam, Owner -> Bool
in_city = |param, who| {
	wanted = param.city
	who.address.city == wanted
}

OwnerCard : { id : Str, name : Str, phone : Str }

## An optional field has a say in the query too: `??` is the same in both.
owner_card : Owner -> OwnerCard
owner_card = |who| {
	phone = who.?phone ?? "none"
	{ phone, name: who.name, id: who.id }
}

## A link to a row of the same table, read through `.?`.
ReferralLine : { id : Str, by : Str }

referral_line : Owner -> ReferralLine
referral_line = |who| {
	by = match who.?referred_by {
		Err(_) => "nobody"
		Ok(friend) => friend.get().name
	}
	{ by, id: who.id }
}

is_vip : Owner -> Bool
is_vip = |who| {
	tag = "vip"
	who.tags.contains(tag)
}

## A traversal through the owner link, and a `match` on the union.
PetLine : { id : Str, kind : Str, owner : Str }

pet_line : Patient -> PetLine
pet_line = |pet| {
	owner_name = pet.owner.get().name
	{ owner: owner_name, kind: species_label(pet.species), id: pet.id }
}

## A link inside an optional record: the chip's vet, or nobody.
ChipLine : { id : Str, chip : Str, by : Str }

chip_line : Patient -> ChipLine
chip_line = |pet| {
	by = match pet.?chip {
		Ok(implant) => implant.implanted_by.get().name
		Err(_) => "nobody"
	}
	code = match pet.?chip {
		Ok(implant) => implant.code
		Err(_) => "none"
	}
	{ by, chip: code, id: pet.id }
}

## Links inside a list of records.
VaccineLine : { id : Str, vets : List(Str) }

vaccine_line : Patient -> VaccineLine
vaccine_line = |pet| {
	names = pet.vaccines.map(|shot| shot.vet.get().name)
	{ vets: names, id: pet.id }
}

vaccinated_by_ruth : Patient -> Bool
vaccinated_by_ruth = |pet| pet.vaccines.any(|shot| shot.vet.id() == ruth_id)

SinceParam : { since : Surreal.Datetime }

seen_since : SinceParam, Visit -> Bool
seen_since = |param, stay| {
	start = param.since
	stay.seen >= start
}

VisitLine : { id : Str, patient : Str, vet : Str, bill : Dec }

visit_line : Visit -> VisitLine
visit_line = |stay| {
	cost = bill(stay)
	{ vet: stay.vet.get().name, patient: stay.patient.get().name, id: stay.id, bill: cost }
}

OutcomeLine : { id : Str, text : Str }

outcome_line : Visit -> OutcomeLine
outcome_line = |stay| {
	text = outcome_text(stay.outcome)
	{ text, id: stay.id }
}

needs_follow_up : Visit -> Bool
needs_follow_up = |stay| needs_attention(stay.outcome)

## Edges leaving a vet: how many patients, and how many are the vet's own.
CaseLoad : { name : Str, patients : I64, primary : I64 }

case_load : Vet, List(Treats) -> CaseLoad
case_load = |doc, links| {
	own = links.keep_if(|link| link.primary).len().to_i64_wrap()
	all = links.len().to_i64_wrap()
	{ primary: own, patients: all, name: doc.name }
}

## Edges arriving at a patient: the lead vet, if any.
TeamLine : { name : Str, team : I64, lead : List(Str) }

team_line : Patient, List(Treats) -> TeamLine
team_line = |pet, links| {
	lead = links.keep_if(|link| link.primary).map(|link| link.from.get().name)
	{ team: links.len().to_i64_wrap(), name: pet.name, lead }
}

Ledger : { vet : Str, visits : I64, revenue : Dec, avg_fee : F64 }

ledger_line : Str, List(Visit) -> Ledger
ledger_line = |who, stays| {
	revenue = stays.map(|stay| stay.fee).sum()
	avg_fee = Surreal.Math.mean(stays.map(|stay| stay.fee.to_f64()))
	{ visits: stays.len().to_i64_wrap(), vet: who, revenue, avg_fee }
}

PatientAge : { id : Str, age : U8 }

patient_age : Patient -> PatientAge
patient_age = |pet| { age: pet.age, id: pet.id }

## A query written inside a function. The price limit exists only when the
## program runs, so the statement takes it as a `LET`.
cheaper_than : Dec -> Try(Surreal.Statement, Surreal.Error)
cheaper_than = |ceiling| {
	cheap = Surreal.select_where(medications, |med| med.unit_price < ceiling)
	Surreal.bind_captured(cheap)
}

stored : Medication -> StoredMedication
stored = |med| { id: medications.id(med.id), name: med.name, form: med.form, label: med.label, unit_price: med.unit_price, stock: med.stock }

ContactLine : { id : Str, city : Str, vets : List(Str) }

## Reads the owner and the vaccinating vets, so a query fetches both links.
contact_line : Patient -> ContactLine
contact_line = |pet| {
	city = pet.owner.get().address.city
	{ vets: pet.vaccines.map(|shot| shot.vet.get().name), city, id: pet.id }
}

StockLine : { id : Str, label : Str, stock : I32 }

stock_line : Medication -> StockLine
stock_line = |med| { stock: med.stock, label: med.label, id: med.id }

RestockParam : { floor : I32, add : I32 }

low_stock : RestockParam, Medication -> Bool
low_stock = |param, med| {
	floor = param.floor
	med.stock < floor
}

refill : RestockParam, Medication -> Medication
refill = |param, med| {
	topped_up = med.stock + param.add
	{ ..med, stock: topped_up }
}

SpecialtyLine : { id : Str, years : U8, specialty : Specialty }

specialty_line : Vet -> SpecialtyLine
specialty_line = |doc| { specialty: doc.specialty, years: doc.years, id: doc.id }

## Tia passes her surgery boards.
certified : Vet -> Vet
certified = |doc| {
	older = doc.years + 1
	{ ..doc, specialty: Surgery({ board: "ECVS" }), years: older }
}

AllergyLine : { id : Str, allergies : List(Str) }

allergy_line : Patient -> AllergyLine
allergy_line = |pet| {
	names = pet.allergies.map(|med| med.get().name)
	{ allergies: names, id: pet.id }
}

EdgeLine : { id : Str, vet : Str, patient : Str }

edge_line : Treats -> EdgeLine
edge_line = |link| { patient: link.to.get().name, vet: link.from.get().name, id: link.id }

RetentionParam : { before : Surreal.Datetime }

too_old : RetentionParam, Visit -> Bool
too_old = |param, stay| {
	limit = param.before
	stay.seen < limit
}

# ------------------- the reference results: the seed rows, filtered in Roc

# Helpers for the `-- roc:` lines of the script. Each one computes a query's
# result in Roc from the seed rows, and `check.py` compares it with the result
# the database returns.

owners_in_city : Str -> List(OwnerCard)
owners_in_city = |city| seed_owners.keep_if(|o| in_city({ city: city }, o)).map(owner_card)

edges_of_vet : Vet -> List(Treats)
edges_of_vet = |v| seed_treats.keep_if(|e| e.from.get().id == v.id)

edges_of_patient : Patient -> List(Treats)
edges_of_patient = |p| seed_treats.keep_if(|e| e.to.get().id == p.id)

visit_names : List(Str)
visit_names = seed_visits.map(|v| v.vet.get().name).fold([], |seen, name| if (seen.contains(name)) seen else seen.append(name))

ledger_in_memory : List(Ledger)
ledger_in_memory = visit_names.map(|name| ledger_line(name, seed_visits.keep_if(|v| v.vet.get().name == name)))

expect owners_in_city("Oslo").map(|c| c.id) == ["jon", "mara"]
expect owner_card(lena).phone == "555-0188"
expect owner_card(jon).phone == "none"
expect referral_line(noor) == { id: "noor", by: "Mara Ito" }
expect referral_line(jon).by == "nobody"
expect pet_line(rex) == { id: "rex", kind: "dog", owner: "Mara Ito" }
expect chip_line(rex) == { id: "rex", chip: "985-100", by: "Ruth Okafor" }
expect chip_line(bo) == { id: "bo", chip: "none", by: "nobody" }
expect vaccine_line(rex).vets == ["Ruth Okafor", "Sam Petrov"]
expect wide_wings(kiwi) and !wide_wings(rex)
expect seed_patients.keep_if(vaccinated_by_ruth).map(|p| p.id) == ["bo", "rex"]
expect bill(visit_of("v4")).to_str() == "89.1"
expect case_load(ruth, edges_of_vet(ruth)) == { name: "Ruth Okafor", patients: 4, primary: 4 }
expect team_line(luna, edges_of_patient(luna)) == { name: "Luna", team: 2, lead: ["Sam Petrov"] }
expect ledger_in_memory.map(|l| l.vet) == ["Ruth Okafor", "Sam Petrov"]
expect outcome_line(visit_of("v3")).text == "referred to Tia Brandt"

visit_of : Str -> Visit
visit_of = |id| match seed_visits.find_first(|v| v.id == id) {
	Ok(v) => v
	Err(_) => crash "no such visit in the seed data"
}

# ----------------------------------------------------------- the constraints

## A visit that gives medication for free.
free_medication : Visit
free_medication = { ..visit_of("v1"), id: "v8", fee: 0 }

zero_doses : Dose
zero_doses = dose(amoxicillin, 0)

expect !fee_covers_items(free_medication)
expect fee_covers_items(visit_of("v1"))
expect !positive_doses(zero_doses)
expect positive_doses(dose(amoxicillin, 3))
expect !sane_outcome(Followup({ days: 0 }))
expect !possible_species(Bird({ wingspan_cm: 0 }))
expect !named("")

## Rows the database must refuse, one for each constraint. Where a Roc
## function states the rule, `expect` tries it on the same row.
light_patient : Patient
light_patient = { ..bo, id: "bad", name: "Featherweight", weight_kg: 0 }

blank_tag_owner : Owner
blank_tag_owner = { ..jon, id: "bad", name: "Blank", email: "blank@example.org", address: { city: "Nowhere", line: "1 Main St" }, tags: [""] }

bad_email_owner : Owner
bad_email_owner = { ..jon, id: "bad", name: "Mailless", email: "mailless.example.org", address: { city: "Nowhere", line: "2 Main St" } }

shared_email_vet : Vet
shared_email_vet = { ..sam, id: "bad", license: "VET-9001" }

twin_patient : Patient
twin_patient = { ..rex, id: "rex2" }

neighbour : Owner
neighbour = { ..mara, id: "bad", name: "Twin", email: "twin@example.org" }

## In full, not `{ ..ruth, years: 300 }`: a record update has the type of
## its base, and this row's `years` is an `I64`.
old_vet : VetRow(I64)
old_vet = { id: "bad", name: "Methuselah", license: "VET-9002", contact: { email: "old@paws.example", phone: "1" }, years: 300, rate: 50, specialty: General }

wingless_bird : Patient
wingless_bird = { ..kiwi, id: "bad", name: "Wingless", species: Bird({ wingspan_cm: 0 }) }

endless_followup : Visit
endless_followup = { ..visit_of("v2"), id: "bad", outcome: Followup({ days: 0 }) }

ghost_owner_patient : Patient
ghost_owner_patient = { ..bo, id: "bad", name: "Stray", owner: owners.link("nobody") }

ghost_medication_visit : Visit
ghost_medication_visit = { ..visit_of("v1"), id: "bad", items: [{ medication: medications.link("ghost"), doses: 1 }] }

ghost_chip_patient : Patient
ghost_chip_patient = { ..bo, id: "bad", name: "Chipped", chip: { code: "000-000", implanted_by: vets.link("ghost") } }

ghost_referral_visit : Visit
ghost_referral_visit = { ..visit_of("v2"), id: "bad", outcome: Referred({ to: vets.link("ghost"), reason: "who" }) }

ghost_vaccine_patient : Patient
ghost_vaccine_patient = { ..bo, id: "bad", name: "Jabbed", vaccines: [{ name: "rabies", given: "2025-01-01", vet: vets.link("ghost") }] }

blank_vaccine_patient : Patient
blank_vaccine_patient = { ..bo, id: "bad", name: "Unnamed", vaccines: [{ name: "", given: "2025-01-01", vet: vet_link(ruth) }] }

early_edge : Treats
early_edge = edge("e10", tia, kiwi, 1980, Bool.False)

repeated_edge : Treats
repeated_edge = edge("e11", ruth, rex, 2026, Bool.False)

expect !valid_email(bad_email_owner.email)
expect !possible_species(wingless_bird.species)
expect !sane_outcome(endless_followup.outcome)
expect blank_tag_owner.tags == [""]
expect light_patient.weight_kg == 0

# --------------------------------------------------------------- the script

## One block: the statement, then the Roc result for the same question.
block : Str, List(Str), Try(Surreal.Statement, Surreal.Error), Try(Str, Surreal.Error) -> Str
block = |header, flags, statement, reference| match (statement, reference) {
	(Ok(s), Ok(literal)) => s.block(header, flags.append("-- roc: ${literal}"))
	(Err(e), _) | (_, Err(e)) => "-- unsupported ${header}: ${Str.inspect(e)}"
}

## A block that has no Roc result: seeds and writes the database must refuse.
plain : Str, List(Str), Try(Surreal.Statement, Surreal.Error) -> Str
plain = |header, flags, statement| match statement {
	Ok(s) => s.block(header, flags)
	Err(e) => "-- unsupported ${header}: ${Str.inspect(e)}"
}

## A write, then the rows it changed.
then_read : Try(Surreal.Statement, Surreal.Error), Try(Surreal.Statement, Surreal.Error) -> Try(Surreal.Statement, Surreal.Error)
then_read = |first, second| match (first, second) {
	(Ok(a), Ok(b)) => a.then(b)
	(Err(e), _) | (_, Err(e)) => Err(e)
}

rejects : Str, Str, Try(Surreal.Statement, Surreal.Error) -> Str
rejects = |name, why, statement| plain("-- rejects: ${name}", ["-- error: ${why}"], statement)

pip : Patient
pip = { id: "pip", name: "Pip", species: Dog, age: 1, weight_kg: 6.5, owner: owner_link(jon), allergies: [], vaccines: [] }

meloxicam_form : MedicationForm
meloxicam_form = { id: "meloxicam", name: "Meloxicam", form: "liquid", unit_price: 2.5 }

meloxicam : Medication
meloxicam = medication("meloxicam", "Meloxicam", "liquid", 2.5, 0)

new_edge : Treats
new_edge = edge("e9", tia, rex, 2026, Bool.False)

refill_param : RestockParam
refill_param = { floor: 60, add: 100 }

cutoff : Surreal.Datetime
cutoff = at("2026-02-15T00:00:00Z")

schema_block : Str
schema_block = match Surreal.schema([owner_def, vet_def, medication_def, patient_def, visit_def, treats_def]) {
	Ok(text) => "-- schema\n${text}"
	Err(e) => "-- bad schema: ${Str.inspect(e)}"
}

reads : List(Str)
reads = [
	block(
		"-- query: owners_in_city",
		["-- ordered"],
		Surreal.from(owners).filter_by(in_city).select(owner_card).order_by(|r| r.id, Asc).bind({ city: "Oslo" }),
		Surreal.literal(owners_in_city("Oslo")),
	),
	block(
		"-- query: vip_owners",
		[],
		Surreal.from(owners).filter(is_vip).select(owner_card).bind({}),
		Surreal.literal(seed_owners.keep_if(is_vip).map(owner_card)),
	),
	block(
		"-- query: referrals",
		[],
		Surreal.from(owners).filter(|who| who.?referred_by.is_ok()).select(referral_line).bind({}),
		Surreal.literal(seed_owners.keep_if(|who| who.?referred_by.is_ok()).map(referral_line)),
	),
	block(
		"-- query: pet_roster",
		["-- ordered"],
		Surreal.from(patients).select(pet_line).order_by(|r| r.id, Asc).bind({}),
		Surreal.literal(seed_patients.map(pet_line)),
	),
	block(
		"-- query: wide_winged",
		[],
		Surreal.from(patients).filter(wide_wings).select_value(|pet| pet.name).bind({}),
		Surreal.literal(seed_patients.keep_if(wide_wings).map(|p| p.name)),
	),
	block(
		"-- query: chips",
		[],
		Surreal.from(patients).select(chip_line).bind({}),
		Surreal.literal(seed_patients.map(chip_line)),
	),
	block(
		"-- query: vaccinated_by_ruth",
		[],
		Surreal.from(patients).filter(vaccinated_by_ruth).select(vaccine_line).bind({}),
		Surreal.literal(seed_patients.keep_if(vaccinated_by_ruth).map(vaccine_line)),
	),
	block(
		"-- query: recent_visits",
		["-- ordered"],
		Surreal.from(visits).filter_by(seen_since).select(visit_line).order_by(|r| r.id, Asc).bind({ since: at("2026-03-01T00:00:00Z") }),
		Surreal.literal(seed_visits.keep_if(|v| seen_since({ since: at("2026-03-01T00:00:00Z") }, v)).map(visit_line)),
	),
	block(
		"-- query: past_visits",
		[],
		Surreal.from(visits).filter(|stay| stay.seen < Surreal.Time.now()).select_value(|stay| stay.id).bind({}),
		Surreal.literal(seed_visits.map(|stay| stay.id)),
	),
	block(
		"-- query: follow_ups",
		[],
		Surreal.from(visits).filter(needs_follow_up).select(outcome_line).bind({}),
		Surreal.literal(seed_visits.keep_if(needs_follow_up).map(outcome_line)),
	),
	block(
		"-- query: case_load",
		[],
		Surreal.from(vets).outgoing(treats).select(|(doc, links)| case_load(doc, links)).bind({}),
		Surreal.literal(seed_vets.map(|v| case_load(v, edges_of_vet(v)))),
	),
	block(
		"-- query: teams",
		[],
		Surreal.from(patients).incoming(treats).select(|(pet, links)| team_line(pet, links)).bind({}),
		Surreal.literal(seed_patients.map(|p| team_line(p, edges_of_patient(p)))),
	),
	block(
		"-- query: ledger",
		["-- ordered"],
		Surreal.from(visits).group_by(|stay| stay.vet.get().name).aggregate(ledger_line).order_by(|line| line.revenue, Desc).limit(2).bind({}),
		Surreal.literal(ledger_in_memory.sort_by_reversed(|l| l.revenue).take_first(2)),
	),
	block(
		"-- query: eldest",
		["-- ordered"],
		Surreal.from(patients).select(patient_age).order_by(|r| r.age, Desc).limit(3).bind({}),
		Surreal.literal(seed_patients.map(patient_age).sort_by_reversed(|r| r.age).take_first(3)),
	),
	block(
		"-- query: labels",
		["-- ordered"],
		Surreal.from(medications).select_value(|med| med.label).order_by(|l| l, Asc).bind({}),
		Surreal.literal(seed_medications.map(|m| m.label)),
	),
	block(
		"-- query: second_page",
		["-- ordered"],
		Surreal.from(patients).select(pet_line).order_by(|r| r.id, Asc).limit(2).start(2).bind({}),
		Surreal.literal(seed_patients.map(pet_line).drop_first(2).take_first(2)),
	),
	block(
		"-- query: fetched_links",
		[],
		Surreal.from(patients).fetch(|pet| pet.owner).fetch_each(|pet| pet.vaccines.map(|shot| shot.vet)).select(contact_line).bind({}),
		Surreal.literal(seed_patients.map(contact_line)),
	),
	block(
		"-- query: cheaper_than",
		[],
		cheaper_than(0.9),
		Surreal.literal(seed_medications.keep_if(|m| m.unit_price < 0.9).map(stored)),
	),
]

script : Str
script = Str.join_with([schema_block].concat(seeds).concat(reads).concat(refusals).concat(writes), "\n\n")

seeds : List(Str)
seeds = [
	plain("-- seed: vet", [], vets.insert(seed_vets)),
	plain("-- seed: owner", [], owners.insert(seed_owners)),
	plain("-- seed: medication", [], medications.insert(seed_medications)),
	plain("-- seed: patient", [], patients.insert(seed_patients)),
	plain("-- seed: visit", [], visits.insert(seed_visits)),
	plain("-- seed: treats", [], treats.insert(seed_treats)),
]

refusals : List(Str)
refusals = [
	rejects("check_as_assert", "field `weight_kg`", patients.create(light_patient)),
	rejects("check_as_event", "visit: items need a fee", visits.create(free_medication)),
	rejects("assert_email", "field `email`", owners.create(bad_email_owner)),
	rejects("assert_on_nested_path", "field `contact.email`", vets.create({ ..shared_email_vet, contact: { email: "no-at-sign", phone: "1" } })),
	rejects("assert_on_union", "field `species`", patients.create(wingless_bird)),
	rejects("assert_on_outcome", "field `outcome`", visits.create(endless_followup)),
	rejects("assert_each_tag", "field `tags`", owners.create(blank_tag_owner)),
	rejects("assert_each_dose", "field `items.*.doses`", visits.create({ ..visit_of("v1"), id: "bad", items: [zero_doses] })),
	rejects("assert_each_vaccine", "field `vaccines.*.name`", patients.create(blank_vaccine_patient)),
	rejects("unique_nested_path", "already contains", vets.create(shared_email_vet)),
	rejects("unique_composite_with_link", "already contains", patients.create(twin_patient)),
	rejects("unique_composite_address", "already contains", owners.create(neighbour)),
	rejects("unique_edge_ends", "already contains", treats.relate(repeated_edge)),
	rejects("check_on_edge", "field `since_year`", treats.relate(early_edge)),
	rejects("u8_range", "field `years`", unchecked_vets.create(old_vet)),
	rejects("readonly_license", "field is readonly", vets.update(|v| v.id == "ruth", |v| { ..v, license: "VET-2000" }).bind({})),
	rejects("link_exists_root", "field `owner`", patients.create(ghost_owner_patient)),
	rejects("link_exists_in_list_of_records", "field `items.*.medication`", visits.create(ghost_medication_visit)),
	rejects("link_exists_in_optional_record", "field `chip.implanted_by`", patients.create(ghost_chip_patient)),
	rejects("link_exists_in_union_arm", "field `outcome`", visits.create(ghost_referral_visit)),
	rejects("link_exists_in_vaccines", "field `vaccines.*.vet`", patients.create(ghost_vaccine_patient)),
	rejects("delete_vet_with_visits", "ON DELETE REJECT", vets.delete(|v| v.id == "ruth").bind({})),
	rejects("delete_vet_in_a_referral", "is referenced by visit.outcome.to", vets.delete(|v| v.id == "tia").bind({})),
	rejects("delete_medication_in_a_visit", "is referenced by visit.items[*].medication", medications.delete(|m| m.id == "amoxicillin").bind({})),
]

patients_now : List(Patient)
patients_now = [bo, kiwi, luna, mimi, pip, rex, zed]

medications_now : List(Medication)
medications_now = seed_medications.append(meloxicam)

without_aspirin : Patient -> Patient
without_aspirin = |p| { ..p, allergies: p.allergies.keep_if(|a| a.get().id != "aspirin") }

owned_by_noor : Patient -> Bool
owned_by_noor = |p| p.owner.get().id == "noor"

expect without_aspirin(rex).allergies.map(|a| a.get().id) == ["amoxicillin"]
expect refill(refill_param, { ..ivermectin, stock: 10 }).stock == 110
expect certified(tia).years == 4

visits_now : List(Visit)
visits_now = seed_visits.keep_if(|v| !owned_by_noor(v.patient.get()))

writes : List(Str)
writes = [
	block(
		"-- write: admit_patient",
		["-- ordered"],
		then_read(patients.create(pip), Surreal.from(patients).select(pet_line).order_by(|r| r.id, Asc).bind({})),
		Surreal.literal(patients_now.map(pet_line)),
	),
	block(
		"-- write: add_medication",
		["-- ordered"],
		then_read(medication_forms.create(meloxicam_form), Surreal.from(medications).select(stock_line).order_by(|r| r.id, Asc).bind({})),
		Surreal.literal(medications_now.map(stock_line)),
	),
	block(
		"-- write: restock",
		["-- ordered"],
		then_read(
			medications.update_by(low_stock, refill).bind(refill_param),
			Surreal.from(medications).select(stock_line).order_by(|r| r.id, Asc).bind({}),
		),
		Surreal.literal(medications_now.map(|m| if (low_stock(refill_param, m)) refill(refill_param, m) else m).map(stock_line)),
	),
	block(
		"-- write: certify_vet",
		["-- ordered"],
		then_read(
			vets.update(|doc| doc.id == "tia", certified).bind({}),
			Surreal.from(vets).select(specialty_line).order_by(|r| r.id, Asc).bind({}),
		),
		Surreal.literal(seed_vets.map(|v| if (v.id == "tia") certified(v) else v).map(specialty_line)),
	),
	block(
		"-- write: delete_medication_unsets_allergies",
		["-- ordered"],
		then_read(
			medications.delete(|m| m.id == "aspirin").bind({}),
			Surreal.from(patients).select(allergy_line).order_by(|r| r.id, Asc).bind({}),
		),
		Surreal.literal(patients_now.map(without_aspirin).map(allergy_line)),
	),
	block(
		"-- write: relate_vet",
		["-- ordered"],
		then_read(treats.relate(new_edge), Surreal.from(treats).select(edge_line).order_by(|r| r.id, Asc).bind({})),
		Surreal.literal(seed_treats.append(new_edge).map(edge_line)),
	),
	block(
		"-- write: delete_owner_cascades_to_patients",
		["-- ordered"],
		then_read(
			owners.delete(|o| o.id == "noor").bind({}),
			Surreal.from(patients).select(|p| { id: p.id }).order_by(|r| r.id, Asc).bind({}),
		),
		Surreal.literal(patients_now.keep_if(|p| !owned_by_noor(p)).map(|p| { id: p.id })),
	),
	block(
		"-- query: visits_left_by_the_cascade",
		["-- ordered"],
		Surreal.from(visits).select(|v| { id: v.id }).order_by(|r| r.id, Asc).bind({}),
		Surreal.literal(visits_now.map(|v| { id: v.id })),
	),
	block(
		"-- query: edges_left_by_the_cascade",
		["-- ordered"],
		Surreal.from(treats).select(edge_line).order_by(|r| r.id, Asc).bind({}),
		Surreal.literal(seed_treats.append(new_edge).keep_if(|e| !owned_by_noor(e.to.get())).map(edge_line)),
	),
	block(
		"-- write: retention",
		["-- ordered"],
		then_read(
			visits.delete_by(too_old).bind({ before: cutoff }),
			Surreal.from(visits).select(|v| { id: v.id }).order_by(|r| r.id, Asc).bind({}),
		),
		Surreal.literal(visits_now.keep_if(|v| !too_old({ before: cutoff }, v)).map(|v| { id: v.id })),
	),
]

expect "${script}\n" == expected_output

main! = |_args| {
	echo!("${script}\n")
	Ok({})
}
