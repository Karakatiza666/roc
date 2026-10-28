-- schema
DEFINE TABLE OVERWRITE owner SCHEMAFULL;
DEFINE TABLE OVERWRITE vet SCHEMAFULL;
DEFINE TABLE OVERWRITE medication SCHEMAFULL;
DEFINE TABLE OVERWRITE patient SCHEMAFULL;
DEFINE TABLE OVERWRITE visit SCHEMAFULL;
DEFINE TABLE OVERWRITE treats TYPE RELATION IN vet OUT patient ENFORCED SCHEMAFULL;
DEFINE FIELD OVERWRITE address ON owner TYPE object;
DEFINE FIELD OVERWRITE address.city ON owner TYPE string;
DEFINE FIELD OVERWRITE address.line ON owner TYPE string;
DEFINE FIELD OVERWRITE address.zip ON owner TYPE option<string>;
DEFINE FIELD OVERWRITE email ON owner TYPE string ASSERT string::contains($value, '@') AND (!string::starts_with($value, '@'));
DEFINE FIELD OVERWRITE name ON owner TYPE string ASSERT $value != '';
DEFINE FIELD OVERWRITE phone ON owner TYPE option<string>;
DEFINE FIELD OVERWRITE referred_by ON owner TYPE option<record<owner>> REFERENCE ON DELETE UNSET ASSERT ($value = NONE OR (record::exists($value)));
DEFINE FIELD OVERWRITE tags ON owner TYPE array<string> DEFAULT [] ASSERT $value.all(|$item| $item != '');
DEFINE FIELD OVERWRITE contact ON vet TYPE object;
DEFINE FIELD OVERWRITE contact.email ON vet TYPE string ASSERT string::is_email($value);
DEFINE FIELD OVERWRITE contact.phone ON vet TYPE string;
DEFINE FIELD OVERWRITE license ON vet TYPE string READONLY ASSERT string::starts_with($value, 'VET-');
DEFINE FIELD OVERWRITE name ON vet TYPE string;
DEFINE FIELD OVERWRITE rate ON vet TYPE decimal ASSERT $value > 0.0dec;
DEFINE FIELD OVERWRITE specialty ON vet TYPE "Dental" | "General" | { kind: "Surgery", board: string };
DEFINE FIELD OVERWRITE years ON vet TYPE int ASSERT $value >= 0 AND $value <= 255;
DEFINE FIELD OVERWRITE form ON medication TYPE string;
DEFINE FIELD OVERWRITE label ON medication TYPE string VALUE $this.name + ' (' + $this.form + ')';
DEFINE FIELD OVERWRITE name ON medication TYPE string;
DEFINE FIELD OVERWRITE stock ON medication TYPE int DEFAULT 0 ASSERT $value >= -2147483648 AND $value <= 2147483647;
DEFINE FIELD OVERWRITE unit_price ON medication TYPE decimal;
DEFINE FIELD OVERWRITE age ON patient TYPE int ASSERT $value >= 0 AND $value <= 255;
DEFINE FIELD OVERWRITE allergies ON patient TYPE array<record<medication>> DEFAULT [] REFERENCE ON DELETE UNSET ASSERT $value.all(|$e1| record::exists($e1));
DEFINE FIELD OVERWRITE chip ON patient TYPE option<object>;
DEFINE FIELD OVERWRITE chip.code ON patient TYPE string;
DEFINE FIELD OVERWRITE chip.implanted_by ON patient TYPE record<vet> ASSERT record::exists($value);
DEFINE FIELD OVERWRITE name ON patient TYPE string;
DEFINE FIELD OVERWRITE owner ON patient TYPE record<owner> REFERENCE ON DELETE CASCADE ASSERT record::exists($value);
DEFINE FIELD OVERWRITE species ON patient TYPE { kind: "Bird", wingspan_cm: int } | "Cat" | "Dog" | { kind: "Exotic", latin: string } ASSERT ((IF $value.kind = 'Bird' THEN $value.wingspan_cm >= 0 AND $value.wingspan_cm <= 255 ELSE true END)) AND ((IF $value.kind = 'Bird' THEN $value.wingspan_cm > 0 ELSE true END));
DEFINE FIELD OVERWRITE vaccines ON patient TYPE array<object> ASSERT $value.all(|$e| object::keys($e).all(|$k| $k IN ['given', 'name', 'vet']));
DEFINE FIELD OVERWRITE vaccines[*].given ON patient TYPE string;
DEFINE FIELD OVERWRITE vaccines[*].name ON patient TYPE string ASSERT $value != '';
DEFINE FIELD OVERWRITE vaccines[*].vet ON patient TYPE record<vet> ASSERT record::exists($value);
DEFINE FIELD OVERWRITE weight_kg ON patient TYPE decimal ASSERT $value > 0.0dec;
DEFINE FIELD OVERWRITE fee ON visit TYPE decimal ASSERT $value >= 0.0dec;
DEFINE FIELD OVERWRITE items ON visit TYPE array<object> ASSERT $value.all(|$e| object::keys($e).all(|$k| $k IN ['doses', 'medication']));
DEFINE FIELD OVERWRITE items[*].doses ON visit TYPE int ASSERT $value > 0;
DEFINE FIELD OVERWRITE items[*].medication ON visit TYPE record<medication> ASSERT record::exists($value);
DEFINE FIELD OVERWRITE outcome ON visit TYPE { kind: "Followup", days: int } | { kind: "Referred", reason: string, to: record<vet> } | "Treated" ASSERT ((IF $value.kind = 'Followup' THEN $value.days >= 0 AND $value.days <= 255 ELSE true END)) AND ((IF $value.kind = 'Referred' THEN record::exists($value.to) ELSE true END)) AND ((IF $value.kind = 'Followup' THEN ($value.days > 0) AND ($value.days <= 90) ELSE true END));
DEFINE FIELD OVERWRITE patient ON visit TYPE record<patient> REFERENCE ON DELETE CASCADE ASSERT record::exists($value);
DEFINE FIELD OVERWRITE seen ON visit TYPE datetime;
DEFINE FIELD OVERWRITE vet ON visit TYPE record<vet> REFERENCE ON DELETE REJECT ASSERT record::exists($value);
DEFINE FIELD OVERWRITE primary ON treats TYPE bool;
DEFINE FIELD OVERWRITE since_year ON treats TYPE int ASSERT $value >= 1990;
DEFINE INDEX OVERWRITE owner_email_unique ON owner FIELDS email UNIQUE;
DEFINE INDEX OVERWRITE owner_address_city_address_line_unique ON owner FIELDS address.city, address.line UNIQUE;
DEFINE INDEX OVERWRITE owner_address_city_index ON owner FIELDS address.city;
DEFINE INDEX OVERWRITE vet_contact_email_unique ON vet FIELDS contact.email UNIQUE;
DEFINE INDEX OVERWRITE patient_name_owner_unique ON patient FIELDS name, owner UNIQUE;
DEFINE INDEX OVERWRITE patient_age_index ON patient FIELDS age;
DEFINE INDEX OVERWRITE patient_chip_implanted_by_link ON patient FIELDS chip.implanted_by;
DEFINE INDEX OVERWRITE patient_vaccines_vet_link ON patient FIELDS vaccines[*].vet;
DEFINE INDEX OVERWRITE visit_seen_index ON visit FIELDS seen;
DEFINE INDEX OVERWRITE visit_items_medication_link ON visit FIELDS items[*].medication;
DEFINE INDEX OVERWRITE treats_in_out_unique ON treats FIELDS in, out UNIQUE;
DEFINE EVENT OVERWRITE visit_check_items_need_a_fee ON visit WHEN $event IN ['CREATE', 'UPDATE'] THEN { IF !(($after.items.len() = 0) OR ($after.fee > 0.0dec)) { THROW 'visit: items need a fee' } };
DEFINE EVENT OVERWRITE patient_chip_implanted_by_on_delete ON vet WHEN $event = 'DELETE' THEN { IF (SELECT VALUE id FROM patient WHERE chip.implanted_by = $before.id LIMIT 1) != [] { THROW <string>$before.id + ' is referenced by patient.chip.implanted_by' } };
DEFINE EVENT OVERWRITE patient_vaccines_vet_on_delete ON vet WHEN $event = 'DELETE' THEN { IF (SELECT VALUE id FROM patient WHERE vaccines.any(|$e1| $e1.vet = $before.id) LIMIT 1) != [] { THROW <string>$before.id + ' is referenced by patient.vaccines[*].vet' } };
DEFINE EVENT OVERWRITE visit_items_medication_on_delete ON medication WHEN $event = 'DELETE' THEN { IF (SELECT VALUE id FROM visit WHERE items.any(|$e1| $e1.medication = $before.id) LIMIT 1) != [] { THROW <string>$before.id + ' is referenced by visit.items[*].medication' } };
DEFINE EVENT OVERWRITE visit_outcome_Referred_to_on_delete ON vet WHEN $event = 'DELETE' THEN { IF (SELECT VALUE id FROM visit WHERE (outcome.kind = 'Referred' AND outcome.to = $before.id) LIMIT 1) != [] { THROW <string>$before.id + ' is referenced by visit.outcome.to' } };

-- seed: vet
BEGIN;
INSERT INTO vet [{ contact: { email: 'ruth@paws.example', phone: '555-0101' }, id: 'ruth', license: 'VET-1001', name: 'Ruth Okafor', rate: 80.0dec, specialty: 'General', years: 12 }, { contact: { email: 'sam@paws.example', phone: '555-0102' }, id: 'sam', license: 'VET-1002', name: 'Sam Petrov', rate: 140.0dec, specialty: { kind: 'Surgery', board: 'ACVS' }, years: 8 }, { contact: { email: 'tia@paws.example', phone: '555-0103' }, id: 'tia', license: 'VET-1003', name: 'Tia Brandt', rate: 95.5dec, specialty: 'Dental', years: 3 }];
COMMIT;

-- seed: owner
BEGIN;
INSERT INTO owner [{ address: { city: 'Oslo', line: 'Storgata 4', zip: '0155' }, email: 'jon@example.org', id: 'jon', name: 'Jon Berg', tags: ['new'] }, { address: { city: 'Lyon', line: 'Rue Merciere 9' }, email: 'lena@example.org', id: 'lena', name: 'Lena Roux', phone: '555-0188', tags: [] }, { address: { city: 'Oslo', line: 'Akersgata 12', zip: '0158' }, email: 'mara@example.org', id: 'mara', name: 'Mara Ito', phone: '555-0142', tags: ['vip'] }, { address: { city: 'Porto', line: 'Rua das Flores 7' }, email: 'noor@example.org', id: 'noor', name: 'Noor Haddad', referred_by: owner:⟨mara⟩, tags: ['vip', 'new'] }];
COMMIT;

-- seed: medication
BEGIN;
INSERT INTO medication [{ form: 'tablet', id: 'amoxicillin', label: 'Amoxicillin (tablet)', name: 'Amoxicillin', stock: 200, unit_price: 0.8dec }, { form: 'tablet', id: 'aspirin', label: 'Aspirin (tablet)', name: 'Aspirin', stock: 500, unit_price: 0.2dec }, { form: 'capsule', id: 'gabapentin', label: 'Gabapentin (capsule)', name: 'Gabapentin', stock: 40, unit_price: 1.4dec }, { form: 'injection', id: 'ivermectin', label: 'Ivermectin (injection)', name: 'Ivermectin', stock: 15, unit_price: 3.5dec }];
COMMIT;

-- seed: patient
BEGIN;
INSERT INTO patient [{ age: 12, allergies: [], id: 'bo', name: 'Bo', owner: owner:⟨jon⟩, species: 'Dog', vaccines: [{ given: '2025-05-02', name: 'rabies', vet: vet:⟨ruth⟩ }], weight_kg: 31.5dec }, { age: 2, allergies: [], id: 'kiwi', name: 'Kiwi', owner: owner:⟨lena⟩, species: { kind: 'Bird', wingspan_cm: 25 }, vaccines: [], weight_kg: 0.4dec }, { age: 3, allergies: [medication:⟨aspirin⟩], chip: { code: '985-112', implanted_by: vet:⟨sam⟩ }, id: 'luna', name: 'Luna', owner: owner:⟨mara⟩, species: 'Cat', vaccines: [], weight_kg: 4.2dec }, { age: 9, allergies: [], id: 'mimi', name: 'Mimi', owner: owner:⟨noor⟩, species: 'Cat', vaccines: [], weight_kg: 5.1dec }, { age: 5, allergies: [medication:⟨aspirin⟩, medication:⟨amoxicillin⟩], chip: { code: '985-100', implanted_by: vet:⟨ruth⟩ }, id: 'rex', name: 'Rex', owner: owner:⟨mara⟩, species: 'Dog', vaccines: [{ given: '2025-06-11', name: 'rabies', vet: vet:⟨ruth⟩ }, { given: '2025-06-11', name: 'distemper', vet: vet:⟨sam⟩ }], weight_kg: 28.0dec }, { age: 4, allergies: [], id: 'zed', name: 'Zed', owner: owner:⟨noor⟩, species: { kind: 'Exotic', latin: 'gecko' }, vaccines: [], weight_kg: 0.1dec }];
COMMIT;

-- seed: visit
BEGIN;
INSERT INTO visit [{ fee: 80.0dec, id: 'v1', items: [{ doses: 14, medication: medication:⟨amoxicillin⟩ }], outcome: 'Treated', patient: patient:⟨rex⟩, seen: d'2026-01-10T09:00:00Z', vet: vet:⟨ruth⟩ }, { fee: 140.0dec, id: 'v2', items: [], outcome: { kind: 'Followup', days: 14 }, patient: patient:⟨rex⟩, seen: d'2026-02-03T14:30:00Z', vet: vet:⟨sam⟩ }, { fee: 80.0dec, id: 'v3', items: [{ doses: 10, medication: medication:⟨gabapentin⟩ }], outcome: { kind: 'Referred', reason: 'dental scale', to: vet:⟨tia⟩ }, patient: patient:⟨luna⟩, seen: d'2026-02-20T10:15:00Z', vet: vet:⟨ruth⟩ }, { fee: 80.0dec, id: 'v4', items: [{ doses: 7, medication: medication:⟨amoxicillin⟩ }, { doses: 1, medication: medication:⟨ivermectin⟩ }], outcome: 'Treated', patient: patient:⟨bo⟩, seen: d'2026-03-05T11:00:00Z', vet: vet:⟨ruth⟩ }, { fee: 140.0dec, id: 'v5', items: [], outcome: 'Treated', patient: patient:⟨mimi⟩, seen: d'2026-03-18T16:45:00Z', vet: vet:⟨sam⟩ }, { fee: 40.0dec, id: 'v6', items: [{ doses: 1, medication: medication:⟨ivermectin⟩ }], outcome: { kind: 'Followup', days: 7 }, patient: patient:⟨kiwi⟩, seen: d'2026-04-02T08:30:00Z', vet: vet:⟨ruth⟩ }, { fee: 60.0dec, id: 'v7', items: [], outcome: 'Treated', patient: patient:⟨zed⟩, seen: d'2026-04-11T13:00:00Z', vet: vet:⟨sam⟩ }];
COMMIT;

-- seed: treats
BEGIN;
INSERT RELATION INTO treats [{ in: vet:⟨ruth⟩, id: 'e1', primary: true, since_year: 2022, out: patient:⟨rex⟩ }, { in: vet:⟨sam⟩, id: 'e2', primary: false, since_year: 2024, out: patient:⟨rex⟩ }, { in: vet:⟨ruth⟩, id: 'e3', primary: true, since_year: 2020, out: patient:⟨bo⟩ }, { in: vet:⟨sam⟩, id: 'e4', primary: true, since_year: 2025, out: patient:⟨luna⟩ }, { in: vet:⟨tia⟩, id: 'e5', primary: false, since_year: 2025, out: patient:⟨luna⟩ }, { in: vet:⟨ruth⟩, id: 'e6', primary: true, since_year: 2026, out: patient:⟨kiwi⟩ }, { in: vet:⟨sam⟩, id: 'e7', primary: true, since_year: 2023, out: patient:⟨mimi⟩ }, { in: vet:⟨ruth⟩, id: 'e8', primary: true, since_year: 2026, out: patient:⟨zed⟩ }];
COMMIT;

-- query: owners_in_city
-- ordered
-- roc: [{ id: 'jon', name: 'Jon Berg', phone: 'none' }, { id: 'mara', name: 'Mara Ito', phone: '555-0142' }]
LET $city = 'Oslo';
SELECT record::id(id) AS id, name AS name, phone ?? 'none' AS phone FROM owner WHERE address.city = $city ORDER BY id;

-- query: vip_owners
-- roc: [{ id: 'mara', name: 'Mara Ito', phone: '555-0142' }, { id: 'noor', name: 'Noor Haddad', phone: 'none' }]
SELECT record::id(id) AS id, name AS name, phone ?? 'none' AS phone FROM owner WHERE tags CONTAINS 'vip';

-- query: referrals
-- roc: [{ by: 'Mara Ito', id: 'noor' }]
SELECT (IF referred_by IS NONE THEN 'nobody' ELSE referred_by.name END) AS by, record::id(id) AS id FROM owner WHERE referred_by IS NOT NONE;

-- query: pet_roster
-- ordered
-- roc: [{ id: 'bo', kind: 'dog', owner: 'Jon Berg' }, { id: 'kiwi', kind: 'bird', owner: 'Lena Roux' }, { id: 'luna', kind: 'cat', owner: 'Mara Ito' }, { id: 'mimi', kind: 'cat', owner: 'Noor Haddad' }, { id: 'rex', kind: 'dog', owner: 'Mara Ito' }, { id: 'zed', kind: 'gecko', owner: 'Noor Haddad' }]
SELECT record::id(id) AS id, (IF species.kind = 'Bird' THEN 'bird' ELSE IF species = 'Cat' THEN 'cat' ELSE IF species = 'Dog' THEN 'dog' ELSE species.latin END) AS kind, owner.name AS owner FROM patient ORDER BY id;

-- query: wide_winged
-- roc: ['Kiwi']
SELECT VALUE name FROM patient WHERE (IF species.kind = 'Bird' THEN species.wingspan_cm >= 20 ELSE false END);

-- query: chips
-- roc: [{ by: 'nobody', chip: 'none', id: 'bo' }, { by: 'nobody', chip: 'none', id: 'kiwi' }, { by: 'Sam Petrov', chip: '985-112', id: 'luna' }, { by: 'nobody', chip: 'none', id: 'mimi' }, { by: 'Ruth Okafor', chip: '985-100', id: 'rex' }, { by: 'nobody', chip: 'none', id: 'zed' }]
SELECT (IF chip IS NONE THEN 'nobody' ELSE chip.implanted_by.name END) AS by, (IF chip IS NONE THEN 'none' ELSE chip.code END) AS chip, record::id(id) AS id FROM patient;

-- query: vaccinated_by_ruth
-- roc: [{ id: 'bo', vets: ['Ruth Okafor'] }, { id: 'rex', vets: ['Ruth Okafor', 'Sam Petrov'] }]
SELECT record::id(id) AS id, vaccines.map(|$v1| $v1.vet.name) AS vets FROM patient WHERE vaccines.any(|$v1| $v1.vet = vet:⟨ruth⟩);

-- query: recent_visits
-- ordered
-- roc: [{ bill: 89.1dec, id: 'v4', patient: 'Bo', vet: 'Ruth Okafor' }, { bill: 140.0dec, id: 'v5', patient: 'Mimi', vet: 'Sam Petrov' }, { bill: 43.5dec, id: 'v6', patient: 'Kiwi', vet: 'Ruth Okafor' }, { bill: 60.0dec, id: 'v7', patient: 'Zed', vet: 'Sam Petrov' }]
LET $since = d'2026-03-01T00:00:00Z';
SELECT fee + math::sum(items.map(|$v1| <decimal>$v1.doses * $v1.medication.unit_price)) AS bill, record::id(id) AS id, patient.name AS patient, vet.name AS vet FROM visit WHERE $since <= seen ORDER BY id;

-- query: past_visits
-- roc: ['v1', 'v2', 'v3', 'v4', 'v5', 'v6', 'v7']
SELECT VALUE record::id(id) FROM visit WHERE seen < time::now();

-- query: follow_ups
-- roc: [{ id: 'v2', text: 'follow-up' }, { id: 'v3', text: 'referred to Tia Brandt' }, { id: 'v6', text: 'follow-up' }]
SELECT record::id(id) AS id, (IF outcome.kind = 'Followup' THEN 'follow-up' ELSE IF outcome.kind = 'Referred' THEN 'referred to ' + outcome.to.name ELSE 'treated' END) AS text FROM visit WHERE (IF outcome = 'Treated' THEN false ELSE true END);

-- query: case_load
-- roc: [{ name: 'Ruth Okafor', patients: 4, primary: 4 }, { name: 'Sam Petrov', patients: 3, primary: 2 }, { name: 'Tia Brandt', patients: 1, primary: 0 }]
SELECT name AS name, ->treats.len() AS patients, ->treats.filter(|$v1| $v1.primary).len() AS primary FROM vet;

-- query: teams
-- roc: [{ lead: ['Ruth Okafor'], name: 'Bo', team: 1 }, { lead: ['Ruth Okafor'], name: 'Kiwi', team: 1 }, { lead: ['Sam Petrov'], name: 'Luna', team: 2 }, { lead: ['Sam Petrov'], name: 'Mimi', team: 1 }, { lead: ['Ruth Okafor'], name: 'Rex', team: 2 }, { lead: ['Ruth Okafor'], name: 'Zed', team: 1 }]
SELECT <-treats.filter(|$v1| $v1.primary).map(|$v2| $v2.in.name) AS lead, name AS name, <-treats.len() AS team FROM patient;

-- query: ledger
-- ordered
-- roc: [{ avg_fee: 113.33333333333333f, revenue: 340.0dec, vet: 'Sam Petrov', visits: 3 }, { avg_fee: 70f, revenue: 280.0dec, vet: 'Ruth Okafor', visits: 4 }]
SELECT math::mean(<float>fee) AS avg_fee, math::sum(fee) AS revenue, vet.name AS vet, count() AS visits FROM visit GROUP BY vet.name ORDER BY revenue DESC LIMIT 2;

-- query: eldest
-- ordered
-- roc: [{ age: 12, id: 'bo' }, { age: 9, id: 'mimi' }, { age: 5, id: 'rex' }]
SELECT age AS age, record::id(id) AS id FROM patient ORDER BY age DESC LIMIT 3;

-- query: labels
-- ordered
-- roc: ['Amoxicillin (tablet)', 'Aspirin (tablet)', 'Gabapentin (capsule)', 'Ivermectin (injection)']
SELECT VALUE label FROM medication ORDER BY label;

-- query: second_page
-- ordered
-- roc: [{ id: 'luna', kind: 'cat', owner: 'Mara Ito' }, { id: 'mimi', kind: 'cat', owner: 'Noor Haddad' }]
SELECT record::id(id) AS id, (IF species.kind = 'Bird' THEN 'bird' ELSE IF species = 'Cat' THEN 'cat' ELSE IF species = 'Dog' THEN 'dog' ELSE species.latin END) AS kind, owner.name AS owner FROM patient ORDER BY id LIMIT 2 START 2;

-- query: fetched_links
-- roc: [{ city: 'Oslo', id: 'bo', vets: ['Ruth Okafor'] }, { city: 'Lyon', id: 'kiwi', vets: [] }, { city: 'Oslo', id: 'luna', vets: [] }, { city: 'Porto', id: 'mimi', vets: [] }, { city: 'Oslo', id: 'rex', vets: ['Ruth Okafor', 'Sam Petrov'] }, { city: 'Porto', id: 'zed', vets: [] }]
SELECT owner.address.city AS city, record::id(id) AS id, vaccines.map(|$v1| $v1.vet.name) AS vets FROM patient FETCH owner, vaccines[*].vet;

-- query: cheaper_than
-- roc: [{ form: 'tablet', id: medication:⟨amoxicillin⟩, label: 'Amoxicillin (tablet)', name: 'Amoxicillin', stock: 200, unit_price: 0.8dec }, { form: 'tablet', id: medication:⟨aspirin⟩, label: 'Aspirin (tablet)', name: 'Aspirin', stock: 500, unit_price: 0.2dec }]
LET $_1 = 0.9dec;
SELECT * FROM medication WHERE unit_price < $_1;

-- rejects: check_as_assert
-- error: field `weight_kg`
CREATE patient:⟨bad⟩ CONTENT { age: 12, allergies: [], name: 'Featherweight', owner: owner:⟨jon⟩, species: 'Dog', vaccines: [{ given: '2025-05-02', name: 'rabies', vet: vet:⟨ruth⟩ }], weight_kg: 0.0dec };

-- rejects: check_as_event
-- error: visit: items need a fee
CREATE visit:⟨v8⟩ CONTENT { fee: 0.0dec, items: [{ doses: 14, medication: medication:⟨amoxicillin⟩ }], outcome: 'Treated', patient: patient:⟨rex⟩, seen: d'2026-01-10T09:00:00Z', vet: vet:⟨ruth⟩ };

-- rejects: assert_email
-- error: field `email`
CREATE owner:⟨bad⟩ CONTENT { address: { city: 'Nowhere', line: '2 Main St' }, email: 'mailless.example.org', name: 'Mailless', tags: ['new'] };

-- rejects: assert_on_nested_path
-- error: field `contact.email`
CREATE vet:⟨bad⟩ CONTENT { contact: { email: 'no-at-sign', phone: '1' }, license: 'VET-9001', name: 'Sam Petrov', rate: 140.0dec, specialty: { kind: 'Surgery', board: 'ACVS' }, years: 8 };

-- rejects: assert_on_union
-- error: field `species`
CREATE patient:⟨bad⟩ CONTENT { age: 2, allergies: [], name: 'Wingless', owner: owner:⟨lena⟩, species: { kind: 'Bird', wingspan_cm: 0 }, vaccines: [], weight_kg: 0.4dec };

-- rejects: assert_on_outcome
-- error: field `outcome`
CREATE visit:⟨bad⟩ CONTENT { fee: 140.0dec, items: [], outcome: { kind: 'Followup', days: 0 }, patient: patient:⟨rex⟩, seen: d'2026-02-03T14:30:00Z', vet: vet:⟨sam⟩ };

-- rejects: assert_each_tag
-- error: field `tags`
CREATE owner:⟨bad⟩ CONTENT { address: { city: 'Nowhere', line: '1 Main St' }, email: 'blank@example.org', name: 'Blank', tags: [''] };

-- rejects: assert_each_dose
-- error: field `items.*.doses`
CREATE visit:⟨bad⟩ CONTENT { fee: 80.0dec, items: [{ doses: 0, medication: medication:⟨amoxicillin⟩ }], outcome: 'Treated', patient: patient:⟨rex⟩, seen: d'2026-01-10T09:00:00Z', vet: vet:⟨ruth⟩ };

-- rejects: assert_each_vaccine
-- error: field `vaccines.*.name`
CREATE patient:⟨bad⟩ CONTENT { age: 12, allergies: [], name: 'Unnamed', owner: owner:⟨jon⟩, species: 'Dog', vaccines: [{ given: '2025-01-01', name: '', vet: vet:⟨ruth⟩ }], weight_kg: 31.5dec };

-- rejects: unique_nested_path
-- error: already contains
CREATE vet:⟨bad⟩ CONTENT { contact: { email: 'sam@paws.example', phone: '555-0102' }, license: 'VET-9001', name: 'Sam Petrov', rate: 140.0dec, specialty: { kind: 'Surgery', board: 'ACVS' }, years: 8 };

-- rejects: unique_composite_with_link
-- error: already contains
CREATE patient:⟨rex2⟩ CONTENT { age: 5, allergies: [medication:⟨aspirin⟩, medication:⟨amoxicillin⟩], chip: { code: '985-100', implanted_by: vet:⟨ruth⟩ }, name: 'Rex', owner: owner:⟨mara⟩, species: 'Dog', vaccines: [{ given: '2025-06-11', name: 'rabies', vet: vet:⟨ruth⟩ }, { given: '2025-06-11', name: 'distemper', vet: vet:⟨sam⟩ }], weight_kg: 28.0dec };

-- rejects: unique_composite_address
-- error: already contains
CREATE owner:⟨bad⟩ CONTENT { address: { city: 'Oslo', line: 'Akersgata 12', zip: '0158' }, email: 'twin@example.org', name: 'Twin', phone: '555-0142', tags: ['vip'] };

-- rejects: unique_edge_ends
-- error: already contains
RELATE vet:⟨ruth⟩->treats:⟨e11⟩->patient:⟨rex⟩ CONTENT { primary: false, since_year: 2026 };

-- rejects: check_on_edge
-- error: field `since_year`
RELATE vet:⟨tia⟩->treats:⟨e10⟩->patient:⟨kiwi⟩ CONTENT { primary: false, since_year: 1980 };

-- rejects: u8_range
-- error: field `years`
CREATE vet:⟨bad⟩ CONTENT { contact: { email: 'old@paws.example', phone: '1' }, license: 'VET-9002', name: 'Methuselah', rate: 50.0dec, specialty: 'General', years: 300 };

-- rejects: readonly_license
-- error: field is readonly
UPDATE vet SET license = 'VET-2000' WHERE record::id(id) = 'ruth';

-- rejects: link_exists_root
-- error: field `owner`
CREATE patient:⟨bad⟩ CONTENT { age: 12, allergies: [], name: 'Stray', owner: owner:⟨nobody⟩, species: 'Dog', vaccines: [{ given: '2025-05-02', name: 'rabies', vet: vet:⟨ruth⟩ }], weight_kg: 31.5dec };

-- rejects: link_exists_in_list_of_records
-- error: field `items.*.medication`
CREATE visit:⟨bad⟩ CONTENT { fee: 80.0dec, items: [{ doses: 1, medication: medication:⟨ghost⟩ }], outcome: 'Treated', patient: patient:⟨rex⟩, seen: d'2026-01-10T09:00:00Z', vet: vet:⟨ruth⟩ };

-- rejects: link_exists_in_optional_record
-- error: field `chip.implanted_by`
CREATE patient:⟨bad⟩ CONTENT { age: 12, allergies: [], chip: { code: '000-000', implanted_by: vet:⟨ghost⟩ }, name: 'Chipped', owner: owner:⟨jon⟩, species: 'Dog', vaccines: [{ given: '2025-05-02', name: 'rabies', vet: vet:⟨ruth⟩ }], weight_kg: 31.5dec };

-- rejects: link_exists_in_union_arm
-- error: field `outcome`
CREATE visit:⟨bad⟩ CONTENT { fee: 140.0dec, items: [], outcome: { kind: 'Referred', reason: 'who', to: vet:⟨ghost⟩ }, patient: patient:⟨rex⟩, seen: d'2026-02-03T14:30:00Z', vet: vet:⟨sam⟩ };

-- rejects: link_exists_in_vaccines
-- error: field `vaccines.*.vet`
CREATE patient:⟨bad⟩ CONTENT { age: 12, allergies: [], name: 'Jabbed', owner: owner:⟨jon⟩, species: 'Dog', vaccines: [{ given: '2025-01-01', name: 'rabies', vet: vet:⟨ghost⟩ }], weight_kg: 31.5dec };

-- rejects: delete_vet_with_visits
-- error: ON DELETE REJECT
DELETE vet WHERE record::id(id) = 'ruth';

-- rejects: delete_vet_in_a_referral
-- error: is referenced by visit.outcome.to
DELETE vet WHERE record::id(id) = 'tia';

-- rejects: delete_medication_in_a_visit
-- error: is referenced by visit.items[*].medication
DELETE medication WHERE record::id(id) = 'amoxicillin';

-- write: admit_patient
-- ordered
-- roc: [{ id: 'bo', kind: 'dog', owner: 'Jon Berg' }, { id: 'kiwi', kind: 'bird', owner: 'Lena Roux' }, { id: 'luna', kind: 'cat', owner: 'Mara Ito' }, { id: 'mimi', kind: 'cat', owner: 'Noor Haddad' }, { id: 'pip', kind: 'dog', owner: 'Jon Berg' }, { id: 'rex', kind: 'dog', owner: 'Mara Ito' }, { id: 'zed', kind: 'gecko', owner: 'Noor Haddad' }]
CREATE patient:⟨pip⟩ CONTENT { age: 1, allergies: [], name: 'Pip', owner: owner:⟨jon⟩, species: 'Dog', vaccines: [], weight_kg: 6.5dec };
SELECT record::id(id) AS id, (IF species.kind = 'Bird' THEN 'bird' ELSE IF species = 'Cat' THEN 'cat' ELSE IF species = 'Dog' THEN 'dog' ELSE species.latin END) AS kind, owner.name AS owner FROM patient ORDER BY id;

-- write: add_medication
-- ordered
-- roc: [{ id: 'amoxicillin', label: 'Amoxicillin (tablet)', stock: 200 }, { id: 'aspirin', label: 'Aspirin (tablet)', stock: 500 }, { id: 'gabapentin', label: 'Gabapentin (capsule)', stock: 40 }, { id: 'ivermectin', label: 'Ivermectin (injection)', stock: 15 }, { id: 'meloxicam', label: 'Meloxicam (liquid)', stock: 0 }]
CREATE medication:⟨meloxicam⟩ CONTENT { form: 'liquid', name: 'Meloxicam', unit_price: 2.5dec };
SELECT record::id(id) AS id, label AS label, stock AS stock FROM medication ORDER BY id;

-- write: restock
-- ordered
-- roc: [{ id: 'amoxicillin', label: 'Amoxicillin (tablet)', stock: 200 }, { id: 'aspirin', label: 'Aspirin (tablet)', stock: 500 }, { id: 'gabapentin', label: 'Gabapentin (capsule)', stock: 140 }, { id: 'ivermectin', label: 'Ivermectin (injection)', stock: 115 }, { id: 'meloxicam', label: 'Meloxicam (liquid)', stock: 100 }]
LET $add = 100;
LET $floor = 60;
UPDATE medication SET stock = stock + $add WHERE stock < $floor;
SELECT record::id(id) AS id, label AS label, stock AS stock FROM medication ORDER BY id;

-- write: certify_vet
-- ordered
-- roc: [{ id: 'ruth', specialty: 'General', years: 12 }, { id: 'sam', specialty: { kind: 'Surgery', board: 'ACVS' }, years: 8 }, { id: 'tia', specialty: { kind: 'Surgery', board: 'ECVS' }, years: 4 }]
UPDATE vet SET specialty = { kind: 'Surgery', board: 'ECVS' }, years = years + 1 WHERE record::id(id) = 'tia';
SELECT record::id(id) AS id, specialty AS specialty, years AS years FROM vet ORDER BY id;

-- write: delete_medication_unsets_allergies
-- ordered
-- roc: [{ allergies: [], id: 'bo' }, { allergies: [], id: 'kiwi' }, { allergies: [], id: 'luna' }, { allergies: [], id: 'mimi' }, { allergies: [], id: 'pip' }, { allergies: ['Amoxicillin'], id: 'rex' }, { allergies: [], id: 'zed' }]
DELETE medication WHERE record::id(id) = 'aspirin';
SELECT allergies.map(|$v1| $v1.name) AS allergies, record::id(id) AS id FROM patient ORDER BY id;

-- write: relate_vet
-- ordered
-- roc: [{ id: 'e1', patient: 'Rex', vet: 'Ruth Okafor' }, { id: 'e2', patient: 'Rex', vet: 'Sam Petrov' }, { id: 'e3', patient: 'Bo', vet: 'Ruth Okafor' }, { id: 'e4', patient: 'Luna', vet: 'Sam Petrov' }, { id: 'e5', patient: 'Luna', vet: 'Tia Brandt' }, { id: 'e6', patient: 'Kiwi', vet: 'Ruth Okafor' }, { id: 'e7', patient: 'Mimi', vet: 'Sam Petrov' }, { id: 'e8', patient: 'Zed', vet: 'Ruth Okafor' }, { id: 'e9', patient: 'Rex', vet: 'Tia Brandt' }]
RELATE vet:⟨tia⟩->treats:⟨e9⟩->patient:⟨rex⟩ CONTENT { primary: false, since_year: 2026 };
SELECT record::id(id) AS id, out.name AS patient, in.name AS vet FROM treats ORDER BY id;

-- write: delete_owner_cascades_to_patients
-- ordered
-- roc: [{ id: 'bo' }, { id: 'kiwi' }, { id: 'luna' }, { id: 'pip' }, { id: 'rex' }]
DELETE owner WHERE record::id(id) = 'noor';
SELECT record::id(id) AS id FROM patient ORDER BY id;

-- query: visits_left_by_the_cascade
-- ordered
-- roc: [{ id: 'v1' }, { id: 'v2' }, { id: 'v3' }, { id: 'v4' }, { id: 'v6' }]
SELECT record::id(id) AS id FROM visit ORDER BY id;

-- query: edges_left_by_the_cascade
-- ordered
-- roc: [{ id: 'e1', patient: 'Rex', vet: 'Ruth Okafor' }, { id: 'e2', patient: 'Rex', vet: 'Sam Petrov' }, { id: 'e3', patient: 'Bo', vet: 'Ruth Okafor' }, { id: 'e4', patient: 'Luna', vet: 'Sam Petrov' }, { id: 'e5', patient: 'Luna', vet: 'Tia Brandt' }, { id: 'e6', patient: 'Kiwi', vet: 'Ruth Okafor' }, { id: 'e9', patient: 'Rex', vet: 'Tia Brandt' }]
SELECT record::id(id) AS id, out.name AS patient, in.name AS vet FROM treats ORDER BY id;

-- write: retention
-- ordered
-- roc: [{ id: 'v3' }, { id: 'v4' }, { id: 'v6' }]
LET $before = d'2026-02-15T00:00:00Z';
DELETE visit WHERE seen < $before;
SELECT record::id(id) AS id FROM visit ORDER BY id;
