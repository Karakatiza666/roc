import Ql
import Types
import Translate

# The schema: `DEFINE` statements from the row types and from the builder's
# clauses. A clause is translated when it is given, so a `Defined` holds only
# text and names. `script` puts the statements of every table in order and
# adds what each link needs: an existence check, and a delete policy at any
# depth (native `REFERENCE` at the root, generated events elsewhere).
Schema :: {}.{

	## What a delete does to the rows that link to the deleted row.
	Policy : [Reject, Unset, Cascade, Ignore]

	## One clause of the builder, translated. Paths are spelled as a field
	## definition names them (`items[*].qty`). Conditions are over `$value`,
	## a row check is over `$after`, a computed value is over `$this`.
	Rule := [
		Assert({ path : Str, cond : Str }),
		Check({ name : Str, cond : Str }),
		Index({ paths : List(Str), unique : Bool }),
		Default({ path : Str, value : Str }),
		Computed({ path : Str, expr : Str }),
		Readonly(Str),
		Comment({ path : Str, text : Str }),
		OnDelete({ table : Str, policy : Schema.Policy }),
		OnDeleteAt({ path : Str, policy : Schema.Policy }),
	].{
		is_eq : _
	}

	## A finished table definition: what `Surreal.schema` takes.
	Defined :: { source : Types.Source, rules : List(Schema.Rule), problems : List(Ql.Error) }

	defined : Types.Source, List(Schema.Rule), List(Ql.Error) -> Schema.Defined
	defined = |source, rules, problems| Defined.({ source, rules, problems })

	## One step to a link: a field, each element of a list, or the arm of a
	## union (the value there is that arm).
	Hop : [Field(Str), Each, Arm(Str)]

	## A `Link` or `Id` in a row. A list of links ends in `Each`. `optional`
	## is True when the link's own field is `?:`.
	Site : { hops : List(Schema.Hop), target : Code.Ty, optional : Bool }

	# ------------------------------------------------------------ clauses

	## A row check, placed by one rule: when it reads only one top-level
	## field, it is that field's `ASSERT`; when it reads more, it is an event
	## over `$after`; when it reads none, it is an error.
	check : Types.Source, Str, Code.Graph -> Try(List(Schema.Rule), Ql.Error)
	check = |source, name, graph| {
		whole = Translate.render(graph, [Translate.document("$after", Schema.is_edge(source))], Translate.variable)?
		fields = Types.record_fields(source.row_ty)?.keep_if(|f| !Schema.skipped(source).contains(f.name))
		match Schema.placed(graph, fields) {
			NoField => Err(BadSchema("the check `${name}` reads no field, so it is always or never true"))
			OnField(f) => Ok([Assert({ path: Ql.ident(f.name), cond: f.cond })])
			Several => Ok([Check({ name, cond: whole })])
		}
	}

	## Where a predicate over a record goes. It is evaluated with the record
	## holding one field at a time, bound to `$value`: it evaluates exactly
	## when it reads nothing outside that field.
	placed : Code.Graph, List({ name : Str, ty : Code.Ty, presence : [Required, Optional] }) -> [NoField, OnField({ name : Str, cond : Str }), Several]
	placed = |graph, fields| {
		evaluated = |only| Translate.render(graph, [Translate.Binding.Fields(only)], Translate.variable)
		if evaluated([]).is_ok() {
			NoField
		} else {
			found = fields.keep_oks(
				|f| {
					value = if (f.presence == Optional) Translate.Binding.Maybe("$value") else Translate.at("$value", f.ty)
					evaluated([{ name: f.name, binding: value }]).map_ok(|cond| { name: f.name, cond })
				},
			)
			match found {
				[one] => OnField(one)
				_ => Several
			}
		}
	}

	## A predicate on one field: its `ASSERT`.
	assert : Code.Graph, Code.Graph -> Try(List(Schema.Rule), Ql.Error)
	assert = |path_graph, predicate| {
		path = Schema.one_field(path_graph, "assert")?
		cond = Translate.render(predicate, [Translate.at("$value", Schema.param_ty(predicate))], Translate.variable)?
		Ok([Assert({ path, cond })])
	}

	## A predicate on each element of a list field. On a list of records it
	## goes on the one element field it reads, as `check` does on a row;
	## otherwise it is `$value.all(..)` on the list.
	assert_each : Code.Graph, Code.Graph -> Try(List(Schema.Rule), Ql.Error)
	assert_each = |path_graph, predicate| {
		path = Schema.one_field(path_graph, "assert_each")?
		item = Schema.param_ty(predicate)
		every = |{}| {
			cond = Translate.render(predicate, [Translate.at("$item", item)], Translate.variable)?
			Ok([Assert({ path, cond: "$value.all(|$item| ${cond})" })])
		}
		match Types.unwrap(item) {
			Record(fields) => match Schema.placed(predicate, fields) {
				NoField => Err(BadSchema("the check on each element of `${path}` reads no field, so it is always or never true"))
				OnField(f) => Ok([Assert({ path: Types.dot("${path}[*]", f.name), cond: f.cond })])
				Several => every({})
			}
			_ => every({})
		}
	}

	## An index on one path or on a record of paths.
	index : Types.Source, Code.Graph, Bool -> Try(List(Schema.Rule), Ql.Error)
	index = |source, graph, unique| {
		paths = Translate.paths_of(graph)?
		Ok([Index({ paths: paths.map(|p| Schema.index_path(p, Schema.is_edge(source))), unique })])
	}

	## An index path. An edge's `from` and `to` are SurrealDB's `in` and `out`.
	index_path : List(Translate.Step), Bool -> Str
	index_path = |steps, edge| match steps {
		[Field(name)] if edge and (name == "from" or name == "to") => Translate.spell_name(name, edge)
		_ => Translate.spell(steps)
	}

	default : Code.Graph, Ql.Value -> Try(List(Schema.Rule), Ql.Error)
	default = |graph, value| Ok([Default({ path: Translate.spell(Translate.path_of(graph)?), value: Ql.literal(value) })])

	## A default that is an expression over `$this`, which may call `Rand`.
	default_by : Types.Source, Code.Graph, Code.Graph -> Try(List(Schema.Rule), Ql.Error)
	default_by = |source, path_graph, value| {
		path = Translate.spell(Translate.path_of(path_graph)?)
		expr = Translate.row_value(value, [Translate.document("$this", Schema.is_edge(source))], Translate.variable)?
		Ok([Default({ path, value: expr })])
	}

	## A value SurrealDB computes on every write, over `$this`. It may call `Rand`.
	computed : Types.Source, Code.Graph, Code.Graph -> Try(List(Schema.Rule), Ql.Error)
	computed = |source, path_graph, value| {
		path = Translate.spell(Translate.path_of(path_graph)?)
		expr = Translate.row_value(value, [Translate.document("$this", Schema.is_edge(source))], Translate.variable)?
		Ok([Computed({ path, expr })])
	}

	readonly : Code.Graph -> Try(List(Schema.Rule), Ql.Error)
	readonly = |graph| Ok([Readonly(Translate.spell(Translate.path_of(graph)?))])

	## The time of the first write, kept: `VALUE time::now() READONLY`
	## (verified: an update keeps it, a create cannot set it).
	created_now : Code.Graph -> Try(List(Schema.Rule), Ql.Error)
	created_now = |graph| {
		path = Translate.spell(Translate.path_of(graph)?)
		Ok([Computed({ path, expr: "time::now()" }), Readonly(path)])
	}

	comment : Code.Graph, Str -> Try(List(Schema.Rule), Ql.Error)
	comment = |graph, text| Ok([Comment({ path: Translate.spell(Translate.path_of(graph)?), text })])

	on_delete : Str, Schema.Policy -> Try(List(Schema.Rule), Ql.Error)
	on_delete = |table, policy| Ok([OnDelete({ table, policy })])

	on_delete_at : Code.Graph, Schema.Policy -> Try(List(Schema.Rule), Ql.Error)
	on_delete_at = |graph, policy| Ok([OnDeleteAt({ path: Translate.spell(Translate.path_of(graph)?), policy })])

	one_field : Code.Graph, Str -> Try(Str, Ql.Error)
	one_field = |graph, clause| {
		steps = Translate.path_of(graph)?
		if steps.contains(Each) {
			Err(Unsupported("`${clause}` reads one field; for each element of a list use `assert_each`"))
		} else {
			Ok(Translate.spell(steps))
		}
	}

	param_ty : Code.Graph -> Code.Ty
	param_ty = |graph| match graph.root_row().params {
		[ty] => ty
		_ => crash "a `Code(v -> Bool)` has one parameter"
	}

	is_edge : Types.Source -> Bool
	is_edge = |source| source.kind != Normal

	## Fields with no definition: the record key, and an edge's two ends.
	skipped : Types.Source -> List(Str)
	skipped = |source| match source.kind {
		Normal => ["id"]
		Relation(_) => ["id", "from", "to"]
	}

	# ------------------------------------------------------------ link sites

	## Every `Link` and `Id` in a row, as `Types.link_sites` lists them, with
	## the steps that reach each one. The ends of an edge are not listed:
	## SurrealDB's `ENFORCED` relation checks them and deletes the edge with
	## either end.
	sites : Types.Source -> Try(List(Schema.Site), Ql.Error)
	sites = |source| {
		fields = Types.record_fields(source.row_ty)?
		Ok(
			fields
				.keep_if(|f| !Schema.skipped(source).contains(f.name))
				.join_map(|f| Schema.walk(f.ty, [Field(f.name)], f.presence == Optional)),
		)
	}

	walk : Code.Ty, List(Schema.Hop), Bool -> List(Schema.Site)
	walk = |ty, hops, optional| match Types.site_of(ty) {
		Ok({ target, .. }) => [{ hops, target, optional }]
		Err(NotASite) => match Types.unwrap(ty) {
			Record(fields) => fields.join_map(|f| Schema.walk(f.ty, hops.append(Field(f.name)), f.presence == Optional))
			ListOf(item) => Schema.walk(item, hops.append(Each), Bool.False)
			TagUnion(variants) => variants.join_map(
				|v| {
					arm = hops.append(Arm(v.name))
					match v.payloads {
						[] => []
						[one] => match Types.unwrap(one) {
							Record(_) => Schema.walk(one, arm, Bool.False)
							_ => Schema.walk(one, arm.append(Field("value")), Bool.False)
						}
						many => many.map_with_index(|p, i| Schema.walk(p, arm.append(Field("_${i.to_str()}")), Bool.False)).join()
					}
				},
			)
			_ => []
		}
	}

	## The field a site is in: a list of links is the list.
	site_path : List(Schema.Hop) -> Str
	site_path = |hops| match hops.last() {
		Ok(Each) => Schema.spell(hops.drop_last(1))
		_ => Schema.spell(hops)
	}

	spell : List(Schema.Hop) -> Str
	spell = |hops| hops.fold(
		"",
		|text, hop| match hop {
			Field(name) => if (text.is_empty()) Ql.ident(name) else Types.dot(text, name)
			Each => "${text}[*]"
			Arm(_) => text
		},
	)

	## The shape `Types.link_sites` gives the same site.
	shape : Schema.Site -> Types.Shape
	shape = |site| {
		tags = site.hops.keep_oks(
			|h| match h {
				Arm(tag) => Ok(tag)
				_ => Err(NotArm)
			},
		)
		inner = site.hops.drop_last(1)
		match tags.last() {
			Ok(tag) => InUnionArm({ tag: tag })
			Err(_) =>
				if inner.contains(Each) {
					InList
				} else if site.hops.len() > 2 or (site.hops.len() == 2 and site.hops.last() != Ok(Each)) {
					InObject
				} else if site.hops.len() == 2 {
					RootList
				} else if site.optional {
					RootOptional
				} else {
					Root
				}
		}
	}

	## A site SurrealDB's own `REFERENCE` covers: a root field, or a root
	## list of links. `REFERENCE` is refused on a nested field (SF).
	is_native : List(Schema.Hop) -> Bool
	is_native = |hops| match hops {
		[Field(_)] | [Field(_), Each] => Bool.True
		_ => Bool.False
	}

	## A condition over a row of the linking table: the link at `hops` is the
	## deleted row, `$before.id`.
	mentions : Str, List(Schema.Hop), U64 -> Str
	mentions = |at, hops, depth| match hops {
		[] => "${at} = $before.id"
		[Each] => "$before.id IN ${at}"
		[Field(name), .. as rest] => Schema.mentions(Schema.member(at, name), rest, depth)
		[Arm(tag), .. as rest] => "(${at}.kind = ${Ql.quote(tag)} AND ${Schema.mentions(at, rest, depth)})"
		[Each, .. as rest] => {
			item = "$e${(depth + 1).to_str()}"
			"${at}.any(|${item}| ${Schema.mentions(item, rest, depth + 1)})"
		}
	}

	is_arm : Schema.Hop -> Bool
	is_arm = |hop| match hop {
		Arm(_) => Bool.True
		_ => Bool.False
	}

	member : Str, Str -> Str
	member = |at, name| if (at.is_empty()) Ql.ident(name) else "${at}.${Ql.member(name)}"

	## The `SET` that unsets a nested link: an optional field becomes `NONE`,
	## a link leaves its list, and an element of a list of objects that holds
	## the link leaves the list, as native `UNSET` does to a list of links.
	unset : Schema.Site -> Try(Str, Str)
	unset = |site| {
		fields = |hops| hops.all(
			|h| match h {
				Field(_) => Bool.True
				_ => Bool.False
			},
		)
		hops = site.hops
		if hops.any(Schema.is_arm) {
			return Err("an arm of a union cannot be unset; use Reject, Cascade or Ignore")
		}
		match hops.find_first_index(|h| h == Each) {
			Err(_) =>
				if site.optional {
					Ok("${Schema.spell(hops)} = NONE")
				} else {
					Err("the link is a required field, so it cannot be unset; make it optional (`?:`) or use Reject, Cascade or Ignore")
				}
			Ok(i) => {
				list = Schema.spell(hops.take_first(i))
				rest = hops.drop_first(i + 1)
				if rest.is_empty() {
					Ok("${list} = ${list}.filter(|$l| $l != $before.id)")
				} else if fields(rest) {
					Ok("${list} = ${list}.filter(|$e1| !(${Schema.mentions("$e1", rest, 1)}))")
				} else {
					Err("a link in a list inside a list cannot be unset; use Reject, Cascade or Ignore")
				}
			}
		}
	}

	# ------------------------------------------------------------ the script

	## The schema script: every `DEFINE TABLE`, then every field, then the
	## indexes, the row-check events and the delete events, so that no
	## statement names a table defined later.
	script : List(Schema.Defined) -> Try(Str, Ql.Error)
	script = |all| {
		defs = all.map(|Defined.(d)| d)
		registry = defs.map(|d| d.source)
		Types.check_registry(registry)?
		match defs.join_map(|d| d.problems) {
			[first, ..] => return Err(first)
			[] => {}
		}
		parts = defs.map_try(|d| Schema.statements(d, registry))?
		Schema.no_cycle(defs, registry)?
		names = parts.join_map(|p| p.names)
		match names.find_first(|n| names.keep_if(|m| m == n).len() > 1) {
			Ok(n) => return Err(BadSchema("two generated statements are named `${n}`; rename a field or a check"))
			Err(_) => {}
		}
		lines = [parts.map(|p| p.table), parts.join_map(|p| p.fields), parts.join_map(|p| p.indexes), parts.join_map(|p| p.checks), parts.join_map(|p| p.deletes)]
		Ok(Str.join_with(lines.join(), "\n"))
	}

	Parts : { table : Str, fields : List(Str), indexes : List(Str), checks : List(Str), deletes : List(Str), names : List(Str) }

	statements : { source : Types.Source, rules : List(Schema.Rule), problems : List(Ql.Error) }, Types.Registry -> Try(Schema.Parts, Ql.Error)
	statements = |d, registry| {
		src = d.source.name
		on = "ON ${Ql.ident(src)}"
		defs = Types.field_defs(src, d.source.row_ty, registry)?
		paths = defs.map(|f| f.path)
		ends = if (Schema.is_edge(d.source)) ["in", "out"] else []
		_ = d.rules.map_try(|r| Schema.known(src, paths, ends, r))?
		links = Schema.sites(d.source)?.map_try(|s| Schema.policy_of(src, s, d.rules, registry))?
		_ = d.rules.map_try(|r| Schema.used(src, links, r))?
		fields = defs.map_try(|f| Schema.field(on, f, d.rules, links))?
		indexes = d.rules.keep_oks(
			|r| match r {
				Index({ paths: on_paths, unique }) => {
					name = "${src}_${Str.join_with(on_paths.map(Schema.slug), "_")}${if (unique) "_unique" else "_index"}"
					Ok({ name, line: "DEFINE INDEX OVERWRITE ${Ql.ident(name)} ${on} FIELDS ${Str.join_with(on_paths, ", ")}${if (unique) " UNIQUE" else ""};" })
				}
				_ => Err(NotIndex)
			},
		)
		nested = links.keep_if(|l| !Schema.is_native(l.site.hops) and l.policy != Ignore)
		link_indexes = nested.keep_oks(
			|l|
				if l.site.hops.any(Schema.is_arm) {
					# An arm of a union has no field definition to index (verified).
					Err(InArm)
				} else {
					name = "${src}_${Schema.slug(Schema.site_path(l.site.hops))}_link"
					Ok({ name, line: "DEFINE INDEX OVERWRITE ${Ql.ident(name)} ${on} FIELDS ${Schema.site_path(l.site.hops)};" })
				},
		)
		checks = d.rules.keep_oks(
			|r| match r {
				Check({ name: check_name, cond }) => {
					name = "${src}_check_${Schema.slug(check_name)}"
					Ok({ name, line: "DEFINE EVENT OVERWRITE ${Ql.ident(name)} ${on} WHEN $event IN ['CREATE', 'UPDATE'] THEN { IF !(${cond}) { THROW ${Ql.quote("${src}: ${check_name}")} } };" })
				}
				_ => Err(NotCheck)
			},
		)
		deletes = nested.map_try(|l| Schema.delete_event(src, l))?
		named = indexes.concat(link_indexes).concat(checks).concat(deletes)
		table = match d.source.kind {
			Normal => "DEFINE TABLE OVERWRITE ${Ql.ident(src)} SCHEMAFULL;"
			Relation({ from, to }) => "DEFINE TABLE OVERWRITE ${Ql.ident(src)} TYPE RELATION IN ${Ql.ident(from.name)} OUT ${Ql.ident(to.name)} ENFORCED SCHEMAFULL;"
		}
		Ok({
			table,
			fields,
			indexes: indexes.concat(link_indexes).map(|n| n.line),
			checks: checks.map(|n| n.line),
			deletes: deletes.map(|n| n.line),
			names: named.map(|n| n.name),
		})
	}

	Link : { site : Schema.Site, table : Str, policy : Schema.Policy }

	## The policy of one site: `on_delete_at` for its path, else `on_delete`
	## for its target table, else `Reject`.
	policy_of : Str, Schema.Site, List(Schema.Rule), Types.Registry -> Try(Schema.Link, Ql.Error)
	policy_of = |src, site, rules, registry| {
		table = Types.table_for(registry, site.target)?
		path = Schema.site_path(site.hops)
		at_path = rules.keep_oks(
			|r| match r {
				OnDeleteAt(p) if p.path == path => Ok(p.policy)
				_ => Err(Other)
			},
		)
		for_table = rules.keep_oks(
			|r| match r {
				OnDelete(p) if p.table == table => Ok(p.policy)
				_ => Err(Other)
			},
		)
		policy = match (at_path.last(), for_table.last()) {
			(Ok(p), _) => p
			(_, Ok(p)) => p
			_ => Reject
		}
		site_name = "`${src}.${Schema.spell(site.hops)}`"
		if policy == Unset {
			if Schema.is_native(site.hops) {
				if site.hops.len() == 1 and !site.optional {
					return Err(BadSchema("${site_name} is required, so a delete cannot unset it; make it optional (`?:`) or use Reject, Cascade or Ignore"))
				}
			} else {
				match Schema.unset(site) {
					Ok(_) => {}
					Err(why) => return Err(BadSchema("${site_name}: ${why}"))
				}
			}
		}
		Ok({ site, table, policy })
	}

	## A clause's path must be a field the table defines.
	known : Str, List(Str), List(Str), Schema.Rule -> Try({}, Ql.Error)
	known = |src, paths, ends, rule| {
		path = match rule {
			Assert(a) => a.path
			Default(a) => a.path
			Computed(a) => a.path
			Readonly(p) => p
			Comment(a) => a.path
			Index(i) => return i.paths.map_try(|p| Schema.known_index(src, paths.concat(ends), p)).map_ok(|_| {})
			Check(_) | OnDelete(_) | OnDeleteAt(_) => return Ok({})
		}
		if paths.contains(path) {
			Ok({})
		} else {
			Err(BadSchema("`${src}.${path}` has no field definition to put this on; the record key and an edge's ends are SurrealDB's own"))
		}
	}

	known_index : Str, List(Str), Str -> Try({}, Ql.Error)
	known_index = |src, paths, path|
		if paths.contains(path) or paths.contains("${path}[*]") or paths.any(|p| p.starts_with("${path}[*].")) {
			Ok({})
		} else {
			Err(BadSchema("`${src}.${path}` has no field definition to index"))
		}

	## A delete clause must name a link of the table.
	used : Str, List(Schema.Link), Schema.Rule -> Try({}, Ql.Error)
	used = |src, links, rule| match rule {
		OnDelete({ table, .. }) =>
			if (links.any(|l| l.table == table)) Ok({}) else Err(BadSchema("no link in `${src}` points at table `${table}`"))
		OnDeleteAt({ path, .. }) =>
			if (links.any(|l| Schema.site_path(l.site.hops) == path)) Ok({}) else Err(BadSchema("`${src}.${path}` is not a link"))
		_ => Ok({})
	}

	## One `DEFINE FIELD`, with what the clauses add to it.
	field : Str, Types.FieldDef, List(Schema.Rule), List(Schema.Link) -> Try(Str, Ql.Error)
	field = |on, def, rules, links| {
		mine = |pick| rules.keep_oks(pick)
		asserts = def.asserts.concat(
			mine(
				|r| match r {
					Assert(a) if a.path == def.path => Ok(a.cond)
					_ => Err(Other)
				},
			),
		)
		at_most_one = |values, what| match values {
			[] => Ok("")
			[one] => Ok(one)
			_ => Err(BadSchema("`${def.path}` has two ${what}"))
		}
		default_part = at_most_one(
			mine(
				|r| match r {
					Default(a) if a.path == def.path => Ok(" DEFAULT ${a.value}")
					_ => Err(Other)
				},
			),
			"defaults",
		)?
		value_part = at_most_one(
			mine(
				|r| match r {
					Computed(a) if a.path == def.path => Ok(" VALUE ${a.expr}")
					_ => Err(Other)
				},
			),
			"computed values",
		)?
		readonly_part = if (rules.any(|r| r == Readonly(def.path))) " READONLY" else ""
		reference_part = at_most_one(
			links.keep_oks(|l| if (Schema.is_native(l.site.hops) and Schema.site_path(l.site.hops) == def.path) Ok(" REFERENCE ON DELETE ${Schema.keyword(l.policy)}") else Err(Other)),
			"links",
		)?
		assert_part = match asserts {
			[] => ""
			[one] => " ASSERT ${one}"
			many => " ASSERT ${Str.join_with(many.map(|a| "(${a})"), " AND ")}"
		}
		comment_part = at_most_one(
			mine(
				|r| match r {
					Comment(a) if a.path == def.path => Ok(" COMMENT ${Ql.quote(a.text)}")
					_ => Err(Other)
				},
			),
			"comments",
		)?
		Ok("DEFINE FIELD OVERWRITE ${def.path} ${on} TYPE ${def.ty}${default_part}${value_part}${readonly_part}${reference_part}${assert_part}${comment_part};")
	}

	keyword : Schema.Policy -> Str
	keyword = |policy| match policy {
		Reject => "REJECT"
		Unset => "UNSET"
		Cascade => "CASCADE"
		Ignore => "IGNORE"
	}

	## The event on the target table that does a nested link's policy.
	delete_event : Str, Schema.Link -> Try({ name : Str, line : Str }, Ql.Error)
	delete_event = |src, link| {
		hops = link.site.hops
		name = "${src}_${Str.join_with(hops.keep_oks(Schema.hop_slug), "_")}_on_delete"
		cond = Schema.mentions("", hops, 0)
		body = match link.policy {
			Reject => Ok("IF (SELECT VALUE id FROM ${Ql.ident(src)} WHERE ${cond} LIMIT 1) != [] { THROW <string>$before.id + ${Ql.quote(" is referenced by ${src}.${Schema.spell(hops)}")} }")
			Cascade => Ok("DELETE ${Ql.ident(src)} WHERE ${cond}")
			Unset => match Schema.unset(link.site) {
				Ok(set) => Ok("UPDATE ${Ql.ident(src)} SET ${set} WHERE ${cond}")
				Err(why) => Err(BadSchema(why))
			}
			Ignore => Err(BadSchema("an ignored link has no event"))
		}?
		Ok({ name, line: "DEFINE EVENT OVERWRITE ${Ql.ident(name)} ON ${Ql.ident(link.table)} WHEN $event = 'DELETE' THEN { ${body} };" })
	}

	hop_slug : Schema.Hop -> Try(Str, [Skip])
	hop_slug = |hop| match hop {
		Field(name) => Ok(Schema.slug(name))
		Arm(tag) => Ok(Schema.slug(tag))
		Each => Err(Skip)
	}

	## A name part made of letters, digits and `_`: `items[*].qty` is `items_qty`.
	slug : Str -> Str
	slug = |text| {
		bytes = text.to_utf8().fold(
			[],
			|out, b|
				if (b >= 97 and b <= 122) or (b >= 65 and b <= 90) or (b >= 48 and b <= 57) {
					out.append(b)
				} else if out.last() == Ok(95) or out.is_empty() {
					out
				} else {
					out.append(95)
				},
		)
		trimmed = if (bytes.last() == Ok(95)) bytes.drop_last(1) else bytes
		match Str.from_utf8(trimmed) {
			Ok(s) => s
			Err(_) => crash "ASCII letters, digits and `_` are valid UTF-8"
		}
	}

	# ------------------------------------------------------------ cycles

	## Rows are written one at a time and each link must exist, so a cycle of
	## required root links can never be filled.
	no_cycle : List({ source : Types.Source, rules : List(Schema.Rule), problems : List(Ql.Error) }), Types.Registry -> Try({}, Ql.Error)
	no_cycle = |defs, registry| {
		edges = defs.map_try(
			|d| {
				required = Schema.sites(d.source)?.keep_if(|s| s.hops.len() == 1 and !s.optional)
				required.map_try(|s| Ok({ from: d.source.name, field: Schema.spell(s.hops), to: Types.table_for(registry, s.target)? }))
			},
		)?.join()
		_ = edges.map_try(|e| Schema.follow(edges, [], e.from))?
		Ok({})
	}

	Edge : { from : Str, field : Str, to : Str }

	follow : List(Schema.Edge), List(Schema.Edge), Str -> Try({}, Ql.Error)
	follow = |edges, trail, table| match trail.find_first_index(|e| e.from == table) {
		Ok(start) => {
			loop = trail.drop_first(start)
			steps = Str.join_with(loop.map(|e| "${e.from}.${e.field}"), " -> ")
			Err(BadSchema("required links form a cycle (${steps} -> ${table}), so no row of it can be written first; make one of them optional (`?:`)"))
		}
		Err(_) => {
			_ = edges.keep_if(|e| e.from == table).map_try(|e| Schema.follow(edges, trail.append(e), e.to))?
			Ok({})
		}
	}
}

# Tests that need no table. The rest are in `SchemaTest.roc`.

expect Schema.slug("items[*].qty") == "items_qty"
expect Schema.slug("⟨x y⟩") == "x_y"
expect Schema.slug("total matches items") == "total_matches_items"
expect Schema.mentions("", [Field("customer")], 0) == "customer = $before.id"
expect Schema.mentions("", [Field("wishlist"), Each], 0) == "$before.id IN wishlist"
expect Schema.mentions("", [Field("gift"), Field("to")], 0) == "gift.to = $before.id"
expect Schema.mentions("", [Field("items"), Each, Field("product")], 0) == "items.any(|$e1| $e1.product = $before.id)"
expect Schema.mentions("", [Field("payment"), Arm("Invoice"), Field("contact")], 0) == "(payment.kind = 'Invoice' AND payment.contact = $before.id)"
expect Schema.mentions("", [Field("xs"), Each, Each], 0) == "xs.any(|$e1| $before.id IN $e1)"
expect Schema.unset({ hops: [Field("gift"), Field("to")], target: Str, optional: Bool.True }) == Ok("gift.to = NONE")
expect Schema.unset({ hops: [Field("gift"), Field("to")], target: Str, optional: Bool.False }).is_err()
expect Schema.unset({ hops: [Field("gift"), Field("tags"), Each], target: Str, optional: Bool.False }) == Ok("gift.tags = gift.tags.filter(|$l| $l != $before.id)")
expect Schema.unset({ hops: [Field("items"), Each, Field("product")], target: Str, optional: Bool.False }) == Ok("items = items.filter(|$e1| !($e1.product = $before.id))")
expect Schema.unset({ hops: [Field("payment"), Arm("Invoice"), Field("contact")], target: Str, optional: Bool.False }).is_err()
expect Schema.unset({ hops: [Field("xs"), Each, Each], target: Str, optional: Bool.False }).is_err()
