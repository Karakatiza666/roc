# Whether code that runs at run time uses a generic definition's `where`
# requirement (the `runs` bit). `roc check` with ROC_REIFY_ONLY set prints the
# bit of each top-level definition's requirements.
Db := {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, _code| q
	}
}

Clock := { n : U64 }.{
	now : Clock -> Bool
	now = |c| c.n > 0
}

# Used at run time.
inner = |x| x.now()

# Used only inside a lambda written at a `Code` place.
frag = |q| Db.Q.filter(q, |x| x.t.now())

# The same, through an annotation's `where` clause.
frag_where : Db.Q({ t : a }) -> Db.Q({ t : a }) where [a.now : a -> Bool]
frag_where = |q| q.filter(|x| x.t.now())

# Used inside the lambda and also at run time.
both : Db.Q({ t : a }), a -> Db.Q({ t : a }) where [a.now : a -> Bool]
both = |q, y| if y.now() q.filter(|x| x.t.now()) else q

# The same without an annotation: the list makes `y` and `x.t` one type, so
# both uses are one requirement.
both_open = |q, y| if y.now() Db.Q.filter(q, |x| [x.t, y].len() > 0 and x.t.now()) else q

# A name written as the `Code` argument is described, not run, so the
# requirement its use copies does not run. Its own body does run.
row_now = |x| x.t.now()
named = |q| Db.Q.filter(q, row_now)

# A template's body is described at each call and never runs.
tmpl : a -> Code(a -> Bool) where [a.now : a -> Bool]
tmpl = |_k| |x| x.now()

# The fragments are not used: a use that fixes their types would describe
# them, and the bits are the definitions' own.
main! = |_args| {
	echo!("${Str.inspect(inner(Clock.({ n: 1 })))}\n")
	Ok({})
}
