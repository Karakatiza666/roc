# Which top-level definitions are reify-only: their run-time code reaches an
# intrinsic. `roc check` with ROC_REIFY_ONLY set prints each one with its
# witness. A reference that runs in a root and reaches an intrinsic is
# reported as code that exists only in reified code.
app [main!] { pf: platform "../fx/platform/main.roc" }

Db := {}.{
	Q(row) := { log : Str }.{
		filter : Q(row), Code(row -> Bool) -> Q(row)
		filter = |q, _code| q
	}
}

# An intrinsic: an annotation with no body.
hot : Str -> Bool

# Calls the intrinsic at run time.
runs_hot = |s| hot(s)

# Uses the intrinsic as a value at run time.
maps_hot = |xs| xs.map(hot)

# Uses the intrinsic only inside a lambda written at a `Code` place.
described_hot = |q| Db.Q.filter(q, |x| hot(x.name))

# A chain of two definitions.
chain_one = |s| runs_hot(s)
chain_two = |s| chain_one(s)

# A mutually recursive pair that reaches the intrinsic.
ping = |n, s| if n == 0 hot(s) else pong(n - 1, s)
pong = |n, s| if n == 0 False else ping(n - 1, s)

# A mutually recursive pair that does not.
even = |n| if n == 0 True else odd(n - 1)
odd = |n| if n == 0 False else even(n - 1)

Clock := { n : U64 }.{
	# An intrinsic method.
	now : Clock -> Bool
}

Meter := { n : U64 }.{
	now : Meter -> Bool
	now = |m| m.n > 0
}

# Generic: the dispatch is resolved where a use fixes the type.
inner = |x| x.now()

# The use fixes the type to Clock, whose `now` is an intrinsic.
outer : Clock -> Bool
outer = |t| inner(t)

# A dispatch on a Clock, written in the definition itself.
direct : Clock -> Bool
direct = |c| c.now()

# The use fixes the type to Meter, whose `now` has a body.
outer_meter : Meter -> Bool
outer_meter = |m| inner(m)

# A dispatch on a Clock inside a lambda written at a `Code` place.
described_now : Db.Q({ c : Clock }) -> Db.Q({ c : Clock })
described_now = |q| q.filter(|x| x.c.now())

# A reify-only definition used only inside a lambda written at a `Code` place.
described_outer : Db.Q({ c : Clock }) -> Db.Q({ c : Clock })
described_outer = |q| q.filter(|x| outer(x.c))

expect runs_hot("a")

expect even(2)

main! = || {}
