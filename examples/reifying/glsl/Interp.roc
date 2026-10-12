# Evaluate a `Code.Ir` on the CPU.
#
# Two things get called "interpreting the shader" and this is the second one.
# The first is free: a reified function is ordinary Roc, so calling it, testing
# it with `expect` and stepping through it need no machinery at all.
#
# This exists to check that the reifier and Roc agree. Run the same IR two
# ways and compare:
#
#     expect Interp.eval(Glsl.fragment_330(wobble).ir, probe) == wobble(probe)
#
# That is a differential test between the reified description and the language
# it came from, and it catches the class of bug otherwise found by looking at
# pixels. It is also the software fallback for a machine with no GPU, which is
# what headless CI is.
Interp :: {}.{

	## A value a reified expression can evaluate to. A GLSL vector is a list of
	## floats rather than four named fields, so one swizzle rule covers every
	## width.
	Value := [Float(F64), Boolean(Bool), Text(Str), Vector(List(F64))].{
		to_str : Value -> Str
		to_str = |value| match value {
			Float(number) => number.to_str()
			Boolean(flag) => if flag {
				"true"
			} else {
				"false"
			}
			Text(text) => text
			Vector(lanes) => "(${Str.join_with(lanes.map(|lane| lane.to_str()), ", ")})"
		}
	}

	## Why an expression could not be evaluated. Every one names the construct.
	Error := [
		Unbound(Str),
		NotAFloat(Str),
		NotAVector(Str),
		UnknownCall(Str),
		UnknownOperator(Str),
		NoSuchLane(Str),
		Crashed(Str),
	]

	## One name in scope, and what it evaluates to.
	Binding := { name : Str, value : Value }

	## Evaluate a reified expression under the given bindings.
	##
	## A `Lambda` at the root is unwrapped: its parameters are expected to be
	## in `scope` already, which is how a caller supplies the shader's inputs.
	eval : Code.Ir, List(Binding) -> Try(Value, Error)
	eval = |node, scope| match node {
		Lambda(_, body, _) => Interp.eval(body, scope)

		Param(name, _) => Interp.lookup(scope, name)
		Local(name, _) => Interp.lookup(scope, name)

		Lit(literal, _) => match literal {
			Frac(number, _) => Ok(Value.Float(number))
			Int(number, _) => Ok(Value.Float(number.to_f64()))
			Fixed(number) => Ok(Value.Float(number.to_f64()))
			Bool(flag) => Ok(Value.Boolean(flag))
			Str(text) => Ok(Value.Text(text))
			Bytes(_) => Err(UnknownCall("a byte blob has no CPU value in this interpreter"))
		}

		Let(name, bound, rest, _) => {
			value = Interp.eval(bound, scope)?
			Interp.eval(rest, scope.append({ name, value }))
		}

		Field(receiver, name, _) => {
			# A field read straight off a lambda parameter is an input by name.
			direct = match receiver {
				Param(_, _) => Bool.True
				_ => Bool.False
			}
			if direct {
				Interp.lookup(scope, name)
			} else {
				Interp.lane(Interp.eval(receiver, scope)?, name)
			}
		}

		Index(receiver, position, _) => Interp.lane_at(Interp.eval(receiver, scope)?, position)

		Binop(op, lhs, rhs, _) => Interp.apply(op, Interp.eval(lhs, scope)?, Interp.eval(rhs, scope)?)

		Unary(op, operand, _) => {
			value = Interp.eval(operand, scope)?
			match op {
				"neg" => Ok(Value.Float(-(Interp.float(value)?)))
				"not" => match value {
					Boolean(flag) => Ok(Value.Boolean(!flag))
					_ => Err(NotAFloat("`not` needs a Bool"))
				}
				_ => Err(UnknownOperator(op))
			}
		}

		If(condition, then_branch, else_branch, _) => match Interp.eval(condition, scope)? {
			Boolean(Bool.True) => Interp.eval(then_branch, scope)
			Boolean(Bool.False) => Interp.eval(else_branch, scope)
			_ => Err(NotAFloat("an `if` condition must be a Bool"))
		}

		MakeTuple(elems, _) => {
			values = elems.map_try(|elem| Interp.eval(elem, scope))?
			lanes = values.map_try(Interp.float)?
			Ok(Value.Vector(lanes))
		}

		Call(callee, args, _) => {
			values = args.map_try(|arg| Interp.eval(arg, scope))?
			Interp.call(callee, values)
		}

		OptField(_, name, _) => Err(UnknownCall("`${name}` may be absent, and this interpreter has no value for a field that is not there"))
		MakeRecord(_, _) => Err(UnknownCall("a record has no CPU value in this interpreter"))
		MakeList(_, _) => Err(UnknownCall("a list has no CPU value in this interpreter"))
		MakeTag(name, _, _) => Err(UnknownCall("`${name}` is a tag, and this interpreter has no tag value"))
		Match(_, _, _) => Err(UnknownCall("`match` needs tag values, which this interpreter has none of"))
		Derived(method, _, _, _) => Err(UnknownCall("`${method}` is derived by the compiler and this interpreter owns no vehicle for it"))
		Widen(_, _) => Err(UnknownCall("a widening moves a tag between unions, and this interpreter has no tag value"))
		Range(_, _, _, _) => Err(UnknownCall("a range counts whole numbers, and this interpreter values floats and vectors"))
		For(_, _) => Err(UnknownCall("this interpreter evaluates an expression, and a loop carries a state it has nowhere to keep"))
		While(_, _) => Err(UnknownCall("this interpreter evaluates an expression, and a loop carries a state it has nowhere to keep"))
		Break(_, _) => Err(UnknownCall("a `break` stands inside a loop, and this interpreter evaluates no loop for it to leave"))
		Return(_, _) => Err(UnknownCall("a `return` node stands inside a loop, and this interpreter evaluates no loop for it to leave"))
		Crash(message, _) => Err(Crashed(Interp.Value.to_str(Interp.eval(message, scope)?)))
	}

	lookup : List(Binding), Str -> Try(Value, Error)
	lookup = |scope, name| match scope.keep_if(|binding| binding.name == name).last() {
		Ok(found) => Ok(found.value)
		Err(_) => Err(Unbound(name))
	}

	float : Value -> Try(F64, Error)
	float = |value| match value {
		Float(number) => Ok(number)
		_ => Err(NotAFloat(Interp.Value.to_str(value)))
	}

	## Swizzles, by the names GLSL and Roc each use for a lane.
	lane : Value, Str -> Try(Value, Error)
	lane = |value, name| match name {
		"x" => Interp.lane_at(value, 0)
		"r" => Interp.lane_at(value, 0)
		"y" => Interp.lane_at(value, 1)
		"g" => Interp.lane_at(value, 1)
		"z" => Interp.lane_at(value, 2)
		"b" => Interp.lane_at(value, 2)
		"w" => Interp.lane_at(value, 3)
		"a" => Interp.lane_at(value, 3)
		_ => Err(NoSuchLane(name))
	}

	lane_at : Value, U64 -> Try(Value, Error)
	lane_at = |value, position| match value {
		Vector(lanes) => match lanes.get(position) {
			Ok(found) => Ok(Value.Float(found))
			Err(_) => Err(NoSuchLane(position.to_str()))
		}
		_ => Err(NotAVector(Interp.Value.to_str(value)))
	}

	## A `Binop` names the Roc method the operator dispatched to, so these are
	## the method names and not the symbols.
	apply : Str, Value, Value -> Try(Value, Error)
	apply = |op, lhs, rhs| match op {
		"plus" => Interp.arith(op, lhs, rhs, |a, b| a + b)
		"minus" => Interp.arith(op, lhs, rhs, |a, b| a - b)
		"times" => Interp.arith(op, lhs, rhs, |a, b| a * b)
		"div_by" => Interp.arith(op, lhs, rhs, |a, b| a / b)
		"is_lt" => Interp.compare(lhs, rhs, |a, b| a < b)
		"is_gt" => Interp.compare(lhs, rhs, |a, b| a > b)
		"is_lte" => Interp.compare(lhs, rhs, |a, b| a <= b)
		"is_gte" => Interp.compare(lhs, rhs, |a, b| a >= b)
		"is_eq" => Interp.equals(lhs, rhs)
		"and" => Interp.logic(op, lhs, rhs, |a, b| a and b)
		"or" => Interp.logic(op, lhs, rhs, |a, b| a or b)
		_ => Err(UnknownOperator(op))
	}

	## Arithmetic is per lane, so a scalar broadcasts across a vector exactly
	## as it does in GLSL.
	arith : Str, Value, Value, (F64, F64 -> F64) -> Try(Value, Error)
	arith = |op, lhs, rhs, step| match (lhs, rhs) {
		(Float(a), Float(b)) => Ok(Value.Float(step(a, b)))
		(Vector(a), Float(b)) => Ok(Value.Vector(a.map(|each| step(each, b))))
		(Float(a), Vector(b)) => Ok(Value.Vector(b.map(|each| step(a, each))))
		(Vector(a), Vector(b)) =>
			if a.len() == b.len() {
				Ok(
					Value.Vector(
						a.map_with_index(
							|each, index| match b.get(index) {
								Ok(other) => step(each, other)
								Err(_) => each
							},
						),
					),
				)
			} else {
				Err(NotAVector("`${op}` needs two vectors of the same width"))
			}
		_ => Err(NotAFloat("`${op}` needs numbers"))
	}

	compare : Value, Value, (F64, F64 -> Bool) -> Try(Value, Error)
	compare = |lhs, rhs, step| Ok(Value.Boolean(step(Interp.float(lhs)?, Interp.float(rhs)?)))

	## Equality is the one comparison that is not numeric only: the compiler
	## expands a derived `==` on any scalar, `Bool` and `Str` included.
	equals : Value, Value -> Try(Value, Error)
	equals = |lhs, rhs| match (lhs, rhs) {
		(Boolean(a), Boolean(b)) => Ok(Value.Boolean(a == b))
		(Text(a), Text(b)) => Ok(Value.Boolean(a == b))
		_ => Interp.compare(lhs, rhs, |a, b| a == b)
	}

	logic : Str, Value, Value, (Bool, Bool -> Bool) -> Try(Value, Error)
	logic = |op, lhs, rhs, step| match (lhs, rhs) {
		(Boolean(a), Boolean(b)) => Ok(Value.Boolean(step(a, b)))
		_ => Err(NotAFloat("`${op}` needs two Bools"))
	}

	## The same calls `Glsl.roc` is willing to emit, evaluated on the CPU.
	call : Str, List(Value) -> Try(Value, Error)
	call = |callee, args| {
		name = match callee.split_on(".").last() {
			Ok(segment) => segment
			Err(_) => callee
		}
		match (name, args) {
			("sin", [only]) => Interp.unary(only, F64.sin)
			("cos", [only]) => Interp.unary(only, F64.cos)
			("sqrt", [only]) => Interp.unary(only, F64.sqrt)
			("abs", [only]) => Interp.unary(only, F64.abs)
			("tan", [only]) => Interp.unary(only, F64.tan)
			("min", [a, b]) => Interp.arith(
				name,
				a,
				b,
				|x, y| if x < y {
					x
				} else {
					y
				},
			)
			("max", [a, b]) => Interp.arith(
				name,
				a,
				b,
				|x, y| if x > y {
					x
				} else {
					y
				},
			)
			("pow", [a, b]) => Interp.arith(name, a, b, |x, y| x.pow(y))
			("vec2", [a, b]) => Interp.vector([a, b])
			("vec3", [a, b, c]) => Interp.vector([a, b, c])
			("vec4", [a, b, c, d]) => Interp.vector([a, b, c, d])
			_ => Err(UnknownCall(callee))
		}
	}

	unary : Value, (F64 -> F64) -> Try(Value, Error)
	unary = |value, step| match value {
		Vector(lanes) => Ok(Value.Vector(lanes.map(step)))
		_ => Ok(Value.Float(step(Interp.float(value)?)))
	}

	vector : List(Value) -> Try(Value, Error)
	vector = |values| Ok(Value.Vector(values.map_try(Interp.float)?))
}
