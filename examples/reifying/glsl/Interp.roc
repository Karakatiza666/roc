# Evaluate a reified description on the CPU.
#
# Two things get called "interpreting the shader" and this is the second one.
# The first is free: a reified function is ordinary Roc, so calling it, testing
# it with `expect` and stepping through it need no machinery at all.
#
# This exists to check that the reifier and Roc agree. Run the same
# description two ways and compare:
#
#     expect Interp.run(Code.graph(wobble), probe) == Ok(wobble(probe))
#
# That is a differential test between the reified description and the language
# it came from, and it catches the class of bug otherwise found by looking at
# pixels. It is also the software fallback for a machine with no GPU, which is
# what headless CI is.
Interp :: {}.{

	## A value a reified expression can evaluate to. A GLSL vector is a list of
	## floats rather than four named fields, so one swizzle rule covers every
	## width. A record is its fields by name, which is how a caller supplies
	## the shader's two input records.
	Value := [Float(F64), Boolean(Bool), Text(Str), Vector(List(F64)), Fields(List({ name : Str, value : Value }))].{
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
			Fields(fields) => "{ ${Str.join_with(fields.map(|field| "${field.name}: ${field.value.to_str()}"), ", ")} }"
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

	## What evaluation reads: the root row's arguments, and the value of each
	## def of the enclosing blocks.
	Scope : { args : List(Value), defs : List({ id : U32, value : Value }) }

	## Evaluate the root row of a description on the given arguments, one per
	## parameter of the reified function.
	run : Code.Graph, List(Value) -> Try(Value, Error)
	run = |graph, args| Interp.eval(graph.to_tree(graph.root_row().id), { args, defs: [] })

	## Evaluate one tree: a block runs its defs in order, then its end.
	eval : Code.Tree, Scope -> Try(Value, Error)
	eval = |tree, scope| match tree {
		Param(k) => match scope.args.get(k.to_u64()) {
			Ok(value) => Ok(value)
			Err(_) => Err(Unbound("parameter ${k.to_str()}"))
		}
		Def(n) => match scope.defs.find_first(|def| def.id == n) {
			Ok(def) => Ok(def.value)
			Err(_) => Err(Unbound("node ${n.to_str()}"))
		}
		Arg(_) | Out(_) => Err(UnknownCall("a loop's or a branch's state, which this interpreter evaluates no loop for"))
		Block(block) => {
			inner = block.defs.fold_try(
				scope,
				|acc, def| {
					value = Interp.eval(def.value, acc)?
					Ok({ ..acc, defs: acc.defs.append({ id: def.id, value }) })
				},
			)?
			match block.end {
				Value([only]) => Interp.eval(only, inner)
				Value(_) | Jump(_) | Return(_) | Continue(_) | Break(_) | Branch(_) =>
					Err(UnknownCall("this interpreter evaluates an expression, and a statement that exits has nowhere to go"))
			}
		}
		Op(node) => Interp.eval_op(node.op, node.args, scope)
	}

	eval_op : Code.Op, List(Code.Tree), Scope -> Try(Value, Error)
	eval_op = |op, args, scope| match op {
		Lit(literal) => match literal {
			Frac(number, _) => Ok(Value.Float(number))
			Int(number, _) => Ok(Value.Float(number.to_f64()))
			Fixed(number) => Ok(Value.Float(number.to_f64()))
			Bool(flag) => Ok(Value.Boolean(flag))
			Str(text) => Ok(Value.Text(text))
			Bytes(_) => Err(UnknownCall("a byte blob has no CPU value in this interpreter"))
		}
		Prim(prim) => Interp.call(prim.owner, prim.method, args.map_try(|arg| Interp.eval(arg, scope))?)
		And(_) => Interp.connective(args, scope, Bool.False)
		Or(_) => Interp.connective(args, scope, Bool.True)
		Record(names) => {
			values = args.map_try(|arg| Interp.eval(arg, scope))?
			Ok(Value.Fields(List.map2(names, values, |name, value| { name, value })))
		}
		# A vector nominal wraps a record of its lanes; the lanes keep the
		# order its type declares them in.
		Wrap(name) => match (Interp.lanes_of(name), args) {
			(Ok(lanes), [inner]) => match Interp.eval(inner, scope)? {
				Fields(fields) => Ok(Value.Vector(lanes.map_try(|lane| Interp.float(Interp.named(fields, lane)?))?))
				other => Ok(other)
			}
			(_, [inner]) => Interp.eval(inner, scope)
			_ => Err(UnknownCall("a wrap of more than one value"))
		}
		Unwrap => match args {
			[inner] => Interp.eval(inner, scope)
			_ => Err(UnknownCall("an unwrap of more than one value"))
		}
		Tuple => Ok(Value.Vector(args.map_try(|arg| Interp.float(Interp.eval(arg, scope)?))?))
		Field(name) => match args {
			[inner] => match Interp.eval(inner, scope)? {
				Fields(fields) => Interp.named(fields, name)
				other => Interp.lane(other, name)
			}
			_ => Err(UnknownCall("a field read of more than one value"))
		}
		Index(position) => match args {
			[inner] => Interp.lane_at(Interp.eval(inner, scope)?, position)
			_ => Err(UnknownCall("a lane read of more than one value"))
		}
		Switch(sw) => match (sw.arms, args) {
			([first, second], [test, first_arm, second_arm]) => match Interp.eval(test, scope)? {
				Boolean(flag) =>
					if Interp.selects(first.key, flag) {
						Interp.eval(first_arm, scope)
					} else if Interp.selects(second.key, flag) {
						Interp.eval(second_arm, scope)
					} else {
						Err(UnknownCall("a `Bool` switch with no arm for its test"))
					}
				_ => Err(NotAFloat("an `if` condition must be a Bool"))
			}
			_ => Err(UnknownCall("a switch on a tag union, which this interpreter has no values for"))
		}
		Crash => match args {
			[message] => Err(Crashed(Interp.Value.to_str(Interp.eval(message, scope)?)))
			_ => Err(Crashed(""))
		}
		Call(_) => Err(UnknownCall("a call to another row, which this interpreter does not follow"))
		Closure(_) | Lambda(_) => Err(UnknownCall("a function value, which this interpreter has no value for"))
		List | Item => Err(UnknownCall("a list has no CPU value in this interpreter"))
		Tag(name) => Err(UnknownCall("`${name}` is a tag, and this interpreter has no tag value"))
		Payload(name, _) => Err(UnknownCall("`${name}` is a tag, and this interpreter has no tag value"))
		OptField(name) => Err(UnknownCall("`${name}` may be absent, and this interpreter has no value for a field that is not there"))
		ForRange(_) | ForList(_) | Loop(_) => Err(UnknownCall("this interpreter evaluates an expression, and a loop carries a state it has nowhere to keep"))
		Derived(method, _) => Err(UnknownCall("`${method}` is derived by the compiler and this interpreter owns no vehicle for it"))
	}

	## `And` and `Or` evaluate each operand only while the ones before it
	## decided nothing. `decides` is the value that settles the result.
	connective : List(Code.Tree), Scope, Bool -> Try(Value, Error)
	connective = |operands, scope, decides| {
		settled = operands.fold_try(
			Undecided,
			|state, operand| match state {
				Decided => Ok(Decided)
				Undecided => match Interp.eval(operand, scope)? {
					Boolean(flag) => Ok(if flag == decides Decided else Undecided)
					_ => Err(NotAFloat("`and` and `or` need Bools"))
				}
			},
		)?
		match settled {
			Decided => Ok(Value.Boolean(decides))
			Undecided => Ok(Value.Boolean(!decides))
		}
	}

	## Whether an arm is the one a test with this outcome selects.
	selects : Code.Key, Bool -> Bool
	selects = |key, flag| match key {
		Lit(Bool(expected)) => expected == flag
		Tag(name) => (name == "True") == flag
		Lit(_) | Len(_) | AtLeast(_) | Default => Bool.False
	}

	named : List({ name : Str, value : Value }), Str -> Try(Value, Error)
	named = |fields, name| match fields.find_first(|field| field.name == name) {
		Ok(found) => Ok(found.value)
		Err(_) => Err(Unbound(name))
	}

	## The lanes of a `Glsl` vector nominal, in the order its type declares them.
	lanes_of : Str -> Try(List(Str), [NotAVector])
	lanes_of = |name| match name {
		"Glsl.Vec2" => Ok(["x", "y"])
		"Glsl.Vec3" => Ok(["x", "y", "z"])
		"Glsl.Vec4" => Ok(["r", "g", "b", "a"])
		_ => Err(NotAVector)
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

	## One `Prim`, by the owner and method it carries: the builtin number
	## methods, `Bool.not`, and the `Glsl` functions `Glsl.roc` emits.
	call : Str, Str, List(Value) -> Try(Value, Error)
	call = |owner, method, args| match (method, args) {
		("not", [Boolean(flag)]) => Ok(Value.Boolean(!flag))
		("negate", [only]) => Interp.unary(only, |x| -x)
		("plus", [a, b]) | ("offset", [a, b]) => Interp.arith(method, a, b, |x, y| x + y)
		("minus", [a, b]) => Interp.arith(method, a, b, |x, y| x - y)
		("times", [a, b]) | ("scale", [a, b]) => Interp.arith(method, a, b, |x, y| x * y)
		("div_by", [a, b]) => Interp.arith(method, a, b, |x, y| x / y)
		("div_trunc_by", [a, b]) => Interp.arith(method, a, b, |x, y| F64.div_trunc_by(x, y))
		("rem_by", [a, b]) => Interp.arith(method, a, b, |x, y| x - y * F64.div_trunc_by(x, y))
		("is_lt", [a, b]) => Interp.compare(a, b, |x, y| x < y)
		("is_gt", [a, b]) => Interp.compare(a, b, |x, y| x > y)
		("is_lte", [a, b]) => Interp.compare(a, b, |x, y| x <= y)
		("is_gte", [a, b]) => Interp.compare(a, b, |x, y| x >= y)
		("is_eq", [a, b]) => Interp.equals(a, b)
		("sin", [only]) => Interp.unary(only, F64.sin)
		("cos", [only]) => Interp.unary(only, F64.cos)
		("tan", [only]) => Interp.unary(only, F64.tan)
		("sqrt", [only]) => Interp.unary(only, F64.sqrt)
		("abs", [only]) => Interp.unary(only, F64.abs)
		("min", [a, b]) => Interp.arith(method, a, b, |x, y| if x < y x else y)
		("max", [a, b]) => Interp.arith(method, a, b, |x, y| if x > y x else y)
		("pow", [a, b]) => Interp.arith(method, a, b, |x, y| x.pow(y))
		_ => Err(UnknownCall("${owner}.${method}"))
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
				Ok(Value.Vector(List.map2(a, b, step)))
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

	unary : Value, (F64 -> F64) -> Try(Value, Error)
	unary = |value, step| match value {
		Vector(lanes) => Ok(Value.Vector(lanes.map(step)))
		_ => Ok(Value.Float(step(Interp.float(value)?)))
	}
}
