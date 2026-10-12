# A GLSL 330 fragment-shader translator: a reified Roc function in, shader
# source out.
#
# This is ordinary Roc that runs at compile time. Naming a Roc function where
# `fragment_330` expects a `Code(f)` is what reifies it: the compiler describes
# the function, `Code.ir` opens the description, and this emits the GLSL that
# raylib accepts together with the interface the application binds through.
#
# A fragment shader takes two records. The first holds the varyings the vertex
# stage interpolates, which become `in` declarations; the second holds the
# uniforms the application writes, which become `uniform` declarations. The
# return type becomes `finalColor`.
#
# The vector types live here because their lanes are named the way GLSL names
# them, so `uv.x` reads the same in Roc and in the emitted shader, and because
# a reified function is ordinary Roc: every method below computes the value it
# describes, so a shader can be called and tested on the CPU.
Glsl :: {}.{

	## A GLSL type. The subset a fragment shader needs, and no more.
	Kind := [Float, Int, Uint, Boolean, Vec2, Vec3, Vec4, Sampler2D].{
		is_vec4 : Kind -> Bool
		is_vec4 = |kind| match kind {
			Vec4 => Bool.True
			_ => Bool.False
		}

		to_str : Kind -> Str
		to_str = |kind| match kind {
			Float => "float"
			Int => "int"
			Uint => "uint"
			Boolean => "bool"
			Vec2 => "vec2"
			Vec3 => "vec3"
			Vec4 => "vec4"
			Sampler2D => "sampler2D"
		}
	}

	## A GLSL `vec2`.
	Vec2 := { x : F32, y : F32 }.{
		plus : Vec2, Vec2 -> Vec2
		plus = |l, r| Vec2.({ x: l.x + r.x, y: l.y + r.y })

		times : Vec2, Vec2 -> Vec2
		times = |l, r| Vec2.({ x: l.x * r.x, y: l.y * r.y })

		scale : Vec2, F32 -> Vec2
		scale = |v, k| Vec2.({ x: v.x * k, y: v.y * k })

		offset : Vec2, F32 -> Vec2
		offset = |v, k| Vec2.({ x: v.x + k, y: v.y + k })
	}

	## A GLSL `vec3`.
	Vec3 := { x : F32, y : F32, z : F32 }.{
		plus : Vec3, Vec3 -> Vec3
		plus = |l, r| Vec3.({ x: l.x + r.x, y: l.y + r.y, z: l.z + r.z })

		times : Vec3, Vec3 -> Vec3
		times = |l, r| Vec3.({ x: l.x * r.x, y: l.y * r.y, z: l.z * r.z })

		scale : Vec3, F32 -> Vec3
		scale = |v, k| Vec3.({ x: v.x * k, y: v.y * k, z: v.z * k })

		offset : Vec3, F32 -> Vec3
		offset = |v, k| Vec3.({ x: v.x + k, y: v.y + k, z: v.z + k })
	}

	## A GLSL `vec4`. Its lanes are the colour names, because every `vec4` a
	## fragment shader returns is a colour.
	Vec4 := { r : F32, g : F32, b : F32, a : F32 }.{
		plus : Vec4, Vec4 -> Vec4
		plus = |l, r| Vec4.({ r: l.r + r.r, g: l.g + r.g, b: l.b + r.b, a: l.a + r.a })

		times : Vec4, Vec4 -> Vec4
		times = |l, r| Vec4.({ r: l.r * r.r, g: l.g * r.g, b: l.b * r.b, a: l.a * r.a })

		scale : Vec4, F32 -> Vec4
		scale = |v, k| Vec4.({ r: v.r * k, g: v.g * k, b: v.b * k, a: v.a * k })

		offset : Vec4, F32 -> Vec4
		offset = |v, k| Vec4.({ r: v.r + k, g: v.g + k, b: v.b + k, a: v.a + k })
	}

	## A texture bound to a sampling unit: `uniform sampler2D` in GLSL.
	##
	## GLSL never looks inside a sampler, so what it holds is the CPU's business:
	## the function that samples it. A reified shader is ordinary Roc, so a test
	## calls it with whatever sampler it wants and gets the shader's real answer.
	Sampler := { at : Glsl.Vec2 -> Glsl.Vec4 }.{
		texture : Sampler, Glsl.Vec2 -> Glsl.Vec4
		texture = |Sampler.(image), uv| {
			sample = image.at
			sample(uv)
		}
	}

	## One shader input, named as the application must name it.
	Binding := { name : Str, kind : Kind, storage : [In, Uniform] }

	## The compiled shader, and the interface it expects.
	##
	## `bindings` exists so a renamed parameter fails at build time rather than
	## becoming a runtime `UniformNotFound` at the first `uniform_f32!` call.
	Fragment := { source : Str, bindings : List(Binding) }

	## Why a reified function is not a shader. Every rejection names the
	## construct and, where there is one, the alternative.
	Error := [Unsupported(Str), BadType(Str), BadInterface(Str)]

	## Compile a reified Roc function to a GLSL 330 fragment shader.
	##
	## Naming a function here reifies it: the compiler describes the function
	## during `roc build` and hands the description over as a `Code(f)`.
	fragment_330 : Code(f) -> Try(Fragment, Error)
	fragment_330 = |code| {
		described = Code.ir(code)
		shader_meta = described.node_meta()
		lambda = match described {
			Lambda(ps, b, _) => { params: ps, body: b }
			_ => return Err(BadInterface("${Glsl.at(shader_meta)}a shader must be a function; this is a bare expression"))
		}
		inputs = match lambda.params {
			[interpolated, per_draw] => { interpolated, per_draw }
			_ => return Err(BadInterface("${Glsl.at(shader_meta)}a fragment shader takes two records: the varyings it reads, then the uniforms it reads"))
		}
		varyings = Glsl.located(Glsl.bindings_of(inputs.interpolated.ty, In), shader_meta)?
		uniforms = Glsl.located(Glsl.bindings_of(inputs.per_draw.ty, Uniform), shader_meta)?
		bindings = varyings.concat(uniforms)
		body_meta = lambda.body.node_meta()
		out_kind = Glsl.located(Glsl.kind_for(body_meta.ty), body_meta)?
		if !out_kind.is_vec4() {
			return Err(BadType("${Glsl.at(body_meta)}a fragment shader must return Vec4; this one returns ${out_kind.to_str()}"))
		}
		rendered = Glsl.render(lambda.body, [inputs.interpolated.name, inputs.per_draw.name])?
		decls = bindings.map(Glsl.declare)
		Ok(
			Fragment.(
				{
					source: Str.join_with(
						[
							"#version 330",
							Str.join_with(decls, "\n"),
							"out vec4 finalColor;",
							"void main() {",
							rendered.statements,
							"\tfinalColor = ${rendered.value};",
							"}",
						].keep_if(Glsl.is_present),
						"\n",
					),
					bindings,
				},
			),
		)
	}

	## Every field of one parameter record, as a binding with that record's
	## storage. Which record a field is in is what makes it an `in` or a
	## `uniform`, so the distinction is a type-level fact and not a naming rule.
	bindings_of : Code.Ty, [In, Uniform] -> Try(List(Binding), Error)
	bindings_of = |ty, storage| match ty {
		Record(fields) => fields.map_try(|field| Glsl.binding_for(field, storage))
		Named(_, Record(fields)) => fields.map_try(|field| Glsl.binding_for(field, storage))
		_ => Err(BadInterface("a shader's parameters are records; each field is one shader input"))
	}

	## A shader input is declared once and is there on every invocation, so a
	## field the record type says may be absent is not one.
	binding_for : { name : Str, ty : Code.Ty, presence : [Required, Optional] }, [In, Uniform] -> Try(Binding, Error)
	binding_for = |field, storage| match field.presence {
		Optional => Err(BadInterface("`${field.name}` may be absent, and a shader input is always there"))
		Required => Ok(Binding.({ name: field.name, kind: Glsl.kind_for(field.ty)?, storage }))
	}

	declare : Binding -> Str
	declare = |binding| {
		storage = match binding.storage {
			In => "in"
			Uniform => "uniform"
		}
		"${storage} ${binding.kind.to_str()} ${binding.name};"
	}

	## Map a reified Roc type onto its GLSL equivalent, or say why there is none.
	kind_for : Code.Ty -> Try(Kind, Error)
	kind_for = |ty| match ty {
		F32 => Ok(Kind.Float)
		I32 => Ok(Kind.Int)
		U32 => Ok(Kind.Uint)
		Bool => Ok(Kind.Boolean)
		Named("Glsl.Sampler", _) => Ok(Kind.Sampler2D)
		Named(name, backing) => match Glsl.vector_kind(name) {
			Ok(vec) => Ok(vec)
			Err(_) => Glsl.kind_for(backing)
		}
		Recursive(name) => Err(BadType("`${name}` reaches itself, and GLSL 330 has no recursive type"))
		Opaque("Glsl.Sampler", _) => Ok(Kind.Sampler2D)
		Tuple(elems) => match elems.len() {
			2 => Ok(Kind.Vec2)
			3 => Ok(Kind.Vec3)
			4 => Ok(Kind.Vec4)
			_ => Err(BadType("a ${elems.len().to_str()}-tuple has no GLSL type"))
		}
		F64 => Err(BadType("F64 has no place in a fragment shader; annotate this as F32"))
		Dec => Err(BadType("Dec is 128-bit fixed point and no GPU has it; annotate this as F32"))
		Str => Err(BadType("GLSL has no strings"))
		ListOf(_) => Err(BadType("GLSL has no growable lists"))
		_ => Err(BadType("`${ty.name()}` has no GLSL equivalent"))
	}

	## The lanes a vector is built from, in the order its constructor takes them.
	lanes_of : Kind -> Try(List(Str), Error)
	lanes_of = |kind| match kind {
		Vec2 => Ok(["x", "y"])
		Vec3 => Ok(["x", "y", "z"])
		Vec4 => Ok(["r", "g", "b", "a"])
		_ => Err(BadType("`${kind.to_str()}` is not built from lanes"))
	}

	## A rendered expression, plus the GLSL locals its `Let` bindings needed.
	Rendered := { statements : Str, value : Str }

	## Render a reified expression. `inputs` holds the names of the shader's two
	## parameters: a field read from either one is a shader input, so
	## `frag.uv` renders as `uv` rather than as a field access on a struct GLSL
	## never sees.
	render : Code.Ir, List(Str) -> Try(Rendered, Error)
	render = |node, inputs| match node {
		Lit(literal, _) => Glsl.plain(Glsl.literal(literal)?)

		Param(name, meta) =>
			if inputs.contains(name) {
				Err(BadInterface("${Glsl.at(meta)}the input record `${name}` has no GLSL value of its own; read a field from it"))
			} else {
				Glsl.plain(name)
			}

		Local(name, _) => Glsl.plain(name)

		Field(receiver, name, _) => {
			from_inputs = match receiver {
				Param(holder, _) => inputs.contains(holder)
				_ => Bool.False
			}
			if from_inputs {
				Glsl.plain(name)
			} else {
				inner = Glsl.render(receiver, inputs)?
				Ok(Rendered.({ statements: inner.statements, value: "${inner.value}.${name}" }))
			}
		}

		Index(receiver, position, meta) => {
			inner = Glsl.render(receiver, inputs)?
			lane = match position {
				0 => "x"
				1 => "y"
				2 => "z"
				3 => "w"
				_ => return Err(BadType("${Glsl.at(meta)}a GLSL vector has at most four lanes"))
			}
			Ok(Rendered.({ statements: inner.statements, value: "${inner.value}.${lane}" }))
		}

		Binop(op, lhs, rhs, meta) => {
			# The node's own type is what the operator produced, and a comparison
			# produces a Bool, so the operand type is the one that settles the form.
			form = Glsl.located(Glsl.operator(op, lhs.node_ty()), meta)?
			left = Glsl.render(lhs, inputs)?
			right = Glsl.render(rhs, inputs)?
			Ok(
				Rendered.(
					{
						statements: Glsl.both(left.statements, right.statements),
						value: form.over(left.value, right.value),
					},
				),
			)
		}

		Unary(op, operand, meta) => {
			symbol = match op {
				"neg" => "-"
				"not" => "!"
				_ => return Err(Unsupported("${Glsl.at(meta)}`${op}` has no GLSL form"))
			}
			inner = Glsl.render(operand, inputs)?
			Ok(Rendered.({ statements: inner.statements, value: "${symbol}(${inner.value})" }))
		}

		Call(callee, args, meta) => {
			rendered = args.map_try(|arg| Glsl.render(arg, inputs))?
			statements = Str.join_with(rendered.map(|r| r.statements).keep_if(Glsl.is_present), "\n")
			values = rendered.map(|r| r.value)
			match Glsl.broadcast(callee, values) {
				Ok(value) => Ok(Rendered.({ statements, value }))
				Err(_) => {
					name = Glsl.located(Glsl.builtin_name(callee, args.len()), meta)?
					Ok(Rendered.({ statements, value: "${name}(${Str.join_with(values, ", ")})" }))
				}
			}
		}

		MakeRecord(fields, meta) => {
			kind = Glsl.located(Glsl.kind_for(meta.ty), meta)?
			lanes = Glsl.located(Glsl.lanes_of(kind), meta)?
			rendered = lanes.map_try(
				|lane| match fields.find_first(|field| field.name == lane) {
					Ok(field) => Glsl.render(field.value, inputs)
					Err(_) => Err(BadType("${Glsl.at(meta)}a ${kind.to_str()} is built from lanes named ${Str.join_with(lanes, ", ")}; this one has no `${lane}`"))
				},
			)?
			Ok(
				Rendered.(
					{
						statements: Str.join_with(rendered.map(|r| r.statements).keep_if(Glsl.is_present), "\n"),
						value: "${kind.to_str()}(${Str.join_with(rendered.map(|r| r.value), ", ")})",
					},
				),
			)
		}

		MakeTuple(elems, meta) => {
			kind = Glsl.located(Glsl.kind_for(meta.ty), meta)?
			rendered = elems.map_try(|elem| Glsl.render(elem, inputs))?
			Ok(
				Rendered.(
					{
						statements: Str.join_with(rendered.map(|r| r.statements).keep_if(Glsl.is_present), "\n"),
						value: "${kind.to_str()}(${Str.join_with(rendered.map(|r| r.value), ", ")})",
					},
				),
			)
		}

		If(condition, then_branch, else_branch, _) => {
			test = Glsl.render(condition, inputs)?
			yes = Glsl.render(then_branch, inputs)?
			no = Glsl.render(else_branch, inputs)?
			Ok(
				Rendered.(
					{
						statements: Glsl.both(test.statements, Glsl.both(yes.statements, no.statements)),
						value: "(${test.value} ? ${yes.value} : ${no.value})",
					},
				),
			)
		}

		Let(name, bound, rest, _) => {
			bound_meta = bound.node_meta()
			kind = Glsl.located(Glsl.kind_for(bound_meta.ty), bound_meta)?
			value = Glsl.render(bound, inputs)?
			body = Glsl.render(rest, inputs)?
			declaration = "\t${kind.to_str()} ${name} = ${value.value};"
			Ok(
				Rendered.(
					{
						statements: Glsl.both(Glsl.both(value.statements, declaration), body.statements),
						value: body.value,
					},
				),
			)
		}

		OptField(_, name, meta) => Err(Unsupported("${Glsl.at(meta)}`${name}` may be absent, and GLSL 330 has no form for a field that is not there"))
		MakeList(_, meta) => Err(Unsupported("${Glsl.at(meta)}GLSL 330 has no list; a fixed-lane vector is built from a tuple"))
		MakeTag(name, _, meta) => Err(Unsupported("${Glsl.at(meta)}GLSL 330 has no tag union, so `${name}` has no GLSL form"))
		Match(_, _, meta) => Err(Unsupported("${Glsl.at(meta)}GLSL 330 has no tag union to match on; use `if`"))
		Derived(method, _, _, meta) => Err(Unsupported("${Glsl.at(meta)}`${method}` is derived by the compiler and a shader owns no vehicle for it"))
		Widen(_, meta) => Err(Unsupported("${Glsl.at(meta)}GLSL 330 has no tag union, so a widening between two has no GLSL form"))
		Range(_, _, _, meta) => Err(Unsupported("${Glsl.at(meta)}a range has no GLSL value of its own; it reaches a shader as the bounds of a `for`"))
		For(_, meta) => Err(Unsupported("${Glsl.at(meta)}this translator renders an expression and the declarations under it, and a loop is a statement it does not emit"))
		While(_, meta) => Err(Unsupported("${Glsl.at(meta)}this translator renders an expression and the declarations under it, and a loop is a statement it does not emit"))
		Break(_, meta) => Err(Unsupported("${Glsl.at(meta)}a `break` stands inside a loop, and this translator emits no loop for it to leave"))
		Return(_, meta) => Err(Unsupported("${Glsl.at(meta)}a `return` node stands inside a loop, and this translator emits no loop for it to leave"))
		Lambda(_, _, meta) => Err(Unsupported("${Glsl.at(meta)}a shader cannot contain a nested function"))
		Crash(_, meta) => Err(Unsupported("${Glsl.at(meta)}`crash` cannot run on a GPU"))
	}

	## Where a node was written, as a prefix an error message can lead with.
	##
	## Every [Code.Ir] node carries one, so a shader that will not compile names
	## the line the author has to look at rather than only the construct.
	at : Code.Meta -> Str
	at = |meta| {
		region = meta.region
		"${region.module_name}:${region.start_line.to_str()}:${region.start_column.to_str()}: "
	}

	## Name where a node was written on an error raised by something that knows
	## only a type or an operator, and so cannot say it itself.
	located : Try(a, Error), Code.Meta -> Try(a, Error)
	located = |result, meta| match result {
		Ok(value) => Ok(value)
		Err(Unsupported(message)) => Err(Unsupported("${Glsl.at(meta)}${message}"))
		Err(BadType(message)) => Err(BadType("${Glsl.at(meta)}${message}"))
		Err(BadInterface(message)) => Err(BadInterface("${Glsl.at(meta)}${message}"))
	}

	plain : Str -> Try(Rendered, Error)
	plain = |value| Ok(Rendered.({ statements: "", value }))

	is_present : Str -> Bool
	is_present = |text| !text.is_empty()

	both : Str, Str -> Str
	both = |first, second|
		if first.is_empty() {
			second
		} else if second.is_empty() {
			first
		} else {
			"${first}\n${second}"
		}

	literal : Code.Lit -> Try(Str, Error)
	literal = |value| match value {
		Frac(number, ty) => Ok(Glsl.float_str(number, ty))
		Int(number, _) => Ok(number.to_str())
		Bool(flag) => Ok(
			if flag {
				"true"
			} else {
				"false"
			},
		)
		Fixed(_) => Err(BadType("Dec is 128-bit fixed point and no GPU has it; annotate this literal as F32"))
		Str(_) => Err(BadType("GLSL has no strings"))
		Bytes(_) => Err(BadType("GLSL has no byte arrays; upload this file as a texture or a buffer instead"))
	}

	## A literal arrives widened to `F64`, so an `F32` prints back through `F32`
	## or a shader reads `0.004` as `0.004000000189989805`. GLSL also infers
	## `int` for a bare `2`, so a float literal keeps its point.
	float_str : F64, Code.Ty -> Str
	float_str = |number, ty| {
		rendered = match ty {
			F32 => number.to_f32_wrap().to_str()
			_ => number.to_str()
		}
		if rendered.contains(".") or rendered.contains("e") {
			rendered
		} else {
			"${rendered}.0"
		}
	}

	## How GLSL writes one binary operator over two rendered operands.
	##
	## Three of the Roc operators are not one symbol in GLSL, which is why this
	## is a form and not the symbol it was.
	Form := [Infix(Str), Apply(Str), Truncated].{
		over : Form, Str, Str -> Str
		over = |form, lhs, rhs| match form {
			Infix(symbol) => "(${lhs} ${symbol} ${rhs})"
			Apply(name) => "${name}(${lhs}, ${rhs})"
			Truncated => "trunc(${lhs} / ${rhs})"
		}
	}

	## A `Binop` names the Roc method the operator dispatched to, so these are
	## the method names and not the symbols.
	##
	## Two of them read differently at a float, which is why the operand type is
	## here beside the name. Roc's `//` truncates toward zero and GLSL's `/` does
	## that only at an integer, and GLSL 330 spells the float remainder `mod` and
	## keeps `%` for integers. Both differences are silent in Roc: one computes
	## another number, the other does not compile on the driver.
	operator : Str, Code.Ty -> Try(Form, Error)
	operator = |method, operand| {
		whole = match operand.numeric() {
			Ok(number) => match number.kind {
				Int => Bool.True
				Frac => Bool.False
				Fixed => Bool.False
			}
			Err(_) => Bool.False
		}
		match method {
			"plus" => Ok(Form.Infix("+"))
			"minus" => Ok(Form.Infix("-"))
			"times" => Ok(Form.Infix("*"))
			"div_by" => Ok(Form.Infix("/"))
			"div_trunc_by" =>
				if whole {
					Ok(Form.Infix("/"))
				} else {
					Ok(Form.Truncated)
				}
			"rem_by" =>
				if whole {
					Ok(Form.Infix("%"))
				} else {
					Ok(Form.Apply("mod"))
				}
			"is_lt" => Ok(Form.Infix("<"))
			"is_gt" => Ok(Form.Infix(">"))
			"is_lte" => Ok(Form.Infix("<="))
			"is_gte" => Ok(Form.Infix(">="))
			"is_eq" => Ok(Form.Infix("=="))
			"and" => Ok(Form.Infix("&&"))
			"or" => Ok(Form.Infix("||"))
			_ => Err(Unsupported("`${method}` has no GLSL operator"))
		}
	}

	## GLSL broadcasts a scalar across a vector, which Roc has no operator for:
	## the right operand of `*` would have to be a vector too. `scale` and
	## `offset` are the methods that say it, and they render as the operator.
	broadcast : Str, List(Str) -> Try(Str, [NotBroadcast])
	broadcast = |callee, values| {
		symbol = match callee {
			"Glsl.Vec2.scale" | "Glsl.Vec3.scale" | "Glsl.Vec4.scale" => "*"
			"Glsl.Vec2.offset" | "Glsl.Vec3.offset" | "Glsl.Vec4.offset" => "+"
			_ => return Err(NotBroadcast)
		}
		match values {
			[lhs, rhs] => Ok("(${lhs} ${symbol} ${rhs})")
			_ => Err(NotBroadcast)
		}
	}

	## The calls a fragment shader may make, each under the whole name a
	## [Code.Ir] `Call` carries, beside the GLSL function that means the same.
	##
	## A `Call` name is complete, so this matches all of it. Matching the last
	## segment instead would send any module's own `sin` to the `sin` row and
	## emit a GLSL call to a function that computes something else.
	##
	## GLSL has more functions than these, and every one of them is missing
	## here because Roc's `F32` has no method that means it. A shader calls what
	## it can write, and anything else is named in the error, because a
	## translator that silently emits an unknown GLSL function moves the failure
	## to the driver.
	builtin_name : Str, U64 -> Try(Str, Error)
	builtin_name = |callee, arity| {
		supported = [
			{ roc: "Builtin.Num.F32.sin", glsl: "sin" },
			{ roc: "Builtin.Num.F32.cos", glsl: "cos" },
			{ roc: "Builtin.Num.F32.tan", glsl: "tan" },
			{ roc: "Builtin.Num.F32.asin", glsl: "asin" },
			{ roc: "Builtin.Num.F32.acos", glsl: "acos" },
			{ roc: "Builtin.Num.F32.atan", glsl: "atan" },
			{ roc: "Builtin.Num.F32.sqrt", glsl: "sqrt" },
			{ roc: "Builtin.Num.F32.abs", glsl: "abs" },
			{ roc: "Builtin.Num.F32.min", glsl: "min" },
			{ roc: "Builtin.Num.F32.max", glsl: "max" },
			{ roc: "Builtin.Num.F32.pow", glsl: "pow" },
			{ roc: "Glsl.Sampler.texture", glsl: "texture" },
		]
		match supported.find_first(|row| row.roc == callee) {
			Ok(row) => Ok(row.glsl)
			Err(_) => Err(Unsupported("`${callee}` is not one of the ${arity.to_str()}-argument functions a fragment shader may call"))
		}
	}

	## A nominal's name is complete too, so these are whole as well.
	vector_kind : Str -> Try(Kind, [NotAVector])
	vector_kind = |name| match name {
		"Glsl.Vec2" => Ok(Kind.Vec2)
		"Glsl.Vec3" => Ok(Kind.Vec3)
		"Glsl.Vec4" => Ok(Kind.Vec4)
		_ => Err(NotAVector)
	}
}
