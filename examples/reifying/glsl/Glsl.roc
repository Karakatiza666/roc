# A GLSL 330 fragment-shader translator: a reified Roc function in, shader
# source out.
#
# This is ordinary Roc that runs at compile time. Naming a Roc function where
# `fragment_330` expects a `Code.Inlined(f)` is what reifies it: the compiler
# describes the function, `Code.Inlined.inline` opens the description, and this
# emits the GLSL that raylib accepts together with the interface the
# application binds through.
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

	no_input : Error
	no_input = Unsupported("a value the shader reads from around itself has no GLSL form; pass it as a uniform")

	## The functions this translator reads by name: its cut. Each one is a
	## GLSL operator or function, so a shader that calls it receives a `Prim`
	## named `Glsl.Vec3` and `scale`, never the CPU body below, which would
	## turn one vector product into three lane products. Every other function
	## a shader calls, in this package or in any other, arrives as its body.
	code_primitives = (
		Vec2.plus,
		Vec2.times,
		Vec2.scale,
		Vec2.offset,
		Vec3.plus,
		Vec3.times,
		Vec3.scale,
		Vec3.offset,
		Vec4.plus,
		Vec4.times,
		Vec4.scale,
		Vec4.offset,
		Sampler.texture,
	)

	## Compile a reified Roc function to a GLSL 330 fragment shader.
	##
	## Naming a function here reifies it: the compiler describes the function
	## during `roc build` and hands the description over as a `Code.Inlined(f)`.
	## That is the `inline` view, because GLSL needs no function form here: every
	## call of a helper is inlined, however many calls it has. The root row is
	## the shader; `to_tree` gives it as nested expressions, with a def for each
	## value the body reads more than once.
	fragment_330 : Code.Inlined(f) -> Try(Fragment, Error)
	fragment_330 = |code| {
		graph = code.inline()
		row = graph.root_row()
		inputs = match row.params {
			[interpolated, per_draw] => { interpolated, per_draw }
			_ => return Err(BadInterface("a fragment shader takes two records: the varyings it reads, then the uniforms it reads"))
		}
		varyings = Glsl.bindings_of(inputs.interpolated, In)?
		uniforms = Glsl.bindings_of(inputs.per_draw, Uniform)?
		bindings = varyings.concat(uniforms)
		out_kind = Glsl.kind_for(row.result)?
		if !out_kind.is_vec4() {
			return Err(BadType("a fragment shader must return Vec4; this one returns ${out_kind.to_str()}"))
		}
		rendered = Glsl.render_block(graph.to_tree(row.id), { row, locals: [] })?
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

	## A rendered block: the GLSL locals its defs needed, and its value.
	Rendered := { statements : Str, value : Str }

	## What rendering reads: the row, for the types of its parameters and
	## nodes, and the GLSL text each def of the enclosing blocks stands for.
	Scope : { row : Code.Row, locals : List({ id : U32, text : Str }) }

	## Render a block. A def that only reads a lane or a field of a value that
	## already has a name is written where it is read, because GLSL reads it
	## as cheaply as a local; every other def becomes one GLSL local, so work
	## the body shares stays shared.
	render_block : Code.Tree, Scope -> Try(Rendered, Error)
	render_block = |tree, scope| match tree {
		Block(block) => {
			start = { scope, statements: "" }
			placed = block.defs.fold_try(
				start,
				|acc, def| {
					text = Glsl.render(def.value, acc.scope)?
					if Glsl.is_read(def.value) {
						Ok({ ..acc, scope: { ..acc.scope, locals: acc.scope.locals.append({ id: def.id, text }) } })
					} else {
						kind = Glsl.kind_for(Glsl.value_ty(def.value, acc.scope)?)?
						local = "n${def.id.to_str()}"
						declaration = "\t${kind.to_str()} ${local} = ${text};"
						Ok({
							scope: { ..acc.scope, locals: acc.scope.locals.append({ id: def.id, text: local }) },
							statements: Glsl.both(acc.statements, declaration),
						})
					}
				},
			)?
			value = match block.end {
				Value([only]) => Glsl.render(only, placed.scope)?
				Value(_) => return Err(Unsupported("a value that carries a loop's or a branch's state has no GLSL expression"))
				Jump(_) => return Err(Unsupported("a branch that continues after it is a statement this translator does not emit"))
				Return(_) => return Err(Unsupported("a `return` is a statement this translator does not emit"))
				Continue(_) => return Err(Unsupported("a loop is a statement this translator does not emit"))
				Break(_) => return Err(Unsupported("a loop is a statement this translator does not emit"))
				Branch(_) => return Err(Unsupported("a branch that leaves the shader early is a statement this translator does not emit"))
			}
			Ok(Rendered.({ statements: placed.statements, value }))
		}
		Op(_) | Param(_) | Input(_) | Arg(_) | Out(_) | Def(_) => Ok(Rendered.({ statements: "", value: Glsl.render(tree, scope)? }))
	}

	## Whether a def only reads a field, a lane or a nominal's backing out of a
	## parameter or another def.
	is_read : Code.Tree -> Bool
	is_read = |tree| match tree {
		Param(_) | Def(_) => Bool.True
		Op(node) => match (node.op, node.args) {
			(Field(_), [inner]) | (Index(_), [inner]) | (Unwrap, [inner]) => Glsl.is_read(inner)
			_ => Bool.False
		}
		Input(_) | Arg(_) | Out(_) | Block(_) => Bool.False
	}

	## The type a def is declared at. A nominal's backing is read under the
	## nominal's name, so a def that unwraps one is a local of the nominal.
	value_ty : Code.Tree, Scope -> Try(Code.Ty, Error)
	value_ty = |tree, scope| match tree {
		Op(node) => match (node.op, node.args) {
			(Unwrap, [inner]) => Glsl.value_ty(inner, scope)
			_ => Ok(node.ty)
		}
		Param(k) => match scope.row.params.get(k.to_u64()) {
			Ok(ty) => Ok(ty)
			Err(_) => Err(BadInterface("a read of a parameter the shader does not have"))
		}
		Def(n) => Ok(scope.row.node(n).ty)
		Arg(_) | Out(_) | Block(_) => Err(Unsupported("a value that carries a loop's or a branch's state has no GLSL local"))
		Input(_) => Err(Glsl.no_input)
	}

	## Render one expression. A field read straight off one of the shader's two
	## parameters is a shader input, so `frag.uv` renders as `uv` rather than as
	## a field access on a struct GLSL never sees.
	render : Code.Tree, Scope -> Try(Str, Error)
	render = |tree, scope| match tree {
		Param(_) => Err(BadInterface("an input record has no GLSL value of its own; read a field from it"))
		Def(n) => match scope.locals.find_first(|local| local.id == n) {
			Ok(local) => Ok(local.text)
			Err(_) => Err(Unsupported("a value read before the translator placed it"))
		}
		Arg(_) | Out(_) => Err(Unsupported("a value that carries a loop's or a branch's state has no GLSL expression"))
		Input(_) => Err(Glsl.no_input)
		Block(_) => {
			inner = Glsl.render_block(tree, scope)?
			if inner.statements.is_empty() {
				Ok(inner.value)
			} else {
				Err(Unsupported("an `if` arm that shares work between its own reads needs statements, and a GLSL `?:` holds only an expression"))
			}
		}
		Op(node) => Glsl.render_op(node.op, node.args, node.ty, scope)
	}

	render_op : Code.Op, List(Code.Tree), Code.Ty, Scope -> Try(Str, Error)
	render_op = |op, args, ty, scope| match op {
		Lit(literal) => Glsl.literal(literal)
		Prim(prim) => Glsl.call(prim.owner, prim.method, args.map_try(|arg| Glsl.render(arg, scope))?)
		And(_) => Ok("(${Str.join_with(args.map_try(|arg| Glsl.render(arg, scope))?, " && ")})")
		Or(_) => Ok("(${Str.join_with(args.map_try(|arg| Glsl.render(arg, scope))?, " || ")})")
		Wrap(_) => {
			kind = Glsl.kind_for(ty)?
			match args {
				[Op({ op: Record(names), args: fields, ty: _ })] => {
					lanes = Glsl.lanes_of(kind)?
					rendered = lanes.map_try(
						|lane| match names.find_first_index(|name| name == lane) {
							Ok(at) => match fields.get(at) {
								Ok(field) => Glsl.render(field, scope)
								Err(_) => Err(BadType("a ${kind.to_str()} with no value for `${lane}`"))
							}
							Err(_) => Err(BadType("a ${kind.to_str()} is built from lanes named ${Str.join_with(lanes, ", ")}; this one has no `${lane}`"))
						},
					)?
					Ok("${kind.to_str()}(${Str.join_with(rendered, ", ")})")
				}
				[inner] => Glsl.render(inner, scope)
				_ => Err(BadType("a ${kind.to_str()} built from ${args.len().to_str()} values"))
			}
		}
		Record(_) => Err(BadType("`${ty.name()}` is a record, and GLSL 330 builds only its vectors from lanes"))
		Tuple => {
			kind = Glsl.kind_for(ty)?
			Ok("${kind.to_str()}(${Str.join_with(args.map_try(|arg| Glsl.render(arg, scope))?, ", ")})")
		}
		Unwrap => match args {
			[inner] => Glsl.render(inner, scope)
			_ => Err(Unsupported("an unwrap of more than one value"))
		}
		Field(name) => match args {
			[Param(_)] => Ok(name)
			[inner] => Ok("${Glsl.render(inner, scope)?}.${name}")
			_ => Err(Unsupported("a field read of more than one value"))
		}
		Index(position) => {
			lane = match position {
				0 => "x"
				1 => "y"
				2 => "z"
				3 => "w"
				_ => return Err(BadType("a GLSL vector has at most four lanes"))
			}
			match args {
				[inner] => Ok("${Glsl.render(inner, scope)?}.${lane}")
				_ => Err(Unsupported("a lane read of more than one value"))
			}
		}
		Switch(sw) => Glsl.conditional(sw, args, scope)
		Call(_) => Err(Unsupported("a shader cannot call a function that reaches itself, and GLSL 330 has no recursion"))
		Closure(_) => Err(Unsupported("a shader cannot contain a nested function"))
		Lambda(_) => Err(Unsupported("a shader cannot contain a nested function"))
		List => Err(Unsupported("GLSL 330 has no list; a fixed-lane vector is built from a tuple"))
		Item => Err(Unsupported("GLSL 330 has no list to read an element of"))
		Tag(name) => Err(Unsupported("GLSL 330 has no tag union, so `${name}` has no GLSL form"))
		Payload(name, _) => Err(Unsupported("GLSL 330 has no tag union, so `${name}` has no payload to read"))
		OptField(name) => Err(Unsupported("`${name}` may be absent, and GLSL 330 has no form for a field that is not there"))
		ForRange(_) | ForList(_) | Loop(_) => Err(Unsupported("this translator renders an expression and the declarations under it, and a loop is a statement it does not emit"))
		Crash => Err(Unsupported("`crash` cannot run on a GPU"))
		Derived(method, _) => Err(Unsupported("`${method}` is derived by the compiler and a shader owns no vehicle for it"))
	}

	## A switch on a `Bool` with one value is GLSL's `?:`. Any other switch is
	## on a tag union, a literal or a list, and GLSL 330 has none of those to
	## switch on.
	conditional : { arms : List({ key : Code.Key, region : Code.Region }), joins : List(Code.Region), outputs : List(Code.Ty) }, List(Code.Tree), Scope -> Try(Str, Error)
	conditional = |sw, args, scope| {
		shaped = match (sw.arms, sw.outputs, args) {
			([first, second], [_], [test, first_arm, second_arm]) =>
				if Glsl.selects(first.key) and !Glsl.selects(second.key) {
					Ok({ test, yes: first_arm, no: second_arm })
				} else if Glsl.selects(second.key) and !Glsl.selects(first.key) {
					Ok({ test, yes: second_arm, no: first_arm })
				} else {
					Err(Unsupported("GLSL 330 has no tag union to switch on; use `if`"))
				}
			_ => Err(Unsupported("GLSL 330 has no tag union to switch on; use `if`"))
		}
		parts = shaped?
		Ok("(${Glsl.render(parts.test, scope)?} ? ${Glsl.render(parts.yes, scope)?} : ${Glsl.render(parts.no, scope)?})")
	}

	## Whether an arm is the one a `True` test selects.
	selects : Code.Key -> Bool
	selects = |key| match key {
		Lit(Bool(flag)) => flag
		Tag(name) => name == "True"
		Lit(_) | Len(_) | AtLeast(_) | Default => Bool.False
	}

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

	## One call, by the owner and method a `Prim` carries.
	##
	## A builtin's owner names its type, `Num.F32` or `Num.I32`, so the owner
	## says which form an operator takes and the method picks the row. A `Glsl`
	## function arrives under its own type's name, because this library is a
	## package of its own and its bodies stay behind their names.
	call : Str, Str, List(Str) -> Try(Str, Error)
	call = |owner, method, values| {
		if owner == "Bool" {
			return match (method, values) {
				("not", [only]) => Ok("!(${only})")
				_ => Err(Unsupported("`Bool.${method}` has no GLSL form"))
			}
		}
		match Glsl.numeric_owner(owner) {
			Ok(whole) => match (method, values) {
				("negate", [only]) => Ok("-(${only})")
				(_, [lhs, rhs]) => match Glsl.operator(method, whole) {
					Ok(form) => Ok(form.over(lhs, rhs))
					Err(_) => Glsl.function(owner, method, values)
				}
				_ => Glsl.function(owner, method, values)
			}
			Err(_) => match (Glsl.broadcast(owner, method), values) {
				(Ok(symbol), [lhs, rhs]) => Ok("(${lhs} ${symbol} ${rhs})")
				_ => Glsl.function(owner, method, values)
			}
		}
	}

	## Whether an owner is a builtin number type, and if so whether it is a
	## whole-number one.
	numeric_owner : Str -> Try(Bool, [NotNumeric])
	numeric_owner = |owner| match owner {
		"Num.F32" | "Num.F64" | "Num.Dec" => Ok(Bool.False)
		"Num.I8" | "Num.U8" | "Num.I16" | "Num.U16" | "Num.I32" | "Num.U32" => Ok(Bool.True)
		"Num.I64" | "Num.U64" | "Num.I128" | "Num.U128" => Ok(Bool.True)
		_ => Err(NotNumeric)
	}

	## The builtin methods that are operators in GLSL. Two of them read
	## differently at a float, which is why the owner's kind is here beside the
	## method. Roc's `//` truncates toward zero and GLSL's `/` does that only at
	## an integer, and GLSL 330 spells the float remainder `mod` and keeps `%`
	## for integers. Both differences are silent in Roc: one computes another
	## number, the other does not compile on the driver.
	operator : Str, Bool -> Try(Form, [NotAnOperator])
	operator = |method, whole| match method {
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
		_ => Err(NotAnOperator)
	}

	## A `Glsl` vector's arithmetic is GLSL's own operators, and GLSL
	## broadcasts a scalar across a vector, which Roc has no operator for: the
	## right operand of `*` would have to be a vector too. `scale` and
	## `offset` are the methods that say it, and they render as the operator.
	broadcast : Str, Str -> Try(Str, [NotBroadcast])
	broadcast = |owner, method| {
		vector = owner == "Glsl.Vec2" or owner == "Glsl.Vec3" or owner == "Glsl.Vec4"
		if !vector {
			return Err(NotBroadcast)
		}
		match method {
			"plus" | "offset" => Ok("+")
			"times" | "scale" => Ok("*")
			_ => Err(NotBroadcast)
		}
	}

	## The calls a fragment shader may make, beside the GLSL function that
	## means the same. A builtin row is keyed by its method, under an owner
	## that is a number type; a `Glsl` row by its whole name.
	##
	## GLSL has more functions than these, and every one of them is missing
	## here because Roc's `F32` has no method that means it. A shader calls what
	## it can write, and anything else is named in the error, because a
	## translator that silently emits an unknown GLSL function moves the failure
	## to the driver.
	function : Str, Str, List(Str) -> Try(Str, Error)
	function = |owner, method, values| {
		builtin = ["sin", "cos", "tan", "asin", "acos", "atan", "sqrt", "abs", "min", "max", "pow"]
		numeric = Glsl.numeric_owner(owner).is_ok()
		name =
			if numeric and builtin.contains(method) {
				method
			} else if owner == "Glsl.Sampler" and method == "texture" {
				"texture"
			} else {
				return Err(Unsupported("`${owner}.${method}` is not one of the ${values.len().to_str()}-argument functions a fragment shader may call"))
			}
		Ok("${name}(${Str.join_with(values, ", ")})")
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
