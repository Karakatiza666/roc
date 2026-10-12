# The same fragment shader as `../glsl/main.roc`, written as a library DSL
# instead of as Roc. It is the control experiment for
# `roc-reify-proposal.md`: how far static dispatch alone reaches, so that what
# `Code(a)` adds can be measured rather than asserted. Run it with
# `roc main.roc`; it prints the GLSL in `expected_output.glsl`.
#
# It works because Roc's arithmetic operators are method calls. `+` dispatches
# to `plus`, `*` to `times`, and a numeric literal to `from_numeral`, so a
# nominal type can implement all three and
#
#     frag.fragTexCoord.y() * 28.0 + settings.time * 2.0
#
# builds a syntax tree instead of computing a number.
#
# Read `post_process` below beside the `post_process` in `../glsl/main.roc`.
# Same name, same shader, written twice. What the DSL costs:
#
#   1. Bindings do not survive. `color` is bound once and emitted four times,
#      `pulse` once and three times, so the shader carries four texture fetches
#      and thirteen `sin` calls where the source writes one and four. A `let`
#      leaves no trace in a tree built by evaluation, and the loss compounds
#      with every binding.
#   2. This `post_process` is not the shader, it is a shader builder. Its
#      parameters are `Expr` rather than `F32`, so nothing can call it on real
#      numbers, run it on the CPU, or reach it from an `expect`.
#   3. Comparison and control flow stay closed to it. `is_gte` is required to
#      return a `Bool`, so `>=` cannot build a node, and `and`, `or`, `if` and
#      `match` are keywords that no method stands in for. `and` is not even a
#      legal method name. So a predicate is written in invented names,
#      `a.gte(b).both(c)`, and a conditional as `mix(a, b, step(x, y))`.
#   4. The interface is written twice. `../glsl/main.roc` declares the varyings
#      and the uniforms as the shader's two parameter records and the
#      translator reads the `in` and `uniform` lines off their types; here the
#      preamble and the `Var` names handed to `post_process` are two
#      hand-written lists, and nothing checks one against the other.

Expr := [
	Lit(F32),
	Var(Str),
	Bin(Str, Expr, Expr),
	Call(Str, List(Expr)),
	Lane(Expr, Str),
].{
	from_numeral : Numeral -> Try(Expr, [InvalidNumeral(Str)])
	from_numeral = |n| Ok(Expr.Lit(F32.from_numeral(n)?))

	plus : Expr, Expr -> Expr
	plus = |a, b| Expr.Bin("+", a, b)

	times : Expr, Expr -> Expr
	times = |a, b| Expr.Bin("*", a, b)

	sin : Expr -> Expr
	sin = |a| Expr.Call("sin", [a])

	to_glsl : Expr -> Str
	to_glsl = |e| match e {
		Expr.Lit(f) => Expr.float_str(f)
		Expr.Var(name) => name
		Expr.Bin(op, a, b) => "(${a.to_glsl()} ${op} ${b.to_glsl()})"
		Expr.Call(name, args) => "${name}(${Str.join_with(args.map(|x| x.to_glsl()), ", ")})"
		Expr.Lane(a, lane) => "${a.to_glsl()}.${lane}"
	}

	## GLSL reads a bare `2` as an `int`, so a float literal keeps its point.
	float_str : F32 -> Str
	float_str = |number| {
		rendered = number.to_str()
		if rendered.contains(".") or rendered.contains("e") {
			rendered
		} else {
			"${rendered}.0"
		}
	}
}

# A vector is one GLSL expression, not two or four scalars, so each lane is a
# method: field access is syntax and offers nothing to dispatch on.
Vec2 := Expr.{
	x : Vec2 -> Expr
	x = |Vec2.(e)| Expr.Lane(e, "x")

	y : Vec2 -> Expr
	y = |Vec2.(e)| Expr.Lane(e, "y")
}

Vec3 := Expr.{
	x : Vec3 -> Expr
	x = |Vec3.(e)| Expr.Lane(e, "x")

	y : Vec3 -> Expr
	y = |Vec3.(e)| Expr.Lane(e, "y")

	z : Vec3 -> Expr
	z = |Vec3.(e)| Expr.Lane(e, "z")

	scale : Vec3, Expr -> Vec3
	scale = |Vec3.(v), k| Vec3.(Expr.Bin("*", v, k))

	offset : Vec3, Expr -> Vec3
	offset = |Vec3.(v), k| Vec3.(Expr.Bin("+", v, k))
}

Vec4 := Expr.{
	r : Vec4 -> Expr
	r = |Vec4.(e)| Expr.Lane(e, "r")

	g : Vec4 -> Expr
	g = |Vec4.(e)| Expr.Lane(e, "g")

	b : Vec4 -> Expr
	b = |Vec4.(e)| Expr.Lane(e, "b")

	a : Vec4 -> Expr
	a = |Vec4.(e)| Expr.Lane(e, "a")

	times : Vec4, Vec4 -> Vec4
	times = |Vec4.(p), Vec4.(q)| Vec4.(Expr.Bin("*", p, q))

	to_glsl : Vec4 -> Str
	to_glsl = |Vec4.(e)| e.to_glsl()
}

## A texture the application binds, named as it names it.
Sampler := Str.{
	texture : Sampler, Vec2 -> Vec4
	texture = |Sampler.(unit), Vec2.(uv)| Vec4.(Expr.Call("texture", [Expr.Var(unit), uv]))
}

# The lanes are named, the way `Glsl.Vec2.({ x: ..., y: ... })` names them next
# door. A nominal type over `Expr` cannot be built from a record directly,
# because its backing type is the expression and not the lanes.
vec2 : { x : Expr, y : Expr } -> Vec2
vec2 = |lanes| Vec2.(Expr.Call("vec2", [lanes.x, lanes.y]))

vec3 : { x : Expr, y : Expr, z : Expr } -> Vec3
vec3 = |lanes| Vec3.(Expr.Call("vec3", [lanes.x, lanes.y, lanes.z]))

vec4 : { r : Expr, g : Expr, b : Expr, a : Expr } -> Vec4
vec4 = |lanes| Vec4.(Expr.Call("vec4", [lanes.r, lanes.g, lanes.b, lanes.a]))

Varyings : { fragTexCoord : Vec2, fragColor : Vec4 }

Uniforms : { texture0 : Sampler, time : Expr }

# The shader. Every operator here is a real Roc operator, and none of the
# values are numbers.
post_process : Varyings, Uniforms -> Vec4
post_process = |frag, settings| {
	wave = (frag.fragTexCoord.y() * 28.0 + settings.time * 2.0).sin() * 0.004
	shifted = vec2({ x: frag.fragTexCoord.x() + wave, y: frag.fragTexCoord.y() })
	color = settings.texture0.texture(shifted) * frag.fragColor
	pulse = vec3({
		x: settings.time.sin(),
		y: (settings.time + 2.1).sin(),
		z: (settings.time + 4.2).sin(),
	}).scale(0.08).offset(0.92)
	vec4({ r: color.r() * pulse.x(), g: color.g() * pulse.y(), b: color.b() * pulse.z(), a: color.a() })
}

fragment_source : Str
fragment_source = {
	body = post_process(
		{ fragTexCoord: Vec2.(Expr.Var("fragTexCoord")), fragColor: Vec4.(Expr.Var("fragColor")) },
		{ texture0: Sampler.("texture0"), time: Expr.Var("time") },
	)
	\\#version 330
	\\in vec4 fragColor;
	\\in vec2 fragTexCoord;
	\\uniform float time;
	\\uniform sampler2D texture0;
	\\out vec4 finalColor;
	\\void main() {
	\\	finalColor = ${body.to_glsl()};
	\\}
}

main! = |_args| {
	echo!("${fragment_source}\n")
	Ok({})
}
