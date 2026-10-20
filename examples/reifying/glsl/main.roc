# What the whole feature is for: `post_process` below is a GLSL fragment
# shader, and it is written in Roc.
#
# Not in a shader DSL. In Roc: its numbers are `F32`, its arithmetic is Roc's
# arithmetic, its bindings are Roc bindings, and it is a function, so the
# `expect` further down calls it on real numbers and reads the colour it
# returns. Naming it where `Glsl.fragment_330` expects a `Code(f)` is
# what reifies it. The compiler describes the function during `roc build` and
# the translator turns that description into GLSL 330.
#
# The same shader written as a library DSL is in
# `examples/reifying/shaders-without-reifying/main.roc`, which is the control
# experiment: how far static dispatch reaches on its own. It defines
# `post_process` under the same name, and the two read almost alike. Then:
#
#   - Every value there is an `Expr` rather than an `F32`, so that
#     `post_process` builds a shader instead of being one. Nothing can call it,
#     test it, or run it on the CPU.
#   - Bindings do not survive evaluation, so `color`, one binding read four
#     times, is one GLSL local here and four texture fetches there.
#   - Nothing reads the parameter records, so the `in` and `uniform` lines are
#     hand-written there and derived from the shader's type here.
#
# It is the shader `roc-ray/examples/post_process` loads from
# `assets/post_process.fs`, written in Roc instead.

app [main!] { glsl: "package.roc" }

import glsl.Glsl
import glsl.Interp

## The varyings raylib's default vertex shader supplies. The names are its
## names, not ours: a fragment shader that renames them receives nothing.
Varyings : { fragTexCoord : Glsl.Vec2, fragColor : Glsl.Vec4 }

## What the application writes before the draws that read them. `texture0` is
## the unit raylib binds the render texture to.
Uniforms : { texture0 : Glsl.Sampler, time : F32 }

## Ripple the finished image horizontally, tint it by the vertex colour, and
## breathe a slow colour shift through it.
post_process : Varyings, Uniforms -> Glsl.Vec4
post_process = |frag, settings| {
	wave = (frag.fragTexCoord.y * 28.0 + settings.time * 2.0).sin() * 0.004
	shifted = Glsl.Vec2.({ x: frag.fragTexCoord.x + wave, y: frag.fragTexCoord.y })
	color = settings.texture0.texture(shifted) * frag.fragColor
	pulse = Glsl.Vec3.(
		{
			x: settings.time.sin(),
			y: (settings.time + 2.1).sin(),
			z: (settings.time + 4.2).sin(),
		},
	).scale(0.08).offset(0.92)
	Glsl.Vec4.({ r: color.r * pulse.x, g: color.g * pulse.y, b: color.b * pulse.z, a: color.a })
}

expected : Str
expected =
	\\#version 330
	\\in vec4 fragColor;
	\\in vec2 fragTexCoord;
	\\uniform sampler2D texture0;
	\\uniform float time;
	\\out vec4 finalColor;
	\\void main() {
	\\	vec4 n20 = (texture(texture0, vec2((fragTexCoord.x + (sin(((fragTexCoord.y * 28.0) + (time * 2.0))) * 0.004)), fragTexCoord.y)) * fragColor);
	\\	vec3 n36 = ((vec3(sin(time), sin((time + 2.1)), sin((time + 4.2))) * 0.08) + 0.92);
	\\	finalColor = vec4((n20.r * n36.x), (n20.g * n36.y), (n20.b * n36.z), n20.a);
	\\}

expect {
	match Glsl.fragment_330(post_process) {
		Ok(fragment) => fragment.source == expected
		Err(_) => Bool.False
	}
}

# The translator reports the interface, so a renamed input fails the build
# instead of failing the first `uniform_f32!` call.
expect {
	match Glsl.fragment_330(post_process) {
		Ok(fragment) => fragment.bindings.map(|binding| binding.name) == ["fragColor", "fragTexCoord", "texture0", "time"]
		Err(_) => Bool.False
	}
}

## A sampler that answers the same colour everywhere, so a test can call the
## shader without a GPU or an image.
flat : Glsl.Vec4 -> Glsl.Sampler
flat = |colour| Glsl.Sampler.({ at: |_uv| colour })

# Calling the shader is free, and it is the point of `Code(a)`: `post_process`
# is ordinary Roc, so an `expect` runs it on real numbers with no machinery.
expect {
	out = post_process(
		{
			fragTexCoord: Glsl.Vec2.({ x: 0.25, y: 0.5 }),
			fragColor: Glsl.Vec4.({ r: 1.0, g: 1.0, b: 1.0, a: 1.0 }),
		},
		{ texture0: flat(Glsl.Vec4.({ r: 0.2, g: 0.4, b: 0.6, a: 1.0 })), time: 1.0 },
	)
	out.a == 1.0
}

## Two operators GLSL spells differently at a float. Roc's `//` truncates
## toward zero, which GLSL's `/` does only at an integer, and GLSL 330 keeps
## `%` for integers and spells the float remainder `mod`. The translator asks
## the operand type, so both reach the shader meaning what Roc meant.
banded : Varyings, Uniforms -> Glsl.Vec4
banded = |frag, settings| {
	band = settings.time // 0.25
	phase = settings.time % 0.25
	Glsl.Vec4.({ r: band, g: phase, b: frag.fragTexCoord.x, a: 1.0 })
}

expect {
	match Glsl.fragment_330(banded) {
		Ok(fragment) =>
			fragment.source.contains("finalColor = vec4(trunc(time / 0.25), mod(time, 0.25), fragTexCoord.x, 1.0);")
		Err(_) => Bool.False
	}
}

# The same description on the CPU. This is a differential test: the emitter and
# the interpreter read one description, and the interpreter's answer is
# comparable with what Roc computes when it calls `banded` itself.
expect {
	frag = Interp.Value.Fields([
		{ name: "fragTexCoord", value: Interp.Value.Vector([0.25, 0.5]) },
		{ name: "fragColor", value: Interp.Value.Vector([1.0, 1.0, 1.0, 1.0]) },
	])
	settings = Interp.Value.Fields([{ name: "time", value: Interp.Value.Float(1.1) }])
	direct = banded(
		{
			fragTexCoord: Glsl.Vec2.({ x: 0.25, y: 0.5 }),
			fragColor: Glsl.Vec4.({ r: 1.0, g: 1.0, b: 1.0, a: 1.0 }),
		},
		{ texture0: flat(Glsl.Vec4.({ r: 0.0, g: 0.0, b: 0.0, a: 1.0 })), time: 1.1 },
	)
	close = |interpreted, computed| F64.abs(interpreted - computed.to_f64()) < 0.0001
	match Interp.run(Code.graph(banded), [frag, settings]) {
		Ok(Vector([r, g, b, a])) => close(r, direct.r) and close(g, direct.g) and close(b, direct.b) and close(a, direct.a)
		_ => Bool.False
	}
}

## A helper the shader calls twice. The translator reads the `inline` view, so
## each call is the helper's body in place and the shader needs no GLSL function.
ripple : F32, F32 -> F32
ripple = |y, t| (y * 28.0 + t * 2.0).sin() * 0.004

rippled : Varyings, Uniforms -> Glsl.Vec4
rippled = |frag, settings| {
	dx = ripple(frag.fragTexCoord.y, settings.time)
	dy = ripple(frag.fragTexCoord.x, settings.time)
	Glsl.Vec4.({ r: dx, g: dy, b: 0.0, a: 1.0 })
}

expect {
	match Glsl.fragment_330(rippled) {
		Ok(fragment) =>
			fragment.source.contains("sin(((fragTexCoord.y * 28.0) + n9)) * 0.004)") and fragment.source.contains("sin(((fragTexCoord.x * 28.0) + n9)) * 0.004)")
		Err(_) => Bool.False
	}
}

## GLSL 330 has no recursion, so a helper that reaches itself stays a call and
## is refused for that reason.
fade : F32, U8 -> F32
fade = |x, n| if n == 0 x else fade(x * 0.5, n - 1)

faded : Varyings, Uniforms -> Glsl.Vec4
faded = |_frag, settings| {
	v = fade(settings.time, 3)
	Glsl.Vec4.({ r: v, g: v, b: v, a: 1.0 })
}

expect {
	match Glsl.fragment_330(faded) {
		Ok(_) => Bool.False
		Err(Unsupported(message)) => message == "a shader cannot call a function that reaches itself, and GLSL 330 has no recursion"
		Err(_) => Bool.False
	}
}

## A shader the translator refuses: a fragment shader writes a colour, and this
## one writes one channel of it.
too_dim : Varyings, Uniforms -> F32
too_dim = |frag, settings|
	frag.fragColor.r * settings.time

# The refusal names the construct and what to write instead.
expect {
	match Glsl.fragment_330(too_dim) {
		Ok(_) => Bool.False
		Err(BadType(message)) => message == "a fragment shader must return Vec4; this one returns float"
		Err(_) => Bool.False
	}
}

main! = |_args| {
	match Glsl.fragment_330(post_process) {
		Ok(fragment) => echo!("${fragment.source}\n")
		Err(Unsupported(message)) => echo!("unsupported: ${message}\n")
		Err(BadType(message)) => echo!("bad type: ${message}\n")
		Err(BadInterface(message)) => echo!("bad interface: ${message}\n")
	}
	Ok({})
}
