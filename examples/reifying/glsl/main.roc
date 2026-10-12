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

import Glsl
import Interp

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
	\\uniform float time;
	\\uniform sampler2D texture0;
	\\out vec4 finalColor;
	\\void main() {
	\\	float wave = (sin(((fragTexCoord.y * 28.0) + (time * 2.0))) * 0.004);
	\\	vec2 shifted = vec2((fragTexCoord.x + wave), fragTexCoord.y);
	\\	vec4 color = (texture(texture0, shifted) * fragColor);
	\\	vec3 pulse = ((vec3(sin(time), sin((time + 2.1)), sin((time + 4.2))) * 0.08) + 0.92);
	\\	finalColor = vec4((color.r * pulse.x), (color.g * pulse.y), (color.b * pulse.z), color.a);
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
		Ok(fragment) => fragment.bindings.map(|binding| binding.name) == ["fragColor", "fragTexCoord", "time", "texture0"]
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

## The description the translator reads, opened here so the interpreter can run
## the same IR the emitter compiled.
described : Code.Ir
described = Code.ir(post_process)

# The same IR on the CPU. This is a differential test: the emitter and
# the interpreter read one description, and the interpreter's answer for `wave`
# is comparable with what Roc computes for the same arithmetic.
expect {
	scope = [
		{ name: "fragTexCoord", value: Interp.Value.Vector([0.25, 0.5]) },
		{ name: "time", value: Interp.Value.Float(1.0) },
	]
	direct = F64.sin(0.5 * 28.0 + 1.0 * 2.0) * 0.004
	match described {
		Lambda(_, Let(_, bound, _, _), _) => match Interp.eval(bound, scope) {
			Ok(Float(interpreted)) => F64.abs(interpreted - direct) < 0.000001
			_ => Bool.False
		}
		_ => Bool.False
	}
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
			fragment.source.contains("float band = trunc(time / 0.25);")
				and fragment.source.contains("float phase = mod(time, 0.25);")
		Err(_) => Bool.False
	}
}

## A shader the translator refuses: a fragment shader writes a colour, and this
## one writes one channel of it.
too_dim : Varyings, Uniforms -> F32
too_dim = |frag, settings|
	frag.fragColor.r * settings.time

# Every node carries where it was written, so a refusal names the module and
# the line the author has to look at and not only the construct. The line is
# `too_dim`'s body, as this file numbers it.
expect {
	match Glsl.fragment_330(too_dim) {
		Ok(_) => Bool.False
		Err(BadType(message)) => message == "main:152:2: a fragment shader must return Vec4; this one returns float"
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
