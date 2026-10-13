# `post_process` of `main.roc`, refactored by hand: every local and both
# parameters renamed, the bindings in another order, and the result record's
# fields in another order. None of it changes what the function computes, so
# the translator gets the same description and writes the same shader, byte
# for byte, down to the names of its locals (`expected_output.glsl`).
#
# This is the claim of reification on the program a reader looks at first:
# a refactor that keeps the meaning keeps the output.

app [main!] { glsl: "package.roc" }

import glsl.Glsl
import "expected_output.glsl" as expected_output : Str

Varyings : { fragTexCoord : Glsl.Vec2, fragColor : Glsl.Vec4 }

Uniforms : { texture0 : Glsl.Sampler, time : F32 }

post_process : Varyings, Uniforms -> Glsl.Vec4
post_process = |varyings, uniforms| {
	breathe = Glsl.Vec3.(
		{
			x: uniforms.time.sin(),
			y: (uniforms.time + 2.1).sin(),
			z: (uniforms.time + 4.2).sin(),
		},
	).scale(0.08).offset(0.92)
	ripple = (varyings.fragTexCoord.y * 28.0 + uniforms.time * 2.0).sin() * 0.004
	uv = Glsl.Vec2.({ x: varyings.fragTexCoord.x + ripple, y: varyings.fragTexCoord.y })
	texel = uniforms.texture0.texture(uv) * varyings.fragColor
	Glsl.Vec4.({ a: texel.a, b: texel.b * breathe.z, g: texel.g * breathe.y, r: texel.r * breathe.x })
}

expect {
	match Glsl.fragment_330(post_process) {
		Ok(fragment) => "${fragment.source}\n" == expected_output
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
