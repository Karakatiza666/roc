# The GLSL stage consumed as a package, the way an application outside this
# repository reaches it.
#
# The staged function has to be a top-level definition of the module that stages
# it, so the shader and the `Glsl.fragment_330` call live together here, which is
# also how `roc-ray/examples/post_process` would carry it.
app [main!] { pf: platform "../fx/platform/main.roc", glsl: "../../examples/reifying/glsl/package.roc" }

import pf.Stdout
import glsl.Glsl

Varyings : { fragTexCoord : Glsl.Vec2 }

Uniforms : { texture0 : Glsl.Sampler }

tint : Varyings, Uniforms -> Glsl.Vec4
tint = |frag, settings| settings.texture0.texture(frag.fragTexCoord)

fragment_source : Str
fragment_source = match Glsl.fragment_330(tint) {
	Ok(compiled) => compiled.source
	Err(Unsupported(message)) => crash "the shader is not GLSL: ${message}"
	Err(BadType(message)) => crash "the shader is not GLSL: ${message}"
	Err(BadInterface(message)) => crash "the shader is not GLSL: ${message}"
}

main! = || {
	Stdout.line!(fragment_source)
}
