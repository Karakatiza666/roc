#version 330
in vec4 fragColor;
in vec2 fragTexCoord;
uniform float time;
uniform sampler2D texture0;
out vec4 finalColor;
void main() {
	finalColor = vec4(((texture(texture0, vec2((fragTexCoord.x + (sin(((fragTexCoord.y * 28.0) + (time * 2.0))) * 0.004)), fragTexCoord.y)) * fragColor).r * ((vec3(sin(time), sin((time + 2.1)), sin((time + 4.2))) * 0.08) + 0.92).x), ((texture(texture0, vec2((fragTexCoord.x + (sin(((fragTexCoord.y * 28.0) + (time * 2.0))) * 0.004)), fragTexCoord.y)) * fragColor).g * ((vec3(sin(time), sin((time + 2.1)), sin((time + 4.2))) * 0.08) + 0.92).y), ((texture(texture0, vec2((fragTexCoord.x + (sin(((fragTexCoord.y * 28.0) + (time * 2.0))) * 0.004)), fragTexCoord.y)) * fragColor).b * ((vec3(sin(time), sin((time + 2.1)), sin((time + 4.2))) * 0.08) + 0.92).z), (texture(texture0, vec2((fragTexCoord.x + (sin(((fragTexCoord.y * 28.0) + (time * 2.0))) * 0.004)), fragTexCoord.y)) * fragColor).a);
}
