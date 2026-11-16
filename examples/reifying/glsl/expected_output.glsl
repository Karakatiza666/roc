#version 330
in vec4 fragColor;
in vec2 fragTexCoord;
uniform sampler2D texture0;
uniform float time;
out vec4 finalColor;
void main() {
	vec4 n20 = (texture(texture0, vec2((fragTexCoord.x + (sin(((fragTexCoord.y * 28.0) + (time * 2.0))) * 0.004)), fragTexCoord.y)) * fragColor);
	vec3 n36 = ((vec3(sin(time), sin((time + 2.1)), sin((time + 4.2))) * 0.08) + 0.92);
	finalColor = vec4((n20.r * n36.x), (n20.g * n36.y), (n20.b * n36.z), n20.a);
}
