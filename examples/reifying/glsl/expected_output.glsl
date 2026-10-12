#version 330
in vec4 fragColor;
in vec2 fragTexCoord;
uniform float time;
uniform sampler2D texture0;
out vec4 finalColor;
void main() {
	float wave = (sin(((fragTexCoord.y * 28.0) + (time * 2.0))) * 0.004);
	vec2 shifted = vec2((fragTexCoord.x + wave), fragTexCoord.y);
	vec4 color = (texture(texture0, shifted) * fragColor);
	vec3 pulse = ((vec3(sin(time), sin((time + 2.1)), sin((time + 4.2))) * 0.08) + 0.92);
	finalColor = vec4((color.r * pulse.x), (color.g * pulse.y), (color.b * pulse.z), color.a);
}
