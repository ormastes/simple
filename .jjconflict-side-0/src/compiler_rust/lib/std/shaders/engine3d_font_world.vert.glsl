#version 450

layout(location = 0) in vec3 in_position;
layout(location = 1) in vec2 in_uv;
layout(location = 2) in vec4 in_color_bgra;

layout(location = 0) out vec2 out_uv;
layout(location = 1) out vec4 out_color;

void main() {
    float vulkan_depth = in_position.z * 0.5 + 0.5;
    gl_Position = vec4(in_position.x, -in_position.y, vulkan_depth, 1.0);
    out_uv = in_uv;
    out_color = in_color_bgra.bgra;
}
