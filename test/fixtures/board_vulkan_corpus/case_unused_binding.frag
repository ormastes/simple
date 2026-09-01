#version 450
layout(set = 0, binding = 0) uniform UnusedBlock {
    vec4 never_read;
} unused_ubo;
layout(location = 0) out vec4 out_color;
void main() {
    out_color = vec4(1.0, 0.0, 0.0, 1.0);
}
