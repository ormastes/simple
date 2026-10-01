#version 450
layout(location = 0) in vec2 v_uv;
layout(location = 0) out vec4 out_color;

// Two independent accumulations over disjoint conditions: a legal compiler
// is free to evaluate/reorder branch_a and branch_b in either order or fuse
// them, since they touch no shared state. This is the "control flow a
// compiler may legally reorder" hostile case: byte-identical SPIR-V is NOT
// guaranteed across implementations even though the observable result is.
void main() {
    float branch_a = 0.0;
    float branch_b = 0.0;
    if (v_uv.x > 0.5) {
        branch_a = v_uv.x * 2.0;
    } else {
        branch_a = v_uv.x * 0.5;
    }
    if (v_uv.y > 0.5) {
        branch_b = v_uv.y * 2.0;
    } else {
        branch_b = v_uv.y * 0.5;
    }
    out_color = vec4(branch_a, branch_b, 0.0, 1.0);
}
