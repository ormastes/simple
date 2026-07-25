__kernel void simple_2d_fill_u32(__global uint* dst, uint value, uint count) {
    uint i = get_global_id(0);
    if (i >= count) { return; }
    dst[i] = value;
}
__kernel void simple_2d_copy_u32(__global const uint* src, __global uint* dst, uint count) {
    uint i = get_global_id(0);
    if (i >= count) { return; }
    dst[i] = src[i];
}
__kernel void simple_2d_alpha_u32(__global const uint* src, __global uint* dst, uint alpha, uint count) {
    uint i = get_global_id(0);
    if (i >= count) { return; }
    uint s = src[i];
    uint d = dst[i];
    uint inv = 255u - alpha;
    uint rb = (((s & 0x00ff00ffu) * alpha) + ((d & 0x00ff00ffu) * inv)) >> 8;
    uint g = (((s & 0x0000ff00u) * alpha) + ((d & 0x0000ff00u) * inv)) >> 8;
    dst[i] = 0xff000000u | (rb & 0x00ff00ffu) | (g & 0x0000ff00u);
}
__kernel void simple_2d_scroll_u32(__global const uint* src, __global uint* dst, uint width, uint height, int delta_y) {
    uint i = get_global_id(0);
    uint count = width * height;
    if (i >= count) { return; }
    uint x = i % width;
    uint y = i / width;
    int sy = (int)y - delta_y;
    if (sy < 0 || sy >= (int)height) { dst[i] = 0u; return; }
    dst[i] = src[(uint)sy * width + x];
}
