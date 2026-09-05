#include <metal_stdlib>
using namespace metal;
kernel void simple_2d_fill_u32(device uint* dst [[buffer(0)]], constant uint& value [[buffer(1)]], constant uint& count [[buffer(2)]], uint gid [[thread_position_in_grid]]) {
    if (gid >= count) { return; }
    dst[gid] = value;
}
kernel void simple_2d_copy_u32(device const uint* src [[buffer(0)]], device uint* dst [[buffer(1)]], constant uint& count [[buffer(2)]], uint gid [[thread_position_in_grid]]) {
    if (gid >= count) { return; }
    dst[gid] = src[gid];
}
kernel void simple_2d_alpha_u32(device const uint* src [[buffer(0)]], device uint* dst [[buffer(1)]], constant uint& alpha [[buffer(2)]], constant uint& count [[buffer(3)]], uint gid [[thread_position_in_grid]]) {
    if (gid >= count) { return; }
    uint s = src[gid];
    uint d = dst[gid];
    uint inv = 255u - alpha;
    uint rb = (((s & 0x00ff00ffu) * alpha) + ((d & 0x00ff00ffu) * inv)) >> 8;
    uint g = (((s & 0x0000ff00u) * alpha) + ((d & 0x0000ff00u) * inv)) >> 8;
    dst[gid] = 0xff000000u | (rb & 0x00ff00ffu) | (g & 0x0000ff00u);
}
kernel void simple_2d_scroll_u32(device const uint* src [[buffer(0)]], device uint* dst [[buffer(1)]], constant uint& width [[buffer(2)]], constant uint& height [[buffer(3)]], constant int& delta_y [[buffer(4)]], uint gid [[thread_position_in_grid]]) {
    uint count = width * height;
    if (gid >= count) { return; }
    uint x = gid % width;
    uint y = gid / width;
    int sy = (int)y - delta_y;
    if (sy < 0 || sy >= (int)height) { dst[gid] = 0u; return; }
    dst[gid] = src[(uint)sy * width + x];
}
