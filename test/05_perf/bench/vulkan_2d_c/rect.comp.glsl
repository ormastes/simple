#version 450
// 2D rect fill into a u32 framebuffer storage buffer — compute-blits model,
// same shape as Simple's Engine2D vulkan backend kernels.
layout(local_size_x = 16, local_size_y = 16) in;
layout(set = 0, binding = 0) buffer Framebuffer { uint pixels[]; };
layout(push_constant) uniform Push {
    int x; int y; int w; int h; uint color; int fb_w; int fb_h;
} pc;
void main() {
    int gx = int(gl_GlobalInvocationID.x);
    int gy = int(gl_GlobalInvocationID.y);
    if (gx >= pc.w || gy >= pc.h) return;
    int px = pc.x + gx;
    int py = pc.y + gy;
    if (px >= pc.fb_w || py >= pc.fb_h) return;
    pixels[py * pc.fb_w + px] = pc.color;
}
