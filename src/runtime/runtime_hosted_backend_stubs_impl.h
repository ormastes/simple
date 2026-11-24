/* runtime_hosted_backend_stubs_impl.h -- fixed-value rt_oneapi_* / rt_opengl_*
 * capability stubs shared by runtime_native.c and runtime_native_gpu_stub.c.
 *
 * Not a public header: include it exactly once per translation unit, after
 * <stdint.h> and <stdbool.h>. Every definition here is a plain (non-weak,
 * ungated) external function, exactly as both includers defined them before
 * the bodies were shared; neither includer may be linked into the same image
 * as the other (runtime_native_gpu_stub.c exists only for the interpreter/seed
 * crate, which cannot compile all of runtime_native.c -- see its header).
 *
 * No real OpenGL or oneAPI/SYCL binding exists anywhere in this tree, so each
 * body is a fail-closed constant: bool -> false, counts -> 0, handles -> -3.
 * Pinned by src/runtime/test/rt_hosted_backend_stubs_selfcheck.c and
 * scripts/check/check-hosted-backend-stubs-selfcheck.shs.
 */
#ifndef SIMPLE_RUNTIME_HOSTED_BACKEND_STUBS_IMPL_H
#define SIMPLE_RUNTIME_HOSTED_BACKEND_STUBS_IMPL_H

/* oneAPI */
bool rt_oneapi_init(void) { return false; }
bool rt_oneapi_is_available(void) { return false; }
int64_t rt_oneapi_device_count(void) { return 0; }
int64_t rt_oneapi_malloc_device(int64_t size) { (void)size; return -3; }
bool rt_oneapi_free(int64_t ptr) { (void)ptr; return false; }
bool rt_oneapi_memset(int64_t ptr, int64_t value, int64_t size) {
    (void)ptr; (void)value; (void)size;
    return false;
}
int64_t rt_oneapi_compile_spirv(int64_t bytes, int64_t size) {
    (void)bytes; (void)size;
    return -3;
}
int64_t rt_oneapi_compile_opencl(int64_t source) { (void)source; return -3; }
int64_t rt_oneapi_get_function(int64_t module, int64_t name) {
    (void)module; (void)name;
    return -3;
}
int64_t rt_oneapi_create_queue(void) { return -3; }
bool rt_oneapi_destroy_queue(int64_t queue) { (void)queue; return false; }
bool rt_oneapi_submit_kernel(int64_t queue, int64_t kernel,
                              int64_t global_range, int64_t local_range) {
    (void)queue; (void)kernel; (void)global_range; (void)local_range;
    return false;
}
bool rt_oneapi_queue_wait(int64_t queue) { (void)queue; return false; }
bool rt_oneapi_unload_module(int64_t module) { (void)module; return false; }

/* OpenGL */
int64_t rt_opengl_init(int64_t width, int64_t height) {
    (void)width; (void)height;
    return -3;
}
bool rt_opengl_destroy(int64_t ctx) { (void)ctx; return false; }
int64_t rt_opengl_is_available(void) { return 0; }
int64_t rt_opengl_create_fbo(int64_t ctx, int64_t width, int64_t height) {
    (void)ctx; (void)width; (void)height;
    return -3;
}
bool rt_opengl_destroy_fbo(int64_t ctx, int64_t fbo) {
    (void)ctx; (void)fbo;
    return false;
}
bool rt_opengl_bind_fbo(int64_t ctx, int64_t fbo) {
    (void)ctx; (void)fbo;
    return false;
}
bool rt_opengl_clear(int64_t ctx, int64_t color) {
    (void)ctx; (void)color;
    return false;
}
bool rt_opengl_draw_image(int64_t ctx, int64_t x, int64_t y, int64_t width,
                          int64_t height, int64_t pixels, int64_t image_width,
                          int64_t image_height) {
    (void)ctx; (void)x; (void)y; (void)width; (void)height;
    (void)pixels; (void)image_width; (void)image_height;
    return false;
}
bool rt_opengl_clear_scissor(int64_t ctx) { (void)ctx; return false; }
bool rt_opengl_set_scissor(int64_t ctx, int64_t x, int64_t y, int64_t w, int64_t h) {
    (void)ctx; (void)x; (void)y; (void)w; (void)h;
    return false;
}
bool rt_opengl_draw_rect(int64_t ctx, int64_t x, int64_t y, int64_t w, int64_t h,
                         int64_t color, int64_t filled) {
    (void)ctx; (void)x; (void)y; (void)w; (void)h; (void)color; (void)filled;
    return false;
}
bool rt_opengl_draw_rounded_rect(int64_t ctx, int64_t x, int64_t y, int64_t w, int64_t h,
                                 int64_t radius, int64_t color) {
    (void)ctx; (void)x; (void)y; (void)w; (void)h; (void)radius; (void)color;
    return false;
}
bool rt_opengl_draw_gradient_rect(int64_t ctx, int64_t x, int64_t y, int64_t w, int64_t h,
                                  int64_t top_color, int64_t bottom_color) {
    (void)ctx; (void)x; (void)y; (void)w; (void)h; (void)top_color; (void)bottom_color;
    return false;
}
bool rt_opengl_draw_line(int64_t ctx, int64_t x1, int64_t y1, int64_t x2, int64_t y2,
                         int64_t color, int64_t thickness) {
    (void)ctx; (void)x1; (void)y1; (void)x2; (void)y2; (void)color; (void)thickness;
    return false;
}
bool rt_opengl_draw_circle(int64_t ctx, int64_t cx, int64_t cy, int64_t radius,
                           int64_t color, int64_t filled) {
    (void)ctx; (void)cx; (void)cy; (void)radius; (void)color; (void)filled;
    return false;
}
bool rt_opengl_draw_triangle(int64_t ctx, int64_t x1, int64_t y1, int64_t x2, int64_t y2,
                             int64_t x3, int64_t y3, int64_t color) {
    (void)ctx; (void)x1; (void)y1; (void)x2; (void)y2; (void)x3; (void)y3; (void)color;
    return false;
}
bool rt_opengl_flush(int64_t ctx) { (void)ctx; return false; }
bool rt_opengl_read_pixels(int64_t ctx, int64_t pixels, int64_t width, int64_t height) {
    (void)ctx; (void)pixels; (void)width; (void)height;
    return false;
}

#endif /* SIMPLE_RUNTIME_HOSTED_BACKEND_STUBS_IMPL_H */
