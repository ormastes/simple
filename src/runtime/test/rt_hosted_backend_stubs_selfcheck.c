/*
 * Characterization selfcheck for the fixed-value rt_oneapi_* / rt_opengl_*
 * capability stubs shared by runtime_native.c and runtime_native_gpu_stub.c
 * through runtime_hosted_backend_stubs_impl.h.
 *
 * Links the seed-side includer (runtime_native_gpu_stub.c) as a separate
 * translation unit and pins every one of the 32 entry points to its fail-closed
 * constant: bool -> false, counts/availability -> 0, handles -> -3.
 *
 *   clang -O1 -I src/runtime src/runtime/test/rt_hosted_backend_stubs_selfcheck.c \
 *       src/runtime/runtime_native_gpu_stub.c -o sc && ./sc
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

bool rt_oneapi_init(void);
bool rt_oneapi_is_available(void);
int64_t rt_oneapi_device_count(void);
int64_t rt_oneapi_malloc_device(int64_t size);
bool rt_oneapi_free(int64_t ptr);
bool rt_oneapi_memset(int64_t ptr, int64_t value, int64_t size);
int64_t rt_oneapi_compile_spirv(int64_t bytes, int64_t size);
int64_t rt_oneapi_compile_opencl(int64_t source);
int64_t rt_oneapi_get_function(int64_t module, int64_t name);
int64_t rt_oneapi_create_queue(void);
bool rt_oneapi_destroy_queue(int64_t queue);
bool rt_oneapi_submit_kernel(int64_t queue, int64_t kernel, int64_t global_range,
                             int64_t local_range);
bool rt_oneapi_queue_wait(int64_t queue);
bool rt_oneapi_unload_module(int64_t module);

int64_t rt_opengl_init(int64_t width, int64_t height);
bool rt_opengl_destroy(int64_t ctx);
int64_t rt_opengl_is_available(void);
int64_t rt_opengl_create_fbo(int64_t ctx, int64_t width, int64_t height);
bool rt_opengl_destroy_fbo(int64_t ctx, int64_t fbo);
bool rt_opengl_bind_fbo(int64_t ctx, int64_t fbo);
bool rt_opengl_clear(int64_t ctx, int64_t color);
bool rt_opengl_draw_image(int64_t ctx, int64_t x, int64_t y, int64_t width, int64_t height,
                          int64_t pixels, int64_t image_width, int64_t image_height);
bool rt_opengl_clear_scissor(int64_t ctx);
bool rt_opengl_set_scissor(int64_t ctx, int64_t x, int64_t y, int64_t w, int64_t h);
bool rt_opengl_draw_rect(int64_t ctx, int64_t x, int64_t y, int64_t w, int64_t h,
                         int64_t color, int64_t filled);
bool rt_opengl_draw_rounded_rect(int64_t ctx, int64_t x, int64_t y, int64_t w, int64_t h,
                                 int64_t radius, int64_t color);
bool rt_opengl_draw_gradient_rect(int64_t ctx, int64_t x, int64_t y, int64_t w, int64_t h,
                                  int64_t top_color, int64_t bottom_color);
bool rt_opengl_draw_line(int64_t ctx, int64_t x1, int64_t y1, int64_t x2, int64_t y2,
                         int64_t color, int64_t thickness);
bool rt_opengl_draw_circle(int64_t ctx, int64_t cx, int64_t cy, int64_t radius,
                           int64_t color, int64_t filled);
bool rt_opengl_draw_triangle(int64_t ctx, int64_t x1, int64_t y1, int64_t x2, int64_t y2,
                             int64_t x3, int64_t y3, int64_t color);
bool rt_opengl_flush(int64_t ctx);
bool rt_opengl_read_pixels(int64_t ctx, int64_t pixels, int64_t width, int64_t height);

static int failures = 0;
static int checks = 0;

static void expect_false(const char *what, bool got)
{
    checks++;
    if (got) { printf("FAIL %s: expected false\n", what); failures++; }
}

static void expect_i64(const char *what, int64_t got, int64_t want)
{
    checks++;
    if (got != want) {
        printf("FAIL %s: got %lld want %lld\n", what, (long long)got, (long long)want);
        failures++;
    }
}

int main(void)
{
    /* Non-zero arguments everywhere: a stub must ignore them, never dereference. */
    const int64_t h = 0x7fff1234;

    expect_false("rt_oneapi_init", rt_oneapi_init());
    expect_false("rt_oneapi_is_available", rt_oneapi_is_available());
    expect_i64("rt_oneapi_device_count", rt_oneapi_device_count(), 0);
    expect_i64("rt_oneapi_malloc_device", rt_oneapi_malloc_device(4096), -3);
    expect_false("rt_oneapi_free", rt_oneapi_free(h));
    expect_false("rt_oneapi_memset", rt_oneapi_memset(h, 1, 16));
    expect_i64("rt_oneapi_compile_spirv", rt_oneapi_compile_spirv(h, 64), -3);
    expect_i64("rt_oneapi_compile_opencl", rt_oneapi_compile_opencl(h), -3);
    expect_i64("rt_oneapi_get_function", rt_oneapi_get_function(h, h), -3);
    expect_i64("rt_oneapi_create_queue", rt_oneapi_create_queue(), -3);
    expect_false("rt_oneapi_destroy_queue", rt_oneapi_destroy_queue(h));
    expect_false("rt_oneapi_submit_kernel", rt_oneapi_submit_kernel(h, h, 64, 8));
    expect_false("rt_oneapi_queue_wait", rt_oneapi_queue_wait(h));
    expect_false("rt_oneapi_unload_module", rt_oneapi_unload_module(h));

    expect_i64("rt_opengl_init", rt_opengl_init(640, 480), -3);
    expect_false("rt_opengl_destroy", rt_opengl_destroy(h));
    expect_i64("rt_opengl_is_available", rt_opengl_is_available(), 0);
    expect_i64("rt_opengl_create_fbo", rt_opengl_create_fbo(h, 64, 64), -3);
    expect_false("rt_opengl_destroy_fbo", rt_opengl_destroy_fbo(h, h));
    expect_false("rt_opengl_bind_fbo", rt_opengl_bind_fbo(h, h));
    expect_false("rt_opengl_clear", rt_opengl_clear(h, 0xff00ff));
    expect_false("rt_opengl_draw_image", rt_opengl_draw_image(h, 1, 2, 3, 4, h, 3, 4));
    expect_false("rt_opengl_clear_scissor", rt_opengl_clear_scissor(h));
    expect_false("rt_opengl_set_scissor", rt_opengl_set_scissor(h, 1, 2, 3, 4));
    expect_false("rt_opengl_draw_rect", rt_opengl_draw_rect(h, 1, 2, 3, 4, 5, 1));
    expect_false("rt_opengl_draw_rounded_rect", rt_opengl_draw_rounded_rect(h, 1, 2, 3, 4, 5, 6));
    expect_false("rt_opengl_draw_gradient_rect", rt_opengl_draw_gradient_rect(h, 1, 2, 3, 4, 5, 6));
    expect_false("rt_opengl_draw_line", rt_opengl_draw_line(h, 1, 2, 3, 4, 5, 6));
    expect_false("rt_opengl_draw_circle", rt_opengl_draw_circle(h, 1, 2, 3, 4, 1));
    expect_false("rt_opengl_draw_triangle", rt_opengl_draw_triangle(h, 1, 2, 3, 4, 5, 6, 7));
    expect_false("rt_opengl_flush", rt_opengl_flush(h));
    expect_false("rt_opengl_read_pixels", rt_opengl_read_pixels(h, h, 4, 4));

    if (checks != 32) { printf("FAIL expected 32 stub checks, ran %d\n", checks); failures++; }
    printf("hosted backend stubs selfcheck: %s (%d checks, %d failures)\n",
           failures == 0 ? "PASS" : "FAIL", checks, failures);
    return failures == 0 ? 0 : 1;
}
