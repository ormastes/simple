#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

extern int64_t rt_vulkan_init(void);
extern int64_t rt_vulkan_shutdown(void);
extern int64_t rt_vulkan_alloc_buffer(int64_t, int64_t);
extern int64_t rt_vulkan_free_buffer(int64_t);
extern int64_t rt_vulkan_compile_spirv_raw(int64_t, int64_t);
extern int64_t rt_vulkan_destroy_shader(int64_t);
extern int64_t rt_vulkan_create_compute_pipeline(int64_t, int64_t, int64_t);
extern int64_t rt_vulkan_destroy_pipeline(int64_t);
extern int64_t rt_vulkan_create_descriptor_set(int64_t);
extern int64_t rt_vulkan_bind_buffer(int64_t, int64_t, int64_t);
extern int64_t rt_vulkan_destroy_descriptor_set(int64_t);
extern int64_t rt_vulkan_begin_compute(void);
extern int64_t rt_vulkan_bind_pipeline(int64_t, int64_t);
extern int64_t rt_vulkan_bind_descriptors(int64_t, int64_t);
extern int64_t rt_vulkan_push_constants_raw(int64_t, int64_t, int64_t, int64_t);
extern int64_t rt_vulkan_dispatch(int64_t, int64_t, int64_t, int64_t);
extern int64_t rt_vulkan_end_compute(int64_t);
extern int64_t rt_vulkan_submit_and_wait_fence(int64_t);
extern int64_t rt_vulkan_wait_fence(int64_t, int64_t);
extern int64_t rt_vulkan_destroy_fence(int64_t);
extern int64_t rt_vulkan_copy_from_buffer_raw(int64_t, int64_t, int64_t, int64_t);

typedef struct { uint32_t color, width, height, reserved[13]; } ClearPush;
typedef struct {
    int32_t x, y, width, height;
    uint32_t color;
    int32_t fb_width, fb_height, clip_x, clip_y, clip_width, clip_height,
            clip_enabled, reserved[4];
} RectPush;

static uint64_t now_ns(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * 1000000000ULL + (uint64_t)t.tv_nsec;
}
static int cmp_u64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t*)a, y = *(const uint64_t*)b;
    return x < y ? -1 : x > y;
}
static unsigned char *read_file(const char *path, size_t *size) {
    FILE *f = fopen(path, "rb"); if (!f) return NULL;
    fseek(f, 0, SEEK_END); long n = ftell(f); rewind(f);
    if (n <= 0) { fclose(f); return NULL; }
    unsigned char *p = malloc((size_t)n);
    if (!p || fread(p, 1, (size_t)n, f) != (size_t)n) { free(p); p = NULL; }
    fclose(f); *size = (size_t)n; return p;
}

int main(int argc, char **argv) {
    if (argc != 6 && argc != 8) return 2;
    uint32_t width = (uint32_t)strtoul(argv[2], NULL, 10);
    uint32_t height = (uint32_t)strtoul(argv[3], NULL, 10);
    uint32_t samples = (uint32_t)strtoul(argv[4], NULL, 10);
    uint32_t bp = (uint32_t)strtoul(argv[5], NULL, 10);
    int rect_mode = argc == 8;
    uint32_t requested_rects = rect_mode ? (uint32_t)strtoul(argv[7], NULL, 10) : 0;
    uint64_t full_pixels = (uint64_t)width * height;
    uint64_t active_pixels = full_pixels / 10000 * bp + (full_pixels % 10000) * bp / 10000;
    if (!width || !height || samples < 3 || !bp || bp > 10000 || !active_pixels ||
            (rect_mode && (!requested_rects || requested_rects > 4096))) return 2;
    uint64_t bytes = full_pixels * 4;
    size_t spirv_size = 0; unsigned char *spirv = read_file(argv[1], &spirv_size);
    if (!spirv || !rt_vulkan_init()) return 3;
    int64_t buffer = rt_vulkan_alloc_buffer((int64_t)bytes, 0x83);
    int64_t shader = rt_vulkan_compile_spirv_raw((int64_t)(uintptr_t)spirv, (int64_t)spirv_size);
    int64_t pipe = rt_vulkan_create_compute_pipeline(shader, (int64_t)(uintptr_t)"main", 64);
    if (!buffer || !shader || !pipe) return 4;
    int64_t rect_shader = 0, rect_pipe = 0;
    if (rect_mode) {
        size_t rect_spirv_size = 0;
        unsigned char *rect_spirv = read_file(argv[6], &rect_spirv_size);
        if (!rect_spirv) return 4;
        rect_shader = rt_vulkan_compile_spirv_raw(
            (int64_t)(uintptr_t)rect_spirv, (int64_t)rect_spirv_size);
        rect_pipe = rt_vulkan_create_compute_pipeline(
            rect_shader, (int64_t)(uintptr_t)"main", 64);
        free(rect_spirv);
        if (!rect_shader || !rect_pipe) return 4;
    }
    uint64_t *times = calloc(samples, sizeof(uint64_t));
    ClearPush pc = { .color = 0xff336699u, .width = (uint32_t)active_pixels, .height = 1 };
    if (rect_mode) {
        /* Seed retained pixels once; timed frames update only active damage. */
        pc.color = 0xff101010u; pc.width = width; pc.height = height;
        int64_t desc = rt_vulkan_create_descriptor_set(pipe);
        int64_t cmd = rt_vulkan_begin_compute();
        int ok = desc > 0 && cmd > 0 && rt_vulkan_bind_buffer(desc, 0, buffer) &&
            rt_vulkan_bind_pipeline(cmd, pipe) && rt_vulkan_bind_descriptors(cmd, desc) &&
            rt_vulkan_push_constants_raw(cmd, pipe, (int64_t)(uintptr_t)&pc, 64) &&
            rt_vulkan_dispatch(cmd, (int64_t)((full_pixels + 255) / 256), 1, 1) &&
            rt_vulkan_end_compute(cmd);
        int64_t fence = ok ? rt_vulkan_submit_and_wait_fence(cmd) : 0;
        ok = fence > 0 && rt_vulkan_wait_fence(fence, 0);
        if (fence > 0) ok = rt_vulkan_destroy_fence(fence) && ok;
        ok = rt_vulkan_destroy_descriptor_set(desc) && ok;
        if (!ok) return 4;
    } else {
        pc.color = 0xff336699u;
    }
    for (uint32_t sample = 0; sample < samples + 1; sample++) {
        uint64_t start = now_ns();
        int64_t active_pipe = rect_mode ? rect_pipe : pipe;
        int64_t desc = rt_vulkan_create_descriptor_set(active_pipe);
        int64_t cmd = 0, fence = 0;
        int ok = desc > 0 && rt_vulkan_bind_buffer(desc, 0, buffer);
        if (ok) { cmd = rt_vulkan_begin_compute(); ok = cmd > 0; }
        if (ok) ok = rt_vulkan_bind_pipeline(cmd, active_pipe);
        if (ok) ok = rt_vulkan_bind_descriptors(cmd, desc);
        if (rect_mode) {
            uint64_t full_rows = active_pixels / width;
            uint32_t tail = (uint32_t)(active_pixels % width);
            uint32_t rects = requested_rects;
            if (full_rows && rects > full_rows) rects = (uint32_t)full_rows;
            if (!full_rows) rects = 0;
            uint64_t row = 0;
            for (uint32_t r = 0; ok && r < rects; r++) {
                uint64_t remaining = full_rows - row;
                uint32_t rh = (uint32_t)((remaining + (rects - r) - 1) / (rects - r));
                RectPush rpc = { .x = 0, .y = (int32_t)row, .width = (int32_t)width,
                    .height = (int32_t)rh, .color = 0xffcc2222u,
                    .fb_width = (int32_t)width, .fb_height = (int32_t)height,
                    .clip_x = 0, .clip_y = 0, .clip_width = (int32_t)width,
                    .clip_height = (int32_t)height, .clip_enabled = 1 };
                ok = rt_vulkan_push_constants_raw(cmd, rect_pipe,
                    (int64_t)(uintptr_t)&rpc, 64) &&
                    rt_vulkan_dispatch(cmd, (width + 15) / 16, (rh + 15) / 16, 1);
                row += rh;
            }
            if (ok && tail) {
                RectPush rpc = { .x = 0, .y = (int32_t)full_rows, .width = (int32_t)tail,
                    .height = 1, .color = 0xffcc2222u,
                    .fb_width = (int32_t)width, .fb_height = (int32_t)height,
                    .clip_x = 0, .clip_y = 0, .clip_width = (int32_t)width,
                    .clip_height = (int32_t)height, .clip_enabled = 1 };
                ok = rt_vulkan_push_constants_raw(cmd, rect_pipe,
                    (int64_t)(uintptr_t)&rpc, 64) &&
                    rt_vulkan_dispatch(cmd, (tail + 15) / 16, 1, 1);
            }
        } else {
            if (ok) ok = rt_vulkan_push_constants_raw(cmd, pipe, (int64_t)(uintptr_t)&pc, 64);
            if (ok) ok = rt_vulkan_dispatch(cmd, (int64_t)((active_pixels + 255) / 256), 1, 1);
        }
        if (ok) ok = rt_vulkan_end_compute(cmd);
        if (ok) { fence = rt_vulkan_submit_and_wait_fence(cmd); ok = fence > 0; }
        if (ok) ok = rt_vulkan_wait_fence(fence, 0);
        if (fence > 0) ok = rt_vulkan_destroy_fence(fence) && ok;
        ok = rt_vulkan_destroy_descriptor_set(desc) && ok;
        if (!ok) return 5;
        if (sample) times[sample - 1] = now_ns() - start;
    }
    qsort(times, samples, sizeof(uint64_t), cmp_u64);
    uint32_t p95i = (95 * samples + 99) / 100 - 1; if (p95i >= samples) p95i = samples - 1;
    uint64_t evidence_pixels = rect_mode ? full_pixels : active_pixels;
    uint64_t readback_bytes = evidence_pixels * 4;
    uint32_t *readback = malloc((size_t)readback_bytes);
    if (!readback) return 6;
    uint64_t copied = 0;
    while (copied < readback_bytes) {
        uint64_t chunk = readback_bytes - copied;
        if (chunk > 64ULL * 1024 * 1024) chunk = 64ULL * 1024 * 1024;
        if (!rt_vulkan_copy_from_buffer_raw(
                (int64_t)(uintptr_t)((unsigned char*)readback + copied),
                (int64_t)chunk, buffer, (int64_t)copied)) return 6;
        copied += chunk;
    }
    uint64_t mismatch = 0, checksum = 1469598103934665603ULL;
    for (uint64_t i = 0; i < evidence_pixels; i++) {
        uint32_t expected = rect_mode ?
            (i < active_pixels ? 0xffcc2222u : 0xff101010u) : pc.color;
        if (readback[i] != expected) mismatch++;
        checksum ^= readback[i]; checksum *= 1099511628211ULL;
    }
    printf("engine2d_vulkan_schema=engine2d-vulkan-primitive-v2\n");
    printf("engine2d_vulkan_width=%u\nengine2d_vulkan_height=%u\n", width, height);
    printf("engine2d_vulkan_active_basis_points=%u\n", bp);
    printf("engine2d_vulkan_active_pixels=%llu\n", (unsigned long long)active_pixels);
    printf("engine2d_vulkan_operation=%s\n", rect_mode ? "rect_filled_batched" : "clear");
    printf("engine2d_vulkan_requested_rect_count=%u\n", requested_rects);
    printf("engine2d_vulkan_samples=%u\n", samples);
    printf("engine2d_vulkan_submit_fence_p50_ns=%llu\n", (unsigned long long)times[(samples-1)/2]);
    printf("engine2d_vulkan_submit_fence_p95_ns=%llu\n", (unsigned long long)times[p95i]);
    printf("engine2d_vulkan_within_80fps_budget=%s\n", times[p95i] <= 12500000 ? "true" : "false");
    printf("engine2d_vulkan_timed_readback_bytes=0\n");
    printf("engine2d_vulkan_evidence_readback_bytes=%llu\n", (unsigned long long)readback_bytes);
    printf("engine2d_vulkan_mismatch_count=%llu\n", (unsigned long long)mismatch);
    printf("engine2d_vulkan_checksum=%llu\n", (unsigned long long)checksum);
    printf("engine2d_vulkan_swapchain_presented=false\n");
    printf("engine2d_vulkan_dynamic_frame_80fps_proven=false\n");
    free(readback); free(times); free(spirv);
    if (rect_pipe) rt_vulkan_destroy_pipeline(rect_pipe);
    if (rect_shader) rt_vulkan_destroy_shader(rect_shader);
    rt_vulkan_destroy_pipeline(pipe); rt_vulkan_destroy_shader(shader);
    rt_vulkan_free_buffer(buffer); rt_vulkan_shutdown();
    return mismatch ? 7 : 0;
}
