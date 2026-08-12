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
    if (argc != 6) return 2;
    uint32_t width = (uint32_t)strtoul(argv[2], NULL, 10);
    uint32_t height = (uint32_t)strtoul(argv[3], NULL, 10);
    uint32_t samples = (uint32_t)strtoul(argv[4], NULL, 10);
    uint32_t bp = (uint32_t)strtoul(argv[5], NULL, 10);
    uint64_t full_pixels = (uint64_t)width * height;
    uint64_t active_pixels = full_pixels / 10000 * bp + (full_pixels % 10000) * bp / 10000;
    if (!width || !height || samples < 3 || !bp || bp > 10000 || !active_pixels) return 2;
    uint64_t bytes = full_pixels * 4;
    size_t spirv_size = 0; unsigned char *spirv = read_file(argv[1], &spirv_size);
    if (!spirv || !rt_vulkan_init()) return 3;
    int64_t buffer = rt_vulkan_alloc_buffer((int64_t)bytes, 0x83);
    int64_t shader = rt_vulkan_compile_spirv_raw((int64_t)(uintptr_t)spirv, (int64_t)spirv_size);
    int64_t pipe = rt_vulkan_create_compute_pipeline(shader, (int64_t)(uintptr_t)"main", 64);
    if (!buffer || !shader || !pipe) return 4;
    uint64_t *times = calloc(samples, sizeof(uint64_t));
    ClearPush pc = { .color = 0xff336699u, .width = (uint32_t)active_pixels, .height = 1 };
    for (uint32_t sample = 0; sample < samples + 1; sample++) {
        uint64_t start = now_ns();
        int64_t desc = rt_vulkan_create_descriptor_set(pipe);
        int64_t cmd = 0, fence = 0;
        int ok = desc > 0 && rt_vulkan_bind_buffer(desc, 0, buffer);
        if (ok) { cmd = rt_vulkan_begin_compute(); ok = cmd > 0; }
        if (ok) ok = rt_vulkan_bind_pipeline(cmd, pipe);
        if (ok) ok = rt_vulkan_bind_descriptors(cmd, desc);
        if (ok) ok = rt_vulkan_push_constants_raw(cmd, pipe, (int64_t)(uintptr_t)&pc, 64);
        if (ok) ok = rt_vulkan_dispatch(cmd, (int64_t)((active_pixels + 255) / 256), 1, 1);
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
    uint64_t readback_bytes = active_pixels * 4;
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
    for (uint64_t i = 0; i < active_pixels; i++) {
        if (readback[i] != pc.color) mismatch++;
        checksum ^= readback[i]; checksum *= 1099511628211ULL;
    }
    printf("engine2d_vulkan_schema=engine2d-vulkan-clear-v1\n");
    printf("engine2d_vulkan_width=%u\nengine2d_vulkan_height=%u\n", width, height);
    printf("engine2d_vulkan_active_basis_points=%u\n", bp);
    printf("engine2d_vulkan_active_pixels=%llu\n", (unsigned long long)active_pixels);
    printf("engine2d_vulkan_samples=%u\n", samples);
    printf("engine2d_vulkan_submit_fence_p50_ns=%llu\n", (unsigned long long)times[(samples-1)/2]);
    printf("engine2d_vulkan_submit_fence_p95_ns=%llu\n", (unsigned long long)times[p95i]);
    printf("engine2d_vulkan_within_80fps_budget=%s\n", times[p95i] <= 12500000 ? "true" : "false");
    printf("engine2d_vulkan_timed_readback_bytes=0\n");
    printf("engine2d_vulkan_evidence_readback_bytes=%llu\n", (unsigned long long)active_pixels * 4);
    printf("engine2d_vulkan_mismatch_count=%llu\n", (unsigned long long)mismatch);
    printf("engine2d_vulkan_checksum=%llu\n", (unsigned long long)checksum);
    printf("engine2d_vulkan_swapchain_presented=false\n");
    printf("engine2d_vulkan_dynamic_frame_80fps_proven=false\n");
    free(readback); free(times); free(spirv);
    rt_vulkan_destroy_pipeline(pipe); rt_vulkan_destroy_shader(shader);
    rt_vulkan_free_buffer(buffer); rt_vulkan_shutdown();
    return mismatch ? 7 : 0;
}
