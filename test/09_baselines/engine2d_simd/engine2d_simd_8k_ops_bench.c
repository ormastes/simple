#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/resource.h>

#include "runtime.h"

typedef struct {
    uint8_t kind;
    uint8_t flags;
    uint8_t reserved[6];
    int64_t len;
    int64_t cap;
    int64_t *data;
} BenchArray;

int64_t rt_array_len(SplArray *array) { return ((BenchArray *)array)->len; }
int64_t rt_array_data_ptr(SplArray *array) {
    return (int64_t)(uintptr_t)((BenchArray *)array)->data;
}

extern SplArray *rt_engine2d_simd_fill_span_u32(SplArray *, int64_t, int64_t, int64_t);
extern SplArray *rt_engine2d_simd_copy_span_u32(SplArray *, int64_t, SplArray *, int64_t, int64_t);
extern SplArray *rt_engine2d_simd_blend_span_u32(SplArray *, int64_t, SplArray *, int64_t, int64_t);
extern SplArray *rt_engine2d_simd_blend_const_span_u32(SplArray *, int64_t, int64_t, int64_t);
extern int64_t rt_simd_engine2d_neon_hits(void);
extern int64_t rt_simd_engine2d_neon_reset(void);

static uint64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

static int compare_u64(const void *a, const void *b) {
    uint64_t av = *(const uint64_t *)a, bv = *(const uint64_t *)b;
    return av < bv ? -1 : av > bv;
}

static uint64_t checksum(const int64_t *data, int64_t count) {
    uint64_t h = 1469598103934665603ULL;
    for (int64_t i = 0; i < count; i++) {
        h ^= (uint64_t)data[i];
        h *= 1099511628211ULL;
    }
    return h;
}

static void emit_times(const char *op, uint64_t *times, int samples,
                       int64_t pixels, uint64_t budget_ns) {
    qsort(times, (size_t)samples, sizeof(uint64_t), compare_u64);
    int p50_index = (samples - 1) / 2;
    int p95_index = (95 * samples + 99) / 100 - 1;
    if (p95_index >= samples) p95_index = samples - 1;
    printf("engine2d_8k_%s_p50_ns=%llu\n", op,
           (unsigned long long)times[p50_index]);
    printf("engine2d_8k_%s_p95_ns=%llu\n", op,
           (unsigned long long)times[p95_index]);
    printf("engine2d_8k_%s_pixels_per_second_p50=%llu\n", op,
           (unsigned long long)((uint64_t)pixels * 1000000000ULL /
                                (times[p50_index] ? times[p50_index] : 1)));
    printf("engine2d_8k_%s_within_80fps_single_op_budget=%s\n", op,
           times[p95_index] <= budget_ns ? "true" : "false");
}

int main(int argc, char **argv) {
    int64_t width = argc > 1 ? atoll(argv[1]) : 7680;
    int64_t height = argc > 2 ? atoll(argv[2]) : 4320;
    int samples = argc > 3 ? atoi(argv[3]) : 7;
    const char *mode = argc > 4 ? argv[4] : "native";
    int64_t active_basis_points = argc > 5 ? atoll(argv[5]) : 10000;
    if (width <= 0 || height <= 0 || samples < 3 || width > INT64_MAX / height)
        return 2;
    if (active_basis_points <= 0 || active_basis_points > 10000) return 2;
    int64_t pixels = width * height;
    int64_t active_pixels = pixels / 10000 * active_basis_points;
    active_pixels += (pixels % 10000) * active_basis_points / 10000;
    if (active_pixels < 1) active_pixels = 1;
    if ((uint64_t)pixels > SIZE_MAX / sizeof(int64_t)) return 2;
    size_t bytes = (size_t)pixels * sizeof(int64_t);
    int64_t *dst = (int64_t *)malloc(bytes);
    int64_t *src = (int64_t *)malloc(bytes);
    uint64_t *fill_ns = (uint64_t *)calloc((size_t)samples, sizeof(uint64_t));
    uint64_t *copy_ns = (uint64_t *)calloc((size_t)samples, sizeof(uint64_t));
    uint64_t *blend_ns = (uint64_t *)calloc((size_t)samples, sizeof(uint64_t));
    uint64_t *blend_const_ns = (uint64_t *)calloc((size_t)samples, sizeof(uint64_t));
    if (!dst || !src || !fill_ns || !copy_ns || !blend_ns || !blend_const_ns) return 3;
    for (int64_t i = 0; i < pixels; i++) {
        uint32_t sa = (uint32_t)((i * 37) & 255);
        uint32_t sp = (sa << 24) | ((uint32_t)(i * 13) & 0x00ffffffu);
        src[i] = (int64_t)((uint64_t)sp << 3);
        dst[i] = (int64_t)((uint64_t)0xff102030u << 3);
    }
    BenchArray dst_array = {0, 0, {0}, pixels, pixels, dst};
    BenchArray src_array = {0, 0, {0}, pixels, pixels, src};
    rt_simd_engine2d_neon_reset();
    for (int sample = 0; sample < samples; sample++) {
        uint64_t start = now_ns();
        rt_engine2d_simd_fill_span_u32((SplArray *)&dst_array, 0, active_pixels, 0xff102030u);
        fill_ns[sample] = now_ns() - start;

        start = now_ns();
        rt_engine2d_simd_copy_span_u32((SplArray *)&dst_array, 0,
                                      (SplArray *)&src_array, 0, active_pixels);
        copy_ns[sample] = now_ns() - start;

        rt_engine2d_simd_fill_span_u32((SplArray *)&dst_array, 0, active_pixels, 0xff102030u);
        start = now_ns();
        rt_engine2d_simd_blend_span_u32((SplArray *)&dst_array, 0,
                                       (SplArray *)&src_array, 0, active_pixels);
        blend_ns[sample] = now_ns() - start;

        rt_engine2d_simd_fill_span_u32((SplArray *)&dst_array, 0, active_pixels, 0xff102030u);
        start = now_ns();
        rt_engine2d_simd_blend_const_span_u32((SplArray *)&dst_array, 0,
                                             active_pixels, 0x804080c0u);
        blend_const_ns[sample] = now_ns() - start;
    }
    const uint64_t budget_ns = 12500000ULL;
    printf("engine2d_8k_schema=engine2d-simd-ops-v1\n");
    printf("engine2d_8k_execution_mode=%s\n", mode);
    printf("engine2d_8k_width=%lld\n", (long long)width);
    printf("engine2d_8k_height=%lld\n", (long long)height);
    printf("engine2d_8k_pixels=%lld\n", (long long)pixels);
    printf("engine2d_8k_active_pixels=%lld\n", (long long)active_pixels);
    printf("engine2d_8k_active_basis_points=%lld\n", (long long)active_basis_points);
    printf("engine2d_8k_storage_bytes_per_buffer=%llu\n", (unsigned long long)bytes);
    printf("engine2d_8k_samples=%d\n", samples);
    printf("engine2d_8k_frame_budget_ns=%llu\n", (unsigned long long)budget_ns);
    emit_times("fill", fill_ns, samples, active_pixels, budget_ns);
    emit_times("copy", copy_ns, samples, active_pixels, budget_ns);
    emit_times("blend", blend_ns, samples, active_pixels, budget_ns);
    emit_times("blend_const", blend_const_ns, samples, active_pixels, budget_ns);
    printf("engine2d_8k_native_simd_hits=%lld\n",
           (long long)rt_simd_engine2d_neon_hits());
    printf("engine2d_8k_checksum=%llu\n", (unsigned long long)checksum(dst, pixels));
    struct rusage usage;
    if (getrusage(RUSAGE_SELF, &usage) == 0)
        printf("engine2d_8k_max_rss_kib=%ld\n", usage.ru_maxrss);
    printf("engine2d_8k_full_dynamic_frame_80fps_proven=false\n");
    free(blend_const_ns); free(blend_ns); free(copy_ns); free(fill_ns);
    free(src); free(dst);
    return 0;
}
