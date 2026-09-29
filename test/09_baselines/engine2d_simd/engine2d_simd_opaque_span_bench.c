#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "runtime.h"

typedef struct { uint8_t kind, flags, reserved[6]; int64_t len, cap; int64_t *data; } TestArray;
int64_t rt_array_len(SplArray *a) { return ((TestArray *)a)->len; }
int64_t rt_array_data_ptr(SplArray *a) { return (int64_t)(uintptr_t)((TestArray *)a)->data; }
SplArray *rt_array_new_uninit(int64_t n) { (void)n; return NULL; }
int64_t rt_array_header_ptr(SplArray *a) { return (int64_t)(uintptr_t)a; }
int8_t rt_array_set_len_known(int64_t p, int64_t n) { (void)p; (void)n; return 0; }
extern SplArray *rt_engine2d_simd_blend_span_u32(SplArray *, int64_t, SplArray *, int64_t, int64_t);
extern SplArray *rt_engine2d_simd_blend_const_span_u32(SplArray *, int64_t, int64_t, int64_t);
extern SplArray *rt_engine2d_simd_fill_span_u32(SplArray *, int64_t, int64_t, int64_t);
extern SplArray *rt_engine2d_simd_copy_span_u32(SplArray *, int64_t, SplArray *, int64_t, int64_t);
extern int64_t rt_simd_engine2d_neon_hits(void);
extern int64_t rt_simd_engine2d_neon_reset(void);

static uint64_t now_ns(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * 1000000000ull + (uint64_t)t.tv_nsec;
}
static int cmp(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return x > y ? 1 : x < y ? -1 : 0;
}
__attribute__((noinline)) static uint32_t scalar_blend(uint32_t s, uint32_t d) {
    uint32_t sa = s >> 24;
    if (sa == 255) return s;
    if (sa == 0) return d;
    uint32_t dw = ((d >> 24) * (255 - sa)) / 255;
    uint32_t oa = sa + dw;
    uint32_t r = ((((s >> 16) & 255) * sa) + (((d >> 16) & 255) * dw)) / oa;
    uint32_t g = ((((s >> 8) & 255) * sa) + (((d >> 8) & 255) * dw)) / oa;
    uint32_t b = (((s & 255) * sa) + ((d & 255) * dw)) / oa;
    return (oa << 24) | (r << 16) | (g << 8) | b;
}
__attribute__((noinline)) static void scalar_fill(int64_t *dst, int n, uint32_t color) {
    int64_t boxed = (int64_t)((uint64_t)color << 3);
    for (int i = 0; i < n; i++) dst[i] = boxed;
}
__attribute__((noinline)) static void scalar_copy(int64_t *dst, const int64_t *src, int n) {
    for (int i = 0; i < n; i++) dst[i] = src[i];
}
int main(void) {
    enum { N = 7680, FRAMES = 500 };
    int64_t *dst = calloc(N, sizeof(int64_t)), *src = calloc(N, sizeof(int64_t));
    int64_t *scalar = calloc(N, sizeof(int64_t)), *scalar_const = calloc(N, sizeof(int64_t));
    int64_t *fill_dst = calloc(N, sizeof(int64_t)), *fill_scalar = calloc(N, sizeof(int64_t));
    int64_t *copy_dst = calloc(N, sizeof(int64_t)), *copy_scalar = calloc(N, sizeof(int64_t));
    int64_t *mixed_dst = calloc(N, sizeof(int64_t)), *mixed_src = calloc(N, sizeof(int64_t));
    int64_t *mixed_scalar = calloc(N, sizeof(int64_t));
    if (!dst || !src || !scalar || !scalar_const || !fill_dst || !fill_scalar || !copy_dst || !copy_scalar || !mixed_dst || !mixed_src || !mixed_scalar) return 2;
    for (int i = 0; i < N; i++) {
        src[i] = (int64_t)((uint64_t)(0xff000000u | ((uint32_t)i * 2654435761u & 0xffffffu)) << 3);
        uint32_t mixed_s = (((uint32_t)(i * 73 + 1) & 255u) << 24) | ((uint32_t)i * 2654435761u & 0xffffffu);
        uint32_t mixed_d = (((uint32_t)(i * 29 + 17) & 255u) << 24) | ((uint32_t)i * 2246822519u & 0xffffffu);
        mixed_src[i] = (int64_t)((uint64_t)mixed_s << 3);
        mixed_dst[i] = mixed_scalar[i] = (int64_t)((uint64_t)mixed_d << 3);
    }
    TestArray d = {0, 0, {0}, N, N, dst}, s = {0, 0, {0}, N, N, src};
    TestArray fd = {0, 0, {0}, N, N, fill_dst}, cd = {0, 0, {0}, N, N, copy_dst};
    TestArray md = {0, 0, {0}, N, N, mixed_dst}, ms = {0, 0, {0}, N, N, mixed_src};
    uint64_t vector_samples[FRAMES], scalar_samples[FRAMES], const_samples[FRAMES];
    uint64_t scalar_const_samples[FRAMES];
    uint64_t fill_samples[FRAMES], scalar_fill_samples[FRAMES];
    uint64_t copy_samples[FRAMES], scalar_copy_samples[FRAMES];
    uint64_t mixed_samples[FRAMES], scalar_mixed_samples[FRAMES];
    rt_simd_engine2d_neon_reset();
    for (int frame = 0; frame < FRAMES; frame++) {
        uint64_t started = now_ns();
        rt_engine2d_simd_blend_span_u32((SplArray *)&d, 0, (SplArray *)&s, 0, N);
        vector_samples[frame] = now_ns() - started;
        started = now_ns();
        for (int i = 0; i < N; i++) {
            uint32_t sp = (uint32_t)((uint64_t)src[i] >> 3);
            uint32_t dp = (uint32_t)((uint64_t)scalar[i] >> 3);
            scalar[i] = (int64_t)((uint64_t)scalar_blend(sp, dp) << 3);
        }
        scalar_samples[frame] = now_ns() - started;
        started = now_ns();
        rt_engine2d_simd_blend_const_span_u32((SplArray *)&d, 0, N, 0xff556677);
        const_samples[frame] = now_ns() - started;
        started = now_ns();
        for (int i = 0; i < N; i++) {
            uint32_t dp = (uint32_t)((uint64_t)scalar_const[i] >> 3);
            scalar_const[i] = (int64_t)((uint64_t)scalar_blend(0xff556677u, dp) << 3);
        }
        scalar_const_samples[frame] = now_ns() - started;
        started = now_ns();
        rt_engine2d_simd_fill_span_u32((SplArray *)&fd, 0, N, 0xff123456);
        fill_samples[frame] = now_ns() - started;
        started = now_ns();
        scalar_fill(fill_scalar, N, 0xff123456u);
        scalar_fill_samples[frame] = now_ns() - started;
        started = now_ns();
        rt_engine2d_simd_copy_span_u32((SplArray *)&cd, 0, (SplArray *)&s, 0, N);
        copy_samples[frame] = now_ns() - started;
        started = now_ns();
        scalar_copy(copy_scalar, src, N);
        scalar_copy_samples[frame] = now_ns() - started;
        started = now_ns();
        rt_engine2d_simd_blend_span_u32((SplArray *)&md, 0, (SplArray *)&ms, 0, N);
        mixed_samples[frame] = now_ns() - started;
        started = now_ns();
        for (int i = 0; i < N; i++) {
            uint32_t sp = (uint32_t)((uint64_t)mixed_src[i] >> 3);
            uint32_t dp = (uint32_t)((uint64_t)mixed_scalar[i] >> 3);
            mixed_scalar[i] = (int64_t)((uint64_t)scalar_blend(sp, dp) << 3);
        }
        scalar_mixed_samples[frame] = now_ns() - started;
    }
    uint64_t mismatches = 0, checksum = 0, scalar_checksum = 0;
    for (int i = 0; i < N; i++) {
        mismatches += dst[i] != (int64_t)((uint64_t)0xff556677 << 3);
        checksum += (uint64_t)dst[i];
        scalar_checksum += (uint64_t)scalar[i];
        mismatches += fill_dst[i] != fill_scalar[i];
        mismatches += copy_dst[i] != copy_scalar[i];
        mismatches += mixed_dst[i] != mixed_scalar[i];
    }
    qsort(vector_samples, FRAMES, sizeof(uint64_t), cmp);
    qsort(scalar_samples, FRAMES, sizeof(uint64_t), cmp);
    qsort(const_samples, FRAMES, sizeof(uint64_t), cmp);
    qsort(scalar_const_samples, FRAMES, sizeof(uint64_t), cmp);
    qsort(fill_samples, FRAMES, sizeof(uint64_t), cmp);
    qsort(scalar_fill_samples, FRAMES, sizeof(uint64_t), cmp);
    qsort(copy_samples, FRAMES, sizeof(uint64_t), cmp);
    qsort(scalar_copy_samples, FRAMES, sizeof(uint64_t), cmp);
    qsort(mixed_samples, FRAMES, sizeof(uint64_t), cmp);
    qsort(scalar_mixed_samples, FRAMES, sizeof(uint64_t), cmp);
    printf("ENGINE2D_OPAQUE_SPAN_PERF width=%d frames=%d image_p50_ns=%llu image_p95_ns=%llu scalar_image_p50_ns=%llu image_speedup_x1000=%llu const_p50_ns=%llu const_p95_ns=%llu scalar_const_p50_ns=%llu const_speedup_x1000=%llu fill_p50_ns=%llu fill_p95_ns=%llu scalar_fill_p50_ns=%llu fill_speedup_x1000=%llu copy_p50_ns=%llu copy_p95_ns=%llu scalar_copy_p50_ns=%llu copy_speedup_x1000=%llu mixed_p50_ns=%llu mixed_p95_ns=%llu scalar_mixed_p50_ns=%llu mixed_speedup_x1000=%llu simd_hits=%lld mismatches=%llu checksum=%llu scalar_checksum=%llu\n",
        N, FRAMES, (unsigned long long)vector_samples[FRAMES / 2],
        (unsigned long long)vector_samples[FRAMES * 95 / 100],
        (unsigned long long)scalar_samples[FRAMES / 2],
        (unsigned long long)(scalar_samples[FRAMES / 2] * 1000 / vector_samples[FRAMES / 2]),
        (unsigned long long)const_samples[FRAMES / 2],
        (unsigned long long)const_samples[FRAMES * 95 / 100],
        (unsigned long long)scalar_const_samples[FRAMES / 2],
        (unsigned long long)(scalar_const_samples[FRAMES / 2] * 1000 / const_samples[FRAMES / 2]),
        (unsigned long long)fill_samples[FRAMES / 2],
        (unsigned long long)fill_samples[FRAMES * 95 / 100],
        (unsigned long long)scalar_fill_samples[FRAMES / 2],
        (unsigned long long)(scalar_fill_samples[FRAMES / 2] * 1000 / fill_samples[FRAMES / 2]),
        (unsigned long long)copy_samples[FRAMES / 2],
        (unsigned long long)copy_samples[FRAMES * 95 / 100],
        (unsigned long long)scalar_copy_samples[FRAMES / 2],
        (unsigned long long)(scalar_copy_samples[FRAMES / 2] * 1000 / copy_samples[FRAMES / 2]),
        (unsigned long long)mixed_samples[FRAMES / 2],
        (unsigned long long)mixed_samples[FRAMES * 95 / 100],
        (unsigned long long)scalar_mixed_samples[FRAMES / 2],
        (unsigned long long)(scalar_mixed_samples[FRAMES / 2] * 1000 / mixed_samples[FRAMES / 2]),
        (long long)rt_simd_engine2d_neon_hits(),
        (unsigned long long)mismatches, (unsigned long long)checksum,
        (unsigned long long)scalar_checksum);
    free(mixed_scalar); free(mixed_src); free(mixed_dst);
    free(copy_scalar); free(copy_dst); free(fill_scalar); free(fill_dst);
    free(scalar_const); free(scalar); free(src); free(dst);
    return mismatches == 0 && scalar_checksum != 0 && rt_simd_engine2d_neon_hits() > 0 ? 0 : 1;
}
