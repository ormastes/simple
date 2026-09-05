#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "runtime.h"

typedef struct {
    uint8_t kind, flags, reserved[6];
    int64_t len, cap;
    int64_t *data;
} TestArray;

int64_t rt_array_len(SplArray *a) { return ((TestArray *)a)->len; }
int64_t rt_array_data_ptr(SplArray *a) {
    return (int64_t)(uintptr_t)((TestArray *)a)->data;
}
SplArray *rt_array_new_uninit(int64_t n) { (void)n; return NULL; }
int64_t rt_array_header_ptr(SplArray *a) { return (int64_t)(uintptr_t)a; }
int8_t rt_array_set_len_known(int64_t p, int64_t n) {
    (void)p; (void)n; return 0;
}

extern SplArray *rt_engine2d_simd_copy_span_u32(
    SplArray *, int64_t, SplArray *, int64_t, int64_t);
extern int64_t rt_simd_engine2d_neon_hits(void);
extern int64_t rt_simd_engine2d_neon_reset(void);

static uint64_t now_ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * 1000000000ull + (uint64_t)t.tv_nsec;
}

static int compare_u64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return x > y ? 1 : x < y ? -1 : 0;
}

static void native_rect(TestArray *dst, TestArray *src, int stride,
                        int x, int y, int width, int height) {
    for (int row = 0; row < height; row++) {
        int64_t offset = (int64_t)(y + row) * stride + x;
        rt_engine2d_simd_copy_span_u32(
            (SplArray *)dst, offset, (SplArray *)src, offset, width);
    }
}

static void scalar_rect(int64_t *dst, const int64_t *src, int stride,
                        int x, int y, int width, int height) {
    for (int row = 0; row < height; row++) {
        int64_t offset = (int64_t)(y + row) * stride + x;
        memcpy(dst + offset, src + offset, (size_t)width * sizeof(int64_t));
    }
}

static void native_scroll(TestArray *buf, int stride, int x, int y,
                          int width, int height) {
    for (int row = height - 2; row >= 0; row--) {
        int64_t src = (int64_t)(y + row) * stride + x;
        rt_engine2d_simd_copy_span_u32(
            (SplArray *)buf, src + stride, (SplArray *)buf, src, width);
    }
}

static void scalar_scroll(int64_t *buf, int stride, int x, int y,
                          int width, int height) {
    for (int row = height - 2; row >= 0; row--) {
        int64_t src = (int64_t)(y + row) * stride + x;
        memmove(buf + src + stride, buf + src, (size_t)width * sizeof(int64_t));
    }
}

static uint64_t checksum(const int64_t *pixels, int64_t count) {
    uint64_t sum = 0;
    for (int64_t i = 0; i < count; i++) sum += (uint64_t)pixels[i];
    return sum;
}

int main(void) {
    enum { W = 7680, H = 4320, X = 320, Y = 256, RW = 64, RH = 64, N = 200 };
    const int64_t count = (int64_t)W * H;
    const size_t bytes = (size_t)count * sizeof(int64_t);
    int64_t *src = malloc(bytes), *native = calloc((size_t)count, sizeof(int64_t));
    int64_t *scalar = calloc((size_t)count, sizeof(int64_t));
    if (!src || !native || !scalar) return 2;
    for (int64_t i = 0; i < count; i++)
        src[i] = (int64_t)((uint64_t)(0xff000000u |
            ((uint32_t)i * 2654435761u & 0xffffffu)) << 3);
    TestArray source = {0, 0, {0}, count, count, src};
    TestArray destination = {0, 0, {0}, count, count, native};
    uint64_t blit[N], scalar_blit[N], scroll[N], scalar_scrolls[N];
    rt_simd_engine2d_neon_reset();
    for (int frame = 0; frame < N; frame++) {
        uint64_t start = now_ns();
        native_rect(&destination, &source, W, X, Y, RW, RH);
        blit[frame] = now_ns() - start;
        start = now_ns();
        scalar_rect(scalar, src, W, X, Y, RW, RH);
        scalar_blit[frame] = now_ns() - start;
    }
    int blit_equal = memcmp(native, scalar, bytes) == 0;
    memcpy(native, src, bytes); memcpy(scalar, src, bytes);
    for (int frame = 0; frame < N; frame++) {
        uint64_t start = now_ns();
        native_scroll(&destination, W, X, Y, RW, RH);
        scroll[frame] = now_ns() - start;
        start = now_ns();
        scalar_scroll(scalar, W, X, Y, RW, RH);
        scalar_scrolls[frame] = now_ns() - start;
    }
    int scroll_equal = memcmp(native, scalar, bytes) == 0;
    qsort(blit, N, sizeof(uint64_t), compare_u64);
    qsort(scalar_blit, N, sizeof(uint64_t), compare_u64);
    qsort(scroll, N, sizeof(uint64_t), compare_u64);
    qsort(scalar_scrolls, N, sizeof(uint64_t), compare_u64);
    printf("ENGINE2D_DAMAGE_RECT_8K width=%d height=%d rect=64x64 frames=%d "
           "blit_p50_ns=%llu blit_p95_ns=%llu scalar_blit_p50_ns=%llu "
           "scroll_p50_ns=%llu scroll_p95_ns=%llu scalar_scroll_p50_ns=%llu "
           "native_hits=%lld blit_equal=%d scroll_equal=%d checksum=%llu\n",
           W, H, N, (unsigned long long)blit[N / 2],
           (unsigned long long)blit[N * 95 / 100],
           (unsigned long long)scalar_blit[N / 2],
           (unsigned long long)scroll[N / 2],
           (unsigned long long)scroll[N * 95 / 100],
           (unsigned long long)scalar_scrolls[N / 2],
           (long long)rt_simd_engine2d_neon_hits(), blit_equal, scroll_equal,
           (unsigned long long)checksum(native, count));
    free(scalar); free(native); free(src);
    return blit_equal && scroll_equal ? 0 : 1;
}
