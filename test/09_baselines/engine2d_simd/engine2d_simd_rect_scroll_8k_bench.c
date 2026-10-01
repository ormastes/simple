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
int64_t rt_array_header_ptr(SplArray *a) {
    return (int64_t)(uintptr_t)a;
}
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
    uint64_t x = *(const uint64_t *)a;
    uint64_t y = *(const uint64_t *)b;
    return x > y ? 1 : x < y ? -1 : 0;
}

static void native_blit(TestArray *dst, TestArray *src, int width, int height) {
    for (int row = 0; row < height; row++) {
        int64_t offset = (int64_t)row * width;
        rt_engine2d_simd_copy_span_u32(
            (SplArray *)dst, offset, (SplArray *)src, offset, width);
    }
}

static void native_blit_rect(TestArray *dst, TestArray *src, int stride,
                             int x, int y, int width, int height) {
    for (int row = 0; row < height; row++) {
        int64_t offset = (int64_t)(y + row) * stride + x;
        rt_engine2d_simd_copy_span_u32(
            (SplArray *)dst, offset, (SplArray *)src, offset, width);
    }
}

static void scalar_blit_rect(int64_t *dst, const int64_t *src, int stride,
                             int x, int y, int width, int height) {
    for (int row = 0; row < height; row++) {
        int64_t offset = (int64_t)(y + row) * stride + x;
        memcpy(dst + offset, src + offset, (size_t)width * sizeof(int64_t));
    }
}

static void native_scroll_down(TestArray *buf, int width, int height) {
    for (int row = height - 2; row >= 0; row--) {
        int64_t src_offset = (int64_t)row * width;
        int64_t dst_offset = src_offset + width;
        rt_engine2d_simd_copy_span_u32(
            (SplArray *)buf, dst_offset, (SplArray *)buf, src_offset, width);
    }
}

static void scalar_scroll_down(int64_t *buf, int width, int height) {
    for (int row = height - 2; row >= 0; row--) {
        memmove(buf + (int64_t)(row + 1) * width,
                buf + (int64_t)row * width,
                (size_t)width * sizeof(int64_t));
    }
}

static void native_scroll_rect_down(TestArray *buf, int stride, int x, int y,
                                    int width, int height) {
    for (int row = height - 2; row >= 0; row--) {
        int64_t src_offset = (int64_t)(y + row) * stride + x;
        int64_t dst_offset = src_offset + stride;
        rt_engine2d_simd_copy_span_u32(
            (SplArray *)buf, dst_offset, (SplArray *)buf, src_offset, width);
    }
}

static void scalar_scroll_rect_down(int64_t *buf, int stride, int x, int y,
                                    int width, int height) {
    for (int row = height - 2; row >= 0; row--) {
        int64_t src_offset = (int64_t)(y + row) * stride + x;
        int64_t dst_offset = src_offset + stride;
        memmove(buf + dst_offset, buf + src_offset,
                (size_t)width * sizeof(int64_t));
    }
}

static uint64_t checksum(const int64_t *pixels, int64_t count) {
    uint64_t sum = 0;
    for (int64_t i = 0; i < count; i++) sum += (uint64_t)pixels[i];
    return sum;
}

int main(void) {
    enum {
        WIDTH = 7680, HEIGHT = 4320, FRAMES = 20, DAMAGE_FRAMES = 200,
        DAMAGE_X = 320, DAMAGE_Y = 256, DAMAGE_W = 64, DAMAGE_H = 64
    };
    const int64_t count = (int64_t)WIDTH * HEIGHT;
    const size_t bytes = (size_t)count * sizeof(int64_t);
    int64_t *src = malloc(bytes);
    int64_t *native = malloc(bytes);
    int64_t *scalar = malloc(bytes);
    if (!src || !native || !scalar) return 2;
    for (int64_t i = 0; i < count; i++) {
        src[i] = (int64_t)((uint64_t)(0xff000000u |
            ((uint32_t)i * 2654435761u & 0xffffffu)) << 3);
    }
    TestArray source = {0, 0, {0}, count, count, src};
    TestArray destination = {0, 0, {0}, count, count, native};
    uint64_t native_blit_samples[FRAMES], scalar_blit_samples[FRAMES];
    uint64_t native_scroll_samples[FRAMES], scalar_scroll_samples[FRAMES];
    uint64_t damage_blit_samples[DAMAGE_FRAMES];
    uint64_t scalar_damage_blit_samples[DAMAGE_FRAMES];
    uint64_t damage_scroll_samples[DAMAGE_FRAMES];
    uint64_t scalar_damage_scroll_samples[DAMAGE_FRAMES];

    rt_simd_engine2d_neon_reset();
    for (int frame = 0; frame < FRAMES; frame++) {
        uint64_t started = now_ns();
        native_blit(&destination, &source, WIDTH, HEIGHT);
        native_blit_samples[frame] = now_ns() - started;
        started = now_ns();
        memcpy(scalar, src, bytes);
        scalar_blit_samples[frame] = now_ns() - started;
    }
    int blit_equal = memcmp(native, scalar, bytes) == 0;
    uint64_t blit_checksum = checksum(native, count);

    memcpy(native, src, bytes);
    memcpy(scalar, src, bytes);
    for (int frame = 0; frame < FRAMES; frame++) {
        uint64_t started = now_ns();
        native_scroll_down(&destination, WIDTH, HEIGHT);
        native_scroll_samples[frame] = now_ns() - started;
        started = now_ns();
        scalar_scroll_down(scalar, WIDTH, HEIGHT);
        scalar_scroll_samples[frame] = now_ns() - started;
    }
    int scroll_equal = memcmp(native, scalar, bytes) == 0;
    uint64_t scroll_checksum = checksum(native, count);

    memcpy(native, src, bytes);
    memcpy(scalar, src, bytes);
    for (int frame = 0; frame < DAMAGE_FRAMES; frame++) {
        uint64_t started = now_ns();
        native_blit_rect(&destination, &source, WIDTH, DAMAGE_X, DAMAGE_Y,
                         DAMAGE_W, DAMAGE_H);
        damage_blit_samples[frame] = now_ns() - started;
        started = now_ns();
        scalar_blit_rect(scalar, src, WIDTH, DAMAGE_X, DAMAGE_Y,
                         DAMAGE_W, DAMAGE_H);
        scalar_damage_blit_samples[frame] = now_ns() - started;
    }
    int damage_blit_equal = memcmp(native, scalar, bytes) == 0;

    memcpy(native, src, bytes);
    memcpy(scalar, src, bytes);
    for (int frame = 0; frame < DAMAGE_FRAMES; frame++) {
        uint64_t started = now_ns();
        native_scroll_rect_down(&destination, WIDTH, DAMAGE_X, DAMAGE_Y,
                                DAMAGE_W, DAMAGE_H);
        damage_scroll_samples[frame] = now_ns() - started;
        started = now_ns();
        scalar_scroll_rect_down(scalar, WIDTH, DAMAGE_X, DAMAGE_Y,
                                DAMAGE_W, DAMAGE_H);
        scalar_damage_scroll_samples[frame] = now_ns() - started;
    }
    int damage_scroll_equal = memcmp(native, scalar, bytes) == 0;
    uint64_t damage_checksum = checksum(native, count);

    qsort(native_blit_samples, FRAMES, sizeof(uint64_t), compare_u64);
    qsort(scalar_blit_samples, FRAMES, sizeof(uint64_t), compare_u64);
    qsort(native_scroll_samples, FRAMES, sizeof(uint64_t), compare_u64);
    qsort(scalar_scroll_samples, FRAMES, sizeof(uint64_t), compare_u64);
    qsort(damage_blit_samples, DAMAGE_FRAMES, sizeof(uint64_t), compare_u64);
    qsort(scalar_damage_blit_samples, DAMAGE_FRAMES, sizeof(uint64_t), compare_u64);
    qsort(damage_scroll_samples, DAMAGE_FRAMES, sizeof(uint64_t), compare_u64);
    qsort(scalar_damage_scroll_samples, DAMAGE_FRAMES, sizeof(uint64_t), compare_u64);
    const int p50 = FRAMES / 2;
    const int p95 = FRAMES * 95 / 100;
    const int64_t hits = rt_simd_engine2d_neon_hits();
    printf(
        "ENGINE2D_RECT_SCROLL_8K width=%d height=%d frames=%d "
        "blit_p50_ns=%llu blit_p95_ns=%llu scalar_blit_p50_ns=%llu "
        "scroll_p50_ns=%llu scroll_p95_ns=%llu scalar_scroll_p50_ns=%llu "
        "damage_rect=64x64 damage_frames=%d "
        "damage_blit_p50_ns=%llu damage_blit_p95_ns=%llu scalar_damage_blit_p50_ns=%llu "
        "damage_scroll_p50_ns=%llu damage_scroll_p95_ns=%llu scalar_damage_scroll_p50_ns=%llu "
        "native_hits=%lld blit_equal=%d scroll_equal=%d "
        "damage_blit_equal=%d damage_scroll_equal=%d "
        "blit_checksum=%llu scroll_checksum=%llu damage_checksum=%llu\n",
        WIDTH, HEIGHT, FRAMES,
        (unsigned long long)native_blit_samples[p50],
        (unsigned long long)native_blit_samples[p95],
        (unsigned long long)scalar_blit_samples[p50],
        (unsigned long long)native_scroll_samples[p50],
        (unsigned long long)native_scroll_samples[p95],
        (unsigned long long)scalar_scroll_samples[p50],
        DAMAGE_FRAMES,
        (unsigned long long)damage_blit_samples[DAMAGE_FRAMES / 2],
        (unsigned long long)damage_blit_samples[DAMAGE_FRAMES * 95 / 100],
        (unsigned long long)scalar_damage_blit_samples[DAMAGE_FRAMES / 2],
        (unsigned long long)damage_scroll_samples[DAMAGE_FRAMES / 2],
        (unsigned long long)damage_scroll_samples[DAMAGE_FRAMES * 95 / 100],
        (unsigned long long)scalar_damage_scroll_samples[DAMAGE_FRAMES / 2],
        (long long)hits, blit_equal, scroll_equal,
        damage_blit_equal, damage_scroll_equal,
        (unsigned long long)blit_checksum,
        (unsigned long long)scroll_checksum,
        (unsigned long long)damage_checksum);
    free(scalar); free(native); free(src);
    return blit_equal && scroll_equal && damage_blit_equal &&
        damage_scroll_equal && hits > 0 ? 0 : 1;
}
