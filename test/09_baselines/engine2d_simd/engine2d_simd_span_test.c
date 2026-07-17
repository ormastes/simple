#include <stdint.h>
#include <stdio.h>

#include "runtime.h"

typedef struct {
    uint8_t kind;
    uint8_t flags;
    uint8_t reserved[6];
    int64_t len;
    int64_t cap;
    int64_t *data;
} TestArray;

int64_t rt_array_len(SplArray *array) {
    return ((TestArray *)array)->len;
}

int64_t rt_array_data_ptr(SplArray *array) {
    return (int64_t)(uintptr_t)((TestArray *)array)->data;
}

extern SplArray *rt_engine2d_simd_fill_span_u32(SplArray *, int64_t, int64_t, int64_t);
extern SplArray *rt_engine2d_simd_copy_span_u32(SplArray *, int64_t, SplArray *, int64_t, int64_t);
extern int64_t rt_simd_engine2d_neon_hits(void);
extern int64_t rt_simd_engine2d_neon_reset(void);

int main(void) {
    int64_t pixels[16] = {0};
    TestArray array = {0, 0, {0}, 16, 16, pixels};
    const int64_t tagged_color = (int64_t)((uint64_t)0xff102030 << 3);
    rt_simd_engine2d_neon_reset();
    SplArray *result = rt_engine2d_simd_fill_span_u32((SplArray *)&array, 8, 8, 0xff102030);
    if (result != (SplArray *)&array) return 1;
    if (pixels[7] != 0 || pixels[8] != tagged_color || pixels[15] != tagged_color) return 2;

    int64_t src_pixels[8] = {10, 11, 12, 13, 14, 15, 16, 17};
    int64_t dst_pixels[8] = {0};
    TestArray src = {0, 0, {0}, 8, 8, src_pixels};
    TestArray dst = {0, 0, {0}, 8, 8, dst_pixels};
    result = rt_engine2d_simd_copy_span_u32(
        (SplArray *)&dst, 2, (SplArray *)&src, 3, 4);
    if (result != (SplArray *)&dst) return 3;
    if (dst_pixels[1] != 0 || dst_pixels[2] != 13 || dst_pixels[5] != 16 || dst_pixels[6] != 0) return 4;
    result = rt_engine2d_simd_copy_span_u32(
        (SplArray *)&dst, 6, (SplArray *)&src, 6, 8);
    if (dst_pixels[6] != 16 || dst_pixels[7] != 17) return 5;
    result = rt_engine2d_simd_copy_span_u32(
        (SplArray *)&dst, -1, (SplArray *)&src, 0, 2);
    if (dst_pixels[0] != 0) return 6;
    result = rt_engine2d_simd_copy_span_u32(
        (SplArray *)&src, 2, (SplArray *)&src, 0, 6);
    if (src_pixels[2] != 10 || src_pixels[7] != 15) return 7;
#if defined(__x86_64__) || defined(_M_X64) || defined(__aarch64__) || defined(_M_ARM64) || \
    (defined(__riscv) && defined(__riscv_vector))
    if (rt_simd_engine2d_neon_hits() <= 0) return 8;
#else
    if (rt_simd_engine2d_neon_hits() != 0) return 8;
#endif
    puts("ENGINE2D_SIMD_SPAN_TEST: PASS");
    return 0;
}
