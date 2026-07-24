#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "runtime.h"

typedef struct {
    uint8_t kind;
    uint8_t flags;
    uint8_t reserved[6];
    int64_t len;
    int64_t cap;
    int64_t *data;
} TestArray;

static TestArray output_array;
static int64_t output_pixels[16];

int64_t rt_array_len(SplArray *array) {
    return ((TestArray *)array)->len;
}

int64_t rt_array_data_ptr(SplArray *array) {
    return (int64_t)(uintptr_t)((TestArray *)array)->data;
}

SplArray *rt_array_new_uninit(int64_t cap) {
    if (cap < 0 || cap > 16) return NULL;
    memset(output_pixels, 0, sizeof(output_pixels));
    output_array = (TestArray){0, 0, {0}, 0, cap, output_pixels};
    return (SplArray *)&output_array;
}

int64_t rt_array_header_ptr(SplArray *array) {
    return (int64_t)(uintptr_t)array;
}

int8_t rt_array_set_len_known(int64_t header_ptr, int64_t len) {
    ((TestArray *)(uintptr_t)header_ptr)->len = len;
    return 1;
}

extern SplArray *rt_engine2d_simd_fill_span_u32(SplArray *, int64_t, int64_t, int64_t);
extern SplArray *rt_engine2d_simd_copy_span_u32(SplArray *, int64_t, SplArray *, int64_t, int64_t);
extern SplArray *rt_engine2d_simd_blend_row_u32(SplArray *, SplArray *);
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

    int64_t blend_dst_pixels[3] = {0, (int64_t)((uint64_t)0x800000ff << 3),
                                   (int64_t)((uint64_t)0x00112233 << 3)};
    int64_t blend_src_pixels[3] = {(int64_t)((uint64_t)0x80ffffff << 3),
                                   (int64_t)((uint64_t)0x80ff0000 << 3), 0};
    TestArray blend_dst = {0, 0, {0}, 3, 3, blend_dst_pixels};
    TestArray blend_src = {0, 0, {0}, 3, 3, blend_src_pixels};
    rt_simd_engine2d_neon_reset();
    result = rt_engine2d_simd_blend_row_u32((SplArray *)&blend_dst,
                                            (SplArray *)&blend_src);
    if (result != (SplArray *)&output_array) return 8;
    if (output_pixels[0] != (int64_t)((uint64_t)0x80ffffff << 3) ||
        output_pixels[1] != (int64_t)((uint64_t)0xbfaa0054 << 3) ||
        output_pixels[2] != (int64_t)((uint64_t)0x00112233 << 3)) return 9;
#if defined(__x86_64__) || defined(_M_X64) || defined(__aarch64__) || defined(_M_ARM64)
    if (rt_simd_engine2d_neon_hits() != 1) return 10;
#else
    if (rt_simd_engine2d_neon_hits() != 0) return 10;
#endif
    puts("ENGINE2D_SIMD_SPAN_TEST: PASS");
    return 0;
}
